{-# LANGUAGE MultiParamTypeClasses, FlexibleInstances, FlexibleContexts #-}
-- | This mpdule contains the implementation of the BaseM monad, the monad
-- that is at the bottom of our monad stack and adds error-handling and
-- unique number generation on top of IO.
-- The module also contains some general monadic functions / combinators.
module Language.Java.Paragon.Monad.Base
    (
     ErrCtxt, BaseM, runBaseM,
     raiseErrors,

     MonadIO(..), MonadBase(..),
     liftEither, liftEitherMB, tryCatch,

     getFreshInt, getErrCtxt, withErrCtxt,

     check, checkC, checkM, ignore, orElse, orM, anyM,
     maybeM, withFold, withFoldMap

    ) where

import Language.Java.Paragon.Monad.Uniq
import Language.Java.Paragon.Error

import Control.Monad
import Control.Monad.Trans.State (StateT(..), runStateT, modify, get)

import Data.Maybe

type ErrCtxt = Error -> Error

-- | The base monad deals adds error handling and unique number generation to IO
-- The error-handling is somewhat involved because we assume the existence of
-- both /fatal/ and /non-fatal/ errors: Errors are accumulated as state,
-- and the Maybe monad is used to short-circuit computation in case of fatal
-- errors. If a non-fatal error occurs, the compuation continues with a Just
-- value, but the list of errors is extended
newtype BaseM a = BaseM (ErrCtxt -> Uniq -> StateT [Error] IO (Maybe a))

instance Monad BaseM where
  return x = BaseM $ \_ _ -> return . Just $ x

  BaseM f >>= k =
      BaseM $ \ec u ->
          do esa <- f ec u
             case esa of
               Nothing -> return Nothing
               Just a ->
                 let BaseM g = k a
                  in g ec u

  -- Provided for the sake of completeness;
  -- failE and failEC should be used instead
  fail err = BaseM $ \ec _ -> do
               modify (\s -> ec (toUndef err) : s)
               return Nothing

instance Applicative BaseM where
  pure = return
  (<*>) = ap

-- | Running a BaseM computation, which will result in either a
-- non-empty list of errors or the result of successfully running
-- the monadic computation
runBaseM :: BaseM a -> IO (Either [Error] a)
runBaseM (BaseM f) = do
  initU <- initUniq
  (a,s) <- runStateT (f id initU) []
  case s of [] -> return . Right . fromJust $ a -- No error => Just value
            e  -> return . Left $ e

instance Functor BaseM where
  fmap = liftM

-- | Access the unique number generation context of a MonadBase monad
-- It should never be necessary to call this, use getFreshInt to get a new
-- number directly. (This function is therefore not exported.)
getUniqRef :: MonadBase m => m Uniq
getUniqRef = liftBase $ BaseM $ \_ u -> return . Just $ u

-- | Get a fresh, unused number from the unique number generator
getFreshInt :: MonadBase m => m Int
getFreshInt = do
  u <- getUniqRef
  liftIO $ getUniq u

-- | Access the ErrCtxt environment
getErrCtxt :: MonadBase m => m ErrCtxt
getErrCtxt = liftBase $ BaseM $ \ec _ -> return . Just $ ec

-- | Abort computation if any non-fatal errors have been logged via failEC
-- The idea is that non-fatal errors collected with failEC do become fatal
-- in later stages of compilation, so we need a mechanism to fail based on
-- previous errors
raiseErrors :: BaseM ()
raiseErrors = BaseM $ \_ _ ->
  do err <- get
     case err of
       [] -> return $ Just ()
       _e -> return Nothing


class Monad m => MonadIO m where
  liftIO :: IO a -> m a

instance MonadIO IO where
  liftIO = id

instance MonadIO BaseM where
  liftIO ioa = BaseM $ \_ _ -> StateT (\s -> do x <- ioa
                                                return (Just x, s))
                               -- ^Just execute the action without touching
                               -- the (error) state

class MonadIO m => MonadBase m where
  -- | Lift BaseM computations to member of the MonadBase class
  liftBase :: BaseM a -> m a
  -- | Run computation with modified error context
  withErrCtxt' :: ( ErrCtxt -> ErrCtxt) -> m a -> m a
  -- | Try computation, returning the result in case of success or the errors
  tryM :: m a -> m (Either [Error] a)
  -- | Fatal error: abort computation (like fail, but on Error, not String)
  failE :: Error -> m a
  -- | Non-fatal error: continue computation from provided default value
  failEC :: a -> Error -> m a

instance MonadBase BaseM where
  liftBase = id
  withErrCtxt' strff (BaseM f) = BaseM $ \ec u -> f (strff ec) u

  -- Construct Either value based on error state
  -- Note that tryM does not distinguish between fatal and non-fatal errors:
  -- If an error occured, we return that rather than any computation result
  tryM (BaseM f) = BaseM $ \ec u -> do
                           olderr <- get     -- store collected errs so far
                           modify (const []) -- start with empty list of err
                           maybeA <- f ec u  -- run code
                           err <- get        -- get errs specific to this code
                           modify (const olderr) -- restore old collection
                           case err of
                             -- No error => The result of the computation is
                             -- of the form Just a
                             -- What we need is a Just (Right a)
                             [] -> return . fmap Right $ maybeA
                             e  -> return . Just . Left $ e
  -- Fatal error => Log error, but Nothing from here
  failE  err     = BaseM $ \ec _ -> do modify (\s -> ec err : s)
                                       return Nothing
  -- Non-fatal error => Log error, but continue with Just value
  failEC def err = BaseM $ \ec _ -> do modify (\s -> ec err : s)
                                       return . Just $ def

-- | Set the error context for the computation
withErrCtxt :: MonadBase m => ContextInfo -> m a -> m a
withErrCtxt err = withErrCtxt' (. addContextInfo err)

-- | Try first argument. If and only it fails, execute catch computation
-- given as second argument.
tryCatch :: MonadBase m => m a -> ([Error] -> m a) -> m a
tryCatch tr ctch = do esa <- tryM tr
                      case esa of
                        Right a -> return a
                        Left err -> ctch err

-- | Lift Either value into monad by mapping Left to fail and Right to return
liftEitherMB :: MonadBase m => Either Error a -> m a
liftEitherMB eerra = case eerra of
                       Left err -> failE err
                       Right x  -> return x

--------------------------------------------
--                                        --
--      Monad-independent helpers         --
--                                        --
--------------------------------------------

-- | Lift Either value into monad by mapping Left to fail and Right to return
liftEither :: Monad m => Either String a -> m a
liftEither esa = case esa of
                   Left err -> fail err
                   Right x  -> return x


check :: MonadBase m => Bool -> Error -> m ()
-- check b err = if b then return () else failE err
check = checkC

-- | Fail (but allow continuation?) if predicate does not hold
checkC :: MonadBase m => Bool -> Error -> m ()
checkC b err = if b then return () else failEC () err

-- | Fail (but allow continuation?) if monadic computation evaluates to False
checkM :: MonadBase m => m Bool -> Error -> m ()
checkM mb err = mb >>= flip check err

-- | Explicitly ignore the result of the computation
ignore :: Monad m => m a -> m ()
ignore = (>> return ())

-- | Get out of the Maybe monad by providing functionality for the Just- and
-- default functionality for the Nothing case
orElse :: Monad m => m (Maybe a) -> m a -> m a
orElse monma mona = do
  ma <- monma
  case ma of
    Just a -> return a
    Nothing -> mona

infixr 3 `orElse`

-- | Monadic non-strict disjunction
orM :: Monad m => m Bool -> m Bool -> m Bool
orM mba mbb = do
  ba <- mba
  if ba then return True else mbb

-- | Monadic non-strict any (list disjunction)
anyM :: Monad m => [m Bool] -> m Bool
anyM ms = foldr orM (return False) ms

-- | Run given computation if given value is Just something.
-- Otherwise just return
maybeM :: Monad m => Maybe a -> (a -> m ()) -> m ()
maybeM ma f = maybe (return ()) f ma

-- | Compose given list of monadic functions
withFold :: Monad m => [m a -> m a] -> m a -> m a
withFold = foldr (.) id

-- | Turn list into sequence of monadic computations that is then composed
withFoldMap :: Monad m => (a -> m b -> m b) -> [a] -> m b -> m b
withFoldMap f = withFold . map f
