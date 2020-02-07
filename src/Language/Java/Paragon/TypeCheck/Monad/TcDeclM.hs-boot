{-# LANGUAGE MultiParamTypeClasses, FunctionalDependencies, FlexibleInstances, 
             TupleSections, QuasiQuotes, BangPatterns #-}
module Language.Java.Paragon.TypeCheck.Monad.TcDeclM (
  module Language.Java.Paragon.Monad.PiReader,
  TcDeclM, MonadTcDeclM(..), getTypeMap, fetchType, evalSrcRefType, EvalPolicyM(..)


 ) where

import Language.Java.Paragon.Monad.PiReader

import Language.Java.Paragon.Error
import Language.Java.Paragon.Syntax (Ident, Name, TypeParam, Exp, Actor, Lock, RefType)
import Language.Java.Paragon.Pretty()
import Language.Java.Paragon.Interaction()
import Language.Java.Paragon.NameResolution()
import Language.Java.Paragon.SourcePos

import Language.Java.Paragon.TypeCheck.TypeMap
import Language.Java.Paragon.TypeCheck.Types
import qualified Language.Java.Paragon.PolicyLang as PL
import Language.Java.Paragon.TypeCheck.NullAnalysis()

import Control.Monad ()
import Control.Applicative ()

import qualified Data.Map as Map ()
import qualified Data.ByteString.Char8 as B
import Data.List ()
import Data.Maybe ()

-----------------------------------------------
-- Underlying non-cont'ed monad

newtype TcDeclM a = TcDeclM (TypeMap -> TypeMap -> TcClassType -> PiReader (a, TypeMap) )
{-
instance Monad TcDeclM  where
  return = liftPR . return

  TcDeclM f >>= k = TcDeclM $ \ !ctm !gtm !ty -> do
                       (a, gtm') <- f ctm gtm ty
                       let TcDeclM g = k a
                       g ctm gtm' ty

  fail = liftPR . fail

instance Functor TcDeclM  where
  fmap = liftM

instance Applicative TcDeclM  where
  pure = return
  (<*>) = ap

instance MonadIO TcDeclM  where
  liftIO = liftPR . liftIO

instance MonadBase TcDeclM  where
  liftBase = liftPR . liftBase
  withErrCtxt' prf (TcDeclM f) = TcDeclM $ \ctm gtm ty -> withErrCtxt' prf $ f ctm gtm ty
  tryM (TcDeclM f) = TcDeclM $ \ctm gtm ty -> do
                             esatm <- tryM (f ctm gtm ty)
                             case esatm of
                               Right (a, tm) -> return (Right a, tm)
                               Left err -> return (Left err, gtm)
  failE = liftPR . failE

instance MonadPR TcDeclM  where
  liftPR pra = TcDeclM $ \_ gtm _ -> pra >>= \a -> return (a, gtm)
-}
instance MonadPR TcDeclM
instance Monad TcDeclM
instance MonadBase TcDeclM

class MonadPR m => MonadTcDeclM m where
  liftTcDeclM :: TcDeclM a -> m a
  withCurrentTypeMap :: (TypeMap -> Either Error TypeMap) -> m a -> m a

instance MonadTcDeclM TcDeclM 
{-
 where
  liftTcDeclM = id
  withCurrentTypeMap = withCurrentTypeMapTB

extendGlobalTypeMap :: MonadTcDeclM m => (TypeMap -> TypeMap) -> m ()
extendGlobalTypeMap = liftTcDeclM . extendGlobalTypeMapTB
  
-}
fetchType :: Name SourcePos -> TcDeclM ([TypeParam SourcePos],[(RefType SourcePos, B.ByteString)],TypeSig)
getTypeMap :: MonadTcDeclM m => m TypeMap

class (HasSubTyping m, MonadTcDeclM m) => EvalPolicyM m where
  evalPolicy :: Exp SourcePos -> m PL.PrgPolicy
  evalActorId :: Name SourcePos -> m PL.TypedActorIdSpec
  evalActor :: [(Ident SourcePos, TcRefType)] -> Actor SourcePos -> m PL.ActorSetRep
  evalLock :: Lock SourcePos -> m PL.TcLock


evalSrcRefType :: EvalPolicyM m => m PL.ActorPolicy -> RefType SourcePos -> m TcRefType


{-getTypeMap = liftTcDeclM getTypeMapTB

getThisType :: MonadTcDeclM m => m TcClassType
getThisType = liftTcDeclM getThisTypeTB

getThisStateType :: MonadTcDeclM m => m TcStateType
getThisStateType = do
  ct <- getThisType
  (is, tsig) <- lookupTypeOfType $ clsTypeToType ct
  let aids = catMaybes $ map (\i -> Map.lookup i $ actors $ tMembers tsig) is
  return $ instanceT (TcClsRefT ct) aids (NotNull, Committed) --Is it correct ?

getSuperType :: MonadTcDeclM m => m TcClassType
getSuperType = do
  thisTy <- getThisType
  (_, thisSig) <- lookupTypeOfType (clsTypeToType thisTy)
  case tSupers thisSig of
    [] -> return objectT
    [s] -> return s
    _  -> panic (tcDeclMModule ++ ".getSuperType")
          $ "Called on non-class with multiple super types"


withFreshCurrentTypeMap :: TcDeclM a -> TcDeclM a
withFreshCurrentTypeMap = withCurrentTypeMap (const emptyTM)

getLocalTypeMap :: MonadTcDeclM m => m TypeMap
getLocalTypeMap = liftTcDeclM $ 
     TcDeclM $ \ctm gtm _ -> return (ctm, gtm)

getTypeMapTB :: TcDeclM TypeMap
getTypeMapTB = TcDeclM $ \ctm gtm _ -> return $ (ctm `merge` gtm, gtm)

getThisTypeTB :: TcDeclM TcClassType
getThisTypeTB = TcDeclM $ \_ gtm ty -> return (ty, gtm)

withCurrentTypeMapTB ::  (TypeMap -> TypeMap) -> TcDeclM a -> TcDeclM a
withCurrentTypeMapTB tmf (TcDeclM f) = TcDeclM $ \ctm gtm ty -> f (tmf ctm) gtm ty

extendGlobalTypeMapTB :: (TypeMap -> TypeMap) -> TcDeclM ()
extendGlobalTypeMapTB tmf = TcDeclM $ \_ gtm _ -> return ((), tmf gtm)
-}
