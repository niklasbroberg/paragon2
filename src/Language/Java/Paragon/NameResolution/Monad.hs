{-# LANGUAGE MultiParamTypeClasses, FlexibleInstances #-}
-- | This module defines the monad used in the name resolution stage of the
-- compilation process.
-- It is defined on top of the PiReader monad and adds
module Language.Java.Paragon.NameResolution.Monad
    (

     module Language.Java.Paragon.Monad.PiReader,

     NameRes, Expansion, runNameRes,

     getCurrentName,

     getExpansion, withExpansion, extendExpansion,

     mkPExpansion, mkTExpansion, mkEExpansion, mkMExpansion, mkLExpansion,

     mkPExpansionWithPrefix, mkTExpansionWithPrefix, mkEExpansionWithPrefix, mkMExpansionWithPrefix, mkLExpansionWithPrefix,

     expansionUnion, unionsWithKey

    ) where

import Language.Java.Paragon.Syntax
import Language.Java.Paragon.Monad.PiReader
import Language.Java.Paragon.SourcePos

import Control.Monad
import qualified Data.Map as Map
import qualified Data.ByteString.Char8 as B

-- | This monad layer adds access to the fully qualified name of the entity
-- that is currently being resolved and access to an expansion map that
-- contains the list of resolved names in scope
newtype NameRes a = NameRes { runNameRes :: Name SourcePos -> Expansion -> PiReader a }

instance Monad NameRes where
  return = liftPR . return
  NameRes f >>= k = NameRes $ \n e -> do
                         a <- f n e
                         let NameRes g = k a
                          in g n e

  fail = liftPR . fail

instance MonadPR NameRes where
  liftPR pr = NameRes $ \_ _ -> pr

instance MonadBase NameRes where
  liftBase = liftPR . liftBase
  withErrCtxt' prf (NameRes f) = NameRes $ (withErrCtxt' prf .) . f
  tryM (NameRes f) = NameRes $ (tryM .) . f
  failE = liftBase . failE
  failEC x = liftBase . failEC x

instance MonadIO NameRes where
  liftIO = liftPR . liftIO

instance Functor NameRes where
  fmap = liftM

instance Applicative NameRes where
  pure = return
  (<*>) = ap

-- | Access expansion map
getExpansion :: NameRes Expansion
getExpansion = NameRes $ const return

-- | Access name of currently handled syntactical unit
getCurrentName :: NameRes (Name SourcePos)
getCurrentName = NameRes $ \n _ -> return n

-- | Set expansion map for given NameRes computation
withExpansion :: Expansion -> NameRes a -> NameRes a
withExpansion e (NameRes f) = NameRes $ \n _ -> f n e

-- | Extend expansion map of given computation by given expansion map
extendExpansion :: Expansion -> NameRes a -> NameRes a
extendExpansion e1 nra = do
  e2 <- getExpansion
  withExpansion (Map.union e1 e2) nra

------------------------------------------
-- Building expansion maps

type Map = Map.Map

type Expansion =
    Map (B.ByteString,                   NameType)   -- NameType may be (partially) unresolved
        (Either String (Maybe (Name SourcePos), NameType))  -- NameType is now fully resolved
-- Note that the source pos does not play any role in the expansion but is only there for type correctness

-- |Expand package / type / expression / method / lock
mkPExpansion, mkTExpansion, mkEExpansion, mkMExpansion, mkLExpansion ::
    B.ByteString -> Expansion

mkPExpansion = mkPExpansionWithPrefix Nothing

mkTExpansion = mkTExpansionWithPrefix Nothing

mkEExpansion = mkEExpansionWithPrefix Nothing

mkMExpansion = mkMExpansionWithPrefix Nothing

mkLExpansion = mkLExpansionWithPrefix Nothing

{-setData :: Name () -> NameSourcePos
dropData (Name _ nt mn id) = Name () nt (fmap dropData mn) (dropDataId id)
dropData (AntiQName _ s) = AntiQName () s

dropData :: Name SourcePos -> Name ()
dropData (Name _ nt mn id) = Name () nt (fmap dropData mn) (dropDataId id)
dropData (AntiQName _ s) = AntiQName () s

dropDataId (Ident _ s) = Ident () s
dropDataId (AntiQIdent _ s) = AntiQIdent () s-}

mkPExpansionWithPrefix, mkTExpansionWithPrefix, mkEExpansionWithPrefix, mkMExpansionWithPrefix, mkLExpansionWithPrefix ::
    Maybe (Name SourcePos) -> B.ByteString -> Expansion

mkPExpansionWithPrefix n i = --n' i = let n = fmap dropData n' in
  Map.fromList [((i, PName   ), return (n, PName)),
                ((i, POrTName), return (n, PName)),
                ((i, AmbName ), return (n, PName))]

-- |Construct an expansion that classifies the given identifier as TName
-- in a lookup of TName or more general NameTypes
mkTExpansionWithPrefix n i = --n' i = let n = fmap dropData n' in
  Map.fromList [((i, TName   ), return (n, TName)),
                ((i, POrTName), return (n, TName)),
                ((i, AmbName ), return (n, TName))]

mkEExpansionWithPrefix n i = -- n' i = let n = fmap dropData n' in
  Map.fromList [((i, EName   ), return (n, EName)),
                ((i, EOrLName), return (n, EName)),
                ((i, AmbName ), return (n, EName))]

mkMExpansionWithPrefix n i = --n' i = let n = fmap dropData n' in
  Map.fromList [((i, MName   ), return (n, MName)),
                ((i, MOrLName), return (n, MName)),
                ((i, AmbName ), return (n, MName))]

mkLExpansionWithPrefix n i = --n' i = let n = fmap dropData n' in
  Map.fromList [((i, LName   ), return (n, LName)),
                ((i, MOrLName), return (n, LName)),
                ((i, EOrLName), return (n, LName)),
                ((i, AmbName ), return (n, LName))]

-- |Convert list of expansions to a single expansion by taking the union
expansionUnion :: [Expansion] -> Expansion
expansionUnion = foldr Map.union Map.empty


unionsWithKey :: Ord k => (k -> a -> a -> a) -> [Map k a] -> Map k a
unionsWithKey f = foldl (Map.unionWithKey f) Map.empty
