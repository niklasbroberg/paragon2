{-# LANGUAGE CPP, DeriveDataTypeable, FlexibleInstances #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}
module Language.Java.Paragon.PolicyLang.Locks where

--import Data.List (intersect, union, (\\) )

import Language.Java.Paragon.Syntax (Name(..), Ident(..), NameType(LName))
import Language.Java.Paragon.Pretty
--import Language.Java.Paragon.Interaction
import Language.Java.Paragon.SourcePos

import Language.Java.Paragon.PolicyLang.Actors

import Security.InfoFlow.Policy.FlowLocks.Lock

import qualified Data.ByteString.Char8 as B

#ifdef BASE4
import Data.Data
#else
import Data.Generics (Data(..),Typeable(..))
#endif
{-
type LockMods = ([TcLock], [TcLock])

noMods :: LockMods
noMods = ([],[])

--data TcLockExp = TcLockExp [TcLock] | TcLockVar Ident
--  deriving (Eq, Ord, Show, Data, Typeable)
-}

-- | In some places we allow a lock to be represented
--   via a lock(-state) type parameter
data LockSpec
    = ConcreteLock (Lock (Name SourcePos) TypedActorIdSpec)
    -- ^ A concrete lock representation, parameterised 
    --   over actors that may in turn be represented 
    --   by type parameters
    | LockTypeParam B.ByteString
    -- ^ Lock (set) represented by a type parameter
    --   (is instantiated upon instance creation)
--data TcLock = TcLock (Name SourcePos) [ActorId] | TcLockVar B.ByteString
  deriving (Eq, Ord, Show, Data, Typeable)

skolemizeLock :: LockSpec -> Lock (Name SourcePos) TypedActorIdSpec
skolemizeLock (LockTypeParam bi) =
    Lock (Name defaultPos LName Nothing $ 
               Ident defaultPos bi) []
skolemizeLock (ConcreteLock l) = l

type LockMods = LockDelta (Name SourcePos) TypedActorIdSpec


instance (Pretty name, Pretty aid) => 
    Pretty (Lock name aid) where
  pretty (Lock n aids) = pretty n <> 
    opt (not $ null aids) (parens (hcat (punctuate (char ',') $ map pretty aids)))

instance Pretty LockSpec where
  pretty (ConcreteLock l)  = pretty l
  pretty (LockTypeParam i) = pretty i

instance (Pretty name, Pretty aid) =>
    Pretty (LockSet name aid) where
  pretty (LockSet ls) = 
      brackets (hcat (punctuate (char ',') $ map pretty ls))
  pretty NoSet = brackets empty

--instance Pretty [TcLock] where
--  pretty ls = brackets $ hcat (punctuate (char ',') $ map pretty ls)

{-
(<++>) :: LockMods -> LockMods -> LockMods
(c1,o1) <++> (c2,o2) = (c1 `union` c2, o1 `intersect` o2)

(||>>) :: LockMods -> LockMods -> LockMods
(c1,o1) ||>> (c2,o2) =
            let os = (filter (not . (closedBy c2)) o1) ++ o2
                cs = (filter (not . (openedBy o2)) c1) ++ c2
             in (cs,os)

closedBy, openedBy :: [TcLock] -> TcLock -> Bool
closedBy xs x = any (closes x) xs
  where closes (TcLock n1 aids1) (TcLock n2 aids2) =
            n1 == n2 && aids1 `unify` aids2
        closes _ _ = panic "TypeCheck.Locks.closedBy"
                     "TcLockVar should have been instantiated but isn't"
openedBy xs x = any (opens x) xs
  where opens (TcLock n1 aids1) (TcLock n2 aids2) =
            n1 == n2 && and (zipWith (==) aids1 aids2)
        opens  _ _ = panic "TypeCheck.Locks.openedBy"
                     "TcLockVar should have been instantiated but isn't"


models :: LockMods -> LockMods -> Bool
models (c1,o1) (c2,o2) = null (c2 \\ c1) && null (o1 \\ o2)
-}