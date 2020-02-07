{-# LANGUAGE CPP, DeriveDataTypeable #-}
module Language.Java.Paragon.PolicyLang.Actors where


import Language.Java.Paragon.Syntax
import Language.Java.Paragon.Pretty

import Language.Java.Paragon.SourcePos
import Language.Java.Paragon.TypeCheck.Types (TcRefType)

import Security.InfoFlow.Policy.FlowLocks.Actor

import Language.Java.Paragon.Monad.Base

import Control.Applicative

import qualified Data.ByteString.Char8 as B

#ifdef BASE4
import Data.Data
#else
import Data.Generics (Data(..),Typeable(..))
#endif

import Prelude hiding ((<>))

-- | The actor identity representation in the Paragon dialect
--   of Paralocks is slightly more complex than basic Paralocks,
--   allowing slightly better precision for instance actors,
--   i.e. non-static actor fields.
data ActorIdentity
    = Fresh Int String
    -- ^ Can be traced back to the actor initialization
    | Instance (Name SourcePos) Int
    -- ^ The non-static fields - the first parameter is
    --   the point-separated address to the actor field
    | Unknown Int
    -- ^ Cannot be traced back to initialization
 deriving (Show, Eq, Ord, Data, Typeable)

-- | In some cases we further allow actors to be specified through
--   an actor type parameter.
data ActorIdSpec
    = ConcreteActorId ActorIdentity
    -- ^ Concrete actor id representation
    | ActorTPVar B.ByteString
    -- ^ Actor represented by a type parameter
    --   (is instatiated upon instance creation)
    | ThisId
    -- ^ Actor representing the current object
 deriving (Show, Eq, Ord, Data, Typeable)

data TypedActorIdSpec
    = TypedActorIdSpec {
        actorType :: TcRefType,
        actorSpec :: ActorIdSpec
      }
      deriving (Show, Eq, Ord, Data, Typeable)

instance ActorId ActorIdentity where
  Fresh a _ `mayEq` Fresh b _ = a == b

  Instance n1 _ `mayEq` Instance n2 _ = n1 == n2

  Unknown _ `mayEq` _ = True
  _ `mayEq` Unknown _ = True

  _ `mayEq` _ = False

instance Pretty ActorIdentity where
  pretty (Fresh k s) = text s <> text ('#':show k)
  pretty (Instance n k) = pretty n <> text ('#':'#':show k)
  pretty (Unknown k) = text ('@':show k)

instance ActorId ActorIdSpec where
  ConcreteActorId aid1 `mayEq` ConcreteActorId aid2
                  = aid1 `mayEq` aid2
  _ `mayEq` _ = True

instance Pretty ActorIdSpec where
  pretty (ConcreteActorId aid) = pretty aid
  pretty (ActorTPVar i) = pretty i
  pretty ThisId = text "this"

instance ActorId TypedActorIdSpec where
  TypedActorIdSpec _ aid1 `mayEq` TypedActorIdSpec _ aid2
                   = aid1 `mayEq` aid2

instance Pretty TypedActorIdSpec where
  pretty (TypedActorIdSpec _ aid) = pretty aid

newUnknown :: MonadBase m => m ActorIdentity
newUnknown = liftBase $ Unknown <$> getFreshInt

newFresh :: MonadBase m => String -> m ActorIdentity
newFresh str = liftBase $ flip Fresh str <$> getFreshInt

newInstance :: MonadBase m => Name SourcePos -> m ActorIdentity
newInstance n = liftBase $ Instance n <$> getFreshInt
