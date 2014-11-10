{-# LANGUAGE CPP #-}
module Language.Java.Paragon.PolicyLang.Actors where

import Security.InfoFlow.Policy.FlowLocks.Actor
import Language.Java.Paragon.Pretty

#ifdef BASE4
import Data.Data
#else
import Data.Generics (Data(..),Typeable(..))
#endif

data TypedActorIdSpec

instance Eq TypedActorIdSpec
instance Ord TypedActorIdSpec
instance Show TypedActorIdSpec
instance Data TypedActorIdSpec
instance Typeable TypedActorIdSpec

instance ActorId TypedActorIdSpec 
instance Pretty TypedActorIdSpec 
