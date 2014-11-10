{-# LANGUAGE CPP, FlexibleInstances, 
    MultiParamTypeClasses, UndecidableInstances #-}
module Language.Java.Paragon.PolicyLang 
    (
     ActorPolicy, ActorPolicyBounds, TcLock, 
     TypedActorIdSpec, LockSpec
    ) where

import Language.Java.Paragon.SourcePos
import Language.Java.Paragon.Syntax (Name)
import Language.Java.Paragon.Pretty

import Control.Applicative

#ifdef BASE4
import Data.Data
#else
import Data.Generics (Data(..),Typeable(..))
#endif

import {-# SOURCE #-} Language.Java.Paragon.PolicyLang.Actors
import {-# SOURCE #-} Language.Java.Paragon.PolicyLang.Locks (LockSpec)
import {-# SOURCE #-} Language.Java.Paragon.PolicyLang.Policy 

import Security.InfoFlow.Policy.FlowLocks


type ActorPolicy 
    = MetaPolicy 
        MetaVarRep 
        PolicyVarRep 
        (Name SourcePos) 
        ActorSetRep

type PrgPolicy
    = VarPolicy
        PolicyVarRep
        (Name SourcePos)
        ActorSetRep

type TcLock = LockSpec
type TcLockDelta = LockDelta (Name SourcePos) TypedActorIdSpec
type GlobalPol = GlobalPolicy (Name SourcePos) ActorSetRep

data ActorPolicyBounds
instance Eq ActorPolicyBounds
instance Show ActorPolicyBounds
instance Data ActorPolicyBounds
instance Typeable ActorPolicyBounds
instance Pretty ActorPolicyBounds

instance HasSubTyping m =>
    PartialOrder m ActorPolicyBounds

instance HasSubTyping m =>
    JoinSemiLattice m ActorPolicyBounds

instance HasSubTyping m =>
    Lattice m ActorPolicyBounds


