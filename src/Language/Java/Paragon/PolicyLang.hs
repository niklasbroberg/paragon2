{-# LANGUAGE CPP, MultiParamTypeClasses, DeriveDataTypeable,
    FlexibleContexts, FlexibleInstances, UndecidableInstances #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  Language.Java.Paragon.PolicyLang
-- Copyright   :  (c) Niklas Broberg 2013
-- License     :  BSD-style (see the file LICENSE.txt)
--
-- Maintainer  :  Niklas Broberg, niklas.broberg@chalmers.se
-- Stability   :  transient
-- Portability :  portable
--
-- This module provides a concrete instantiation of the
-- Flow Locks Framework, in the form of the Paragon dialect
-- of the Paralocks language. The differences from the presentation
-- in Broberg & Sands,
-- "Paralocks - Role-Based Information Flow Control and Beyond",
-- are a) the precision is improved for instance actor fields, and
-- b) the Paragon dialect can represent actor/lock type parameters.
--
-----------------------------------------------------------------------------
module Language.Java.Paragon.PolicyLang
    (
     module Language.Java.Paragon.PolicyLang.Actors,
     module Language.Java.Paragon.PolicyLang.Locks,
     module Language.Java.Paragon.PolicyLang.Policy,

--     module Security.InfoFlow.Policy.Paralocks,
     module Security.InfoFlow.Policy.FlowLocks,

     ActorPolicy, ActorPolicyBounds(..), PrgPolicy, BasePolicy,
     TcLockDelta, TcLockSet, TcLock, TcClause, TcActor, TcAtom,
     GlobalPol, LockProp, TcConstraint, ConstraintWMsg,
     thisP, substThis, includesThis, includesThisVP
    ) where

import Language.Java.Paragon.SourcePos
import Language.Java.Paragon.Error (Error)
import Language.Java.Paragon.Syntax (Name)
import Language.Java.Paragon.Pretty

import Language.Java.Paragon.TypeCheck.Types

import Language.Java.Paragon.PolicyLang.Actors
import Language.Java.Paragon.PolicyLang.Locks
import Language.Java.Paragon.PolicyLang.Policy

import Security.InfoFlow.Policy.FlowLocks

import Control.Applicative
import qualified Data.ByteString.Char8 as B

#ifdef BASE4
import Data.Data
#else
import Data.Generics (Data(..),Typeable(..))
#endif

import Prelude hiding ((<>))

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

type BasePolicy = Policy (Name SourcePos) ActorSetRep

thisP :: PrgPolicy
thisP = PolicyVar ThisVar

includesThis :: ActorPolicy -> Bool
includesThis mpol =
    case mpol of
      VarPolicy vp -> includesThisVP vp
      MetaJoin p1 p2 -> any includesThis [p1,p2]
      MetaMeet p1 p2 -> any includesThis [p1,p2]
      _ -> False

includesThisVP :: PrgPolicy -> Bool
includesThisVP vpol =
    case vpol of
      PolicyVar ThisVar -> True
      Join p1 p2 -> any includesThisVP [p1,p2]
      Meet p1 p2 -> any includesThisVP [p1,p2]
      _ -> False


substThis :: BasePolicy
          -> PrgPolicy
          -> PrgPolicy
substThis x = substVarPolicy ThisVar x

type TcLock = LockSpec -- Lock (Name SourcePos) ActorIdSpec
type TcLockSet = LockSet (Name SourcePos) TypedActorIdSpec
type TcLockDelta = LockDelta (Name SourcePos) TypedActorIdSpec

type TcClause = Clause (Name SourcePos) ActorSetRep

type LockProp = DatalogClause (Name SourcePos) ActorSetRep

type TcActor = ActorSetRep

type TcAtom = Atom (Name SourcePos)

type GlobalPol = GlobalPolicy (Name SourcePos) ActorSetRep

type TcConstraint =
    Constraint MetaVarRep PolicyVarRep (Name SourcePos) ActorSetRep TypedActorIdSpec

type ConstraintWMsg = (TcConstraint, Error)

data ActorPolicyBounds
    = KnownPolicy ActorPolicy
    -- | Invariant: For 'PolicyBounds p q', p <= q
    | PolicyBounds ActorPolicy ActorPolicy
  deriving (Eq, Show, Data, Typeable)

instance HasSubTyping m =>
    PartialOrder m ActorPolicyBounds where
  leq (KnownPolicy p1) (KnownPolicy p2) = leq p1 p2
  leq (KnownPolicy p1) (PolicyBounds lb _ub) = leq p1 lb
  leq (PolicyBounds _lb ub) (KnownPolicy p2) = leq ub p2
  leq (PolicyBounds _lb1 ub1) (PolicyBounds lb2 _ub2) = leq ub1 lb2

instance HasSubTyping m =>
    JoinSemiLattice m ActorPolicyBounds where
  KnownPolicy p1 `lub` KnownPolicy p2 = KnownPolicy <$> p1 `lub` p2
  KnownPolicy p1 `lub` PolicyBounds lb ub =
      PolicyBounds <$> p1 `lub` lb <*> p1 `lub` ub
  PolicyBounds lb ub `lub` KnownPolicy p1 =
      PolicyBounds <$> lb `lub` p1 <*> ub `lub` p1
  PolicyBounds lb1 ub1 `lub` PolicyBounds lb2 ub2 =
      PolicyBounds <$> lb1 `lub` lb2 <*> ub1 `lub` ub2

  topM = return $ KnownPolicy $ VarPolicy $ ConcretePolicy $ Policy []

instance HasSubTyping m =>
    Lattice m ActorPolicyBounds where
  KnownPolicy p1 `glb` KnownPolicy p2 = KnownPolicy <$> p1 `glb` p2
  KnownPolicy p1 `glb` PolicyBounds lb ub =
      PolicyBounds <$> p1 `glb` lb <*> p1 `glb` ub
  PolicyBounds lb ub `glb` KnownPolicy p1 =
      PolicyBounds <$> lb `glb` p1 <*> ub `glb` p1
  PolicyBounds lb1 ub1 `glb` PolicyBounds lb2 ub2 =
      PolicyBounds <$> lb1 `glb` lb2 <*> ub1 `glb` ub2

  bottomM = return $ KnownPolicy $ VarPolicy $ ConcretePolicy $
                     Policy [Clause (TypedActor (TcClsRefT objectT) $ B.pack "x") [] []]


instance Pretty ActorPolicyBounds where
  pretty (KnownPolicy p) = pretty p
  pretty (PolicyBounds p q) = pretty p <> char '/' <> pretty q

