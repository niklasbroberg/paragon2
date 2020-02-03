{-# LANGUAGE DeriveDataTypeable #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  Security.InfoFlow.Policy.FlowLocks.GlobalPolicy
-- Copyright   :  (c) Niklas Broberg 2013
-- License     :  BSD-style (see the file LICENSE.txt)
--
-- Maintainer  :  Niklas Broberg, niklas.broberg@chalmers.se
-- Stability   :  transient
-- Portability :  portable
--
-- This module provides provides a representation of recursive
-- datalog clauses used to implement lock properties. In principle
-- these could be used to represent non-static properties, but
-- the constraint solver in ".Constraint" expects all constraints
-- to use the same set of clauses.
--
-----------------------------------------------------------------------------
module Security.InfoFlow.Policy.FlowLocks.GlobalPolicy where

import Security.InfoFlow.Policy.FlowLocks.Policy

import Data.Generics (Data, Typeable)

type GlobalPolicy name actset = [DatalogClause name actset]

-- | Datalog clauses are (potentially recursive) clauses
--   with atoms as heads. We require that all actor reps
--   used in all atoms are 'QuantActor's, since there is
--   no 'HeadActor' to refer to.
data DatalogClause name actset 
    = DatalogClause [actset] (Predicate name) [Predicate name]
      deriving (Eq, Show, Data, Typeable)


-- | Transform a 'Clause' into a 'DatalogClause' by transforming
--   its head to a flow predicate. We parameterize over the exact
--   predicate, since we don't know what representation 
addFlowPredicate :: Clause name actset -> DatalogClause name actset
addFlowPredicate (Clause headC qualsC bodyC) =
    let quals = headC : qualsC
        headRep = QuantActor 0
        transform (Atom n reps) = AtomPred $ Atom n $ map incSubst reps
        incSubst HeadActor = headRep
        incSubst (QuantActor i) = QuantActor $ i+1
        bodyCoff = map transform bodyC
    in 
      DatalogClause quals (FlowPred headRep) bodyCoff

-- | A 'Predicate' represents either an ordinary atom,
--   or a distinguished predicate.
data Predicate name 
    = FlowPred ActorRep     
    -- ^ Distinguished flow predicate used for modelling policies.
    | AtomPred (Atom name)  -- ^ Ordinary atom (lock) predicate
  deriving (Eq, Show, Data, Typeable)

-- | A 'PredicateName' represents the name of a predicate
data PredicateName actset name
    = FlowPredName
    | ActSetPredName actset
    | LockPredName name
  deriving (Eq, Show, Data, Typeable)
