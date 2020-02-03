{-# LANGUAGE MultiParamTypeClasses, FunctionalDependencies,
             FlexibleInstances, PatternGuards, FlexibleContexts #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  Security.InfoFlow.Policy.FlowLocks.Containment
-- Copyright   :  (c) Niklas Broberg 2013
-- License     :  BSD-style (see the file LICENSE.txt)
--
-- Maintainer  :  Niklas Broberg, niklas.broberg@chalmers.se
-- Stability   :  transient
-- Portability :  portable
--
-- This module provides containment checks for policies in the
-- presence of a global policy and a lockstate.
--
-----------------------------------------------------------------------------
module Security.InfoFlow.Policy.FlowLocks.ActorSet
    (
      ActorSet(..)
    ) where

import Security.InfoFlow.Policy.FlowLocks.Lattice
import Security.InfoFlow.Policy.FlowLocks.Actor

import qualified Control.Monad.Fail as Fail

class (Fail.MonadFail m, Lattice m actset, ActorId aid, Show aid, Show actset) =>
    ActorSet m actset aid | actset -> aid where

  inSet :: aid -> actset -> m Bool

  enumSetMembers :: actset -> m (Maybe [aid])


