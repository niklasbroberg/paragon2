-----------------------------------------------------------------------------
-- |
-- Module      :  Security.InfoFlow.Policy.FlowLocks.Actor
-- Copyright   :  (c) Niklas Broberg 2013
-- License     :  BSD-style (see the file LICENSE.txt)
--
-- Maintainer  :  Niklas Broberg, niklas.broberg@chalmers.se
-- Stability   :  transient
-- Portability :  portable
--
-- This module provides an abstract interface to actor identities,
-- which should be instantiated in a given actor analysis.
--
-----------------------------------------------------------------------------
module Security.InfoFlow.Policy.FlowLocks.Actor
    (
     ActorId(..), (=~=), allMayEq, allMustEq
    ) where


-- | We require that an abstract actor identity supports
--   the "must equal" and "may equal" tests. We rely on
--   the standard 'Eq' class for the first.
class (Eq aid, Show aid) => ActorId aid where
  mayEq :: aid -> aid -> Bool

-- | Synonym for 'mayEq'
(=~=) :: ActorId aid => aid -> aid -> Bool
(=~=) = mayEq

-- | Tests whether all actor identities in
--   two vectors may be equal. The vectors must be
--   of the same length.
allMayEq :: ActorId aid => [aid] -> [aid] -> Bool
allMayEq [] [] = True
allMayEq (x:xs) (y:ys) = x =~= y && xs `allMayEq` ys
allMayEq _ _ = False

-- | Tests whether all actor identities in
--   two vectors may be equal. The vectors must be
--   of the same length.
allMustEq :: ActorId aid => [aid] -> [aid] -> Bool
allMustEq xs ys = length xs == length ys && and (zipWith (==) xs ys)