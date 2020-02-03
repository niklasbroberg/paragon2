{-# LANGUAGE DeriveDataTypeable #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  Security.InfoFlow.Policy.FlowLocks.Lock
-- Copyright   :  (c) Niklas Broberg 2013
-- License     :  BSD-style (see the file LICENSE.txt)
--
-- Maintainer  :  Niklas Broberg, niklas.broberg@chalmers.se
-- Stability   :  transient
-- Portability :  portable
--
-- This module defines the notion of a flow lock, and
-- relevant operations.
--
-----------------------------------------------------------------------------
module Security.InfoFlow.Policy.FlowLocks.Lock
    (
     -- * Locks, sets and modifiers
     Lock(..), LockSet(..), emptyLockSet, LockDelta(..), 
     noDelta, open, close, openAll, closeAll,

     -- * Composition of sets and modifiers
     (<||>), (||>>), (<++>), (++>>), 

     -- * Modifier comparison
     models

    ) where

import Security.InfoFlow.Policy.FlowLocks.Actor

import Data.Generics (Data, Typeable)
import Data.List (union, intersect, (\\))


-- | In the theory of Flow Locks, a 'Lock' is a concrete
--   member of a "lock family", identified by its name,
--   with specific actor arguments, represented by abstract
--   identities.
--   
--   We require that the @name@ parameter be an instance
--   of class 'Eq', and that the @aid@ parameter be an
--   instance of class 'ActorId'.
data Lock name aid = Lock name [aid]
  deriving (Eq, Ord, Show, Data, Typeable)


-- | A 'LockSet' is simply a set of locks, typically
--   modelling the set of locks being open at a particular
--   time (i.e. a "lock state").
data LockSet name aid = LockSet [Lock name aid] | NoSet
  deriving (Eq, Ord, Show, Data, Typeable)

emptyLockSet :: LockSet name aid
emptyLockSet = LockSet []

-- | 'LockDelta's represent modifications, deltas, to a 'LockSet'. 
--   The first parameter represents locks being
--   opened by applying the modification, and the second
--   parameter locks being closed.
data LockDelta name aid 
    = LockDelta [Lock name aid] [Lock name aid]
    | ImpossibleDelta -- ^ Represents an "impossible" modifier
      deriving (Eq, Show, Data, Typeable)

noDelta :: LockDelta name aid
noDelta = LockDelta [] []

open :: Lock name aid -> LockDelta name aid
open l = LockDelta [l] []

openAll :: [Lock name aid] -> LockDelta name aid
openAll = flip LockDelta []

close :: Lock name aid -> LockDelta name aid
close l = LockDelta [] [l]

closeAll :: [Lock name aid] -> LockDelta name aid
closeAll = LockDelta []

-- | Sequential modification of a lock set with a delta.
(||>>) :: (Eq name, ActorId aid) =>
          LockSet name aid -> LockDelta name aid -> LockSet name aid
NoSet ||>> _delta = NoSet
LockSet ls ||>> delta = case LockDelta ls [] ++>> delta of
                          ImpossibleDelta -> NoSet
                          LockDelta os _ -> LockSet os

-- | Parallel composition of lock states.
(<||>) :: (Eq name, ActorId aid) =>
          LockSet name aid -> LockSet name aid -> LockSet name aid
LockSet ls1 <||> LockSet ls2 = LockSet $ ls1 `intersect` ls2
_ <||> _ = NoSet


-- | Parallel composition of lock modifiers.
(<++>) :: (Eq name, ActorId aid) => 
          LockDelta name aid -> LockDelta name aid -> LockDelta name aid
mods1 <++> mods2 = 
    case (mods1, mods2) of
      (LockDelta o1 c1, LockDelta o2 c2) ->
          LockDelta (o1 `intersect` o2) (c1 `union` c2)
      (ImpossibleDelta, _) -> mods2
      (_, ImpossibleDelta) -> mods1

-- | Sequential composition of lock modifiers.
(++>>) :: (Eq name, ActorId aid) => 
          LockDelta name aid -> LockDelta name aid -> LockDelta name aid
LockDelta o1 c1 ++>> LockDelta o2 c2 =
            let os = (filter (not . (closedBy c2)) o1) ++ o2
                cs = (filter (not . (openedBy o2)) c1) ++ c2
             in LockDelta os cs
_ ++>> _ = ImpossibleDelta

-- Internal definitions used in sequential composition of deltas.
closedBy, openedBy :: (Eq name, ActorId aid) =>
                      [Lock name aid] -> Lock name aid -> Bool
closedBy xs x = any (closes x) xs
  where closes (Lock n1 aids1) (Lock n2 aids2) =
            n1 == n2 && aids1 `allMayEq` aids2

openedBy xs x = any (opens x) xs
  where opens (Lock n1 aids1) (Lock n2 aids2) =
            n1 == n2 && aids1 `allMustEq` aids2

-- | Check whether one delta is a conservative
--   approximation of another. If @m1 `models` m2@
--   then @m1@ closes all locks that @m2@ closes,
--   and opens no locks that @m2@ doesn't.
models :: (Eq name, ActorId aid) => 
          LockDelta name aid -> LockDelta name aid -> Bool
models (LockDelta o1 c1) (LockDelta o2 c2) = 
    null (c2 \\ c1) && null (o1 \\ o2)
models _ _ = False