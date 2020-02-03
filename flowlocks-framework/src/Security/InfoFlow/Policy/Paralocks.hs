{-# LANGUAGE MultiParamTypeClasses, DeriveDataTypeable,
             FlexibleInstances, UndecidableInstances #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  Security.InfoFlow.Policy.Paralocks
-- Copyright   :  (c) Niklas Broberg 2013
-- License     :  BSD-style (see the file LICENSE.txt)
--
-- Maintainer  :  Niklas Broberg, niklas.broberg@chalmers.se
-- Stability   :  transient
-- Portability :  portable
--
-- This module provides a concrete instantiation of the 
-- Flow Locks Framework, in the form of the Paralocks
-- language, as presented in Broberg & Sands, 
-- "Paralocks - Role-Based Information Flow Control and Beyond",
-- POPL'10.
--
-----------------------------------------------------------------------------
module Security.InfoFlow.Policy.Paralocks where

import Security.InfoFlow.Policy.FlowLocks

import Data.Generics (Data, Typeable)

import Control.Applicative

import qualified Control.Monad.Fail as Fail

-- $story
--   In order to provide a complete language,
--   Paralocks needs to provide concrete 
--   representations for:
--   * Actors, here being a concrete data type
--   * Actor sets, here being either singleton 
--     actors or the set of all actors.

{----------------------------------------}
{-    Actor identity representation     -}
{----------------------------------------}

-- | 'ActorIdentity' are approximations of actual
--   identities of actors, to the best of our
--   knowledge.
data ActorIdentity
    = Fresh Int   
    -- ^ We know the identity.
    | Unknown Int [Int]
    -- ^ We don't know the identity, but know it
    --   to be one of the listed ones.
  deriving (Show, Data, Typeable)

instance Eq ActorIdentity where
  Fresh i == Fresh j = i == j
  Unknown i _ == Unknown j _ = i == j
  _ == _ = False

instance ActorId ActorIdentity where
  Unknown i is `mayEq` Unknown j js =
      or [ x == y | x <- (i:is), y <- (j:js) ]

  Unknown _ is `mayEq` Fresh j = j `elem` is
  Fresh i `mayEq` Unknown _ js = i `elem` js
  Fresh i `mayEq` Fresh j      = i == j


{----------------------------------------}
{-       Actor set representation       -}
{----------------------------------------}

-- | In Paralocks, an actor representation
--   can either mention a concrete actor,
--   or be a quantified variable representing
--   any actor. We also include a distinguished
--   'top' element, which is one of the
--   requirements (must form a join semi-lattice).
data ActorSetRep aid
    = SingletonActor aid
    | AnyActor
    | NoActor
  deriving (Eq, Show, Data, Typeable)

instance (Functor m, Monad m, Applicative m, ActorId aid) => 
          PartialOrder m (ActorSetRep aid) where
    AnyActor `leq` _ = return True
    SingletonActor aid1 `leq` SingletonActor aid2 = return $
        aid1 == aid2
    _ `leq` NoActor = return True
    _ `leq` _ = return False

instance (Functor m, Monad m, Applicative m, ActorId aid) => 
          JoinSemiLattice m (ActorSetRep aid) where
    topM = return NoActor

    NoActor `lub` _ = return NoActor
    _ `lub` NoActor = return NoActor

    AnyActor `lub` a = return a
    a `lub` AnyActor = return a

    SingletonActor aid1 `lub` SingletonActor aid2
                       | aid1 == aid2 = return $ SingletonActor aid1
                       | otherwise    = return NoActor

instance (Functor m, Monad m, Applicative m, ActorId aid) => 
          Lattice m (ActorSetRep aid) where
    bottomM = return AnyActor

    NoActor `glb` a = return a
    a `glb` NoActor = return a

    AnyActor `glb` _a = return AnyActor
    _a `glb` AnyActor = return AnyActor

    SingletonActor aid1 `glb` SingletonActor aid2
                       | aid1 == aid2 = return $ SingletonActor aid1
                       | otherwise    = return AnyActor


instance (Fail.MonadFail m, Functor m, Monad m, Applicative m, ActorId aid) => 
          ActorSet m (ActorSetRep aid) aid where

  inSet aid1 (SingletonActor aid2) = return $ aid1 == aid2
  inSet _aid AnyActor = return True
  inSet _aid NoActor  = return False

  enumSetMembers (SingletonActor aid) = return $ Just [aid]
  enumSetMembers AnyActor = return Nothing
  enumSetMembers NoActor  = return $ Just []

-- This gives us, for free, the following instances:
--
--   instance (Ord name, Functor m, Monad m) => 
--      Containment m (XPolicy name ActorSetRep) 
--                  name ActorSetRep ActorId
--
-- where XPolicy \in { Policy, VarPolicy, MetaPolicy }
