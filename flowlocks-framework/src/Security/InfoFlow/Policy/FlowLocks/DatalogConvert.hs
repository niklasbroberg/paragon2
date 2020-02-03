{-# LANGUAGE MultiParamTypeClasses, FunctionalDependencies,
             FlexibleInstances, PatternGuards, FlexibleContexts #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  Security.InfoFlow.Policy.FlowLocks.DatalogConvert
-- Copyright   :  (c) Bart van Delft 2013
-- License     :  BSD-style (see the file LICENSE.txt)
--
-- Maintainer  :  Bart van Delft, vandeba@chalmers.se
-- Stability   :  transient
-- Portability :  portable
--
-- This module provides helper functions for converting flowlocks policies to
-- datalog input.
--
-----------------------------------------------------------------------------
module Security.InfoFlow.Policy.FlowLocks.DatalogConvert
    (
     polToDatalog, lockToFact, addActsetFacts, generateActSetRel
    ) where

import Security.InfoFlow.Policy.FlowLocks.Lattice
import Security.InfoFlow.Policy.FlowLocks.Lock
import Security.InfoFlow.Policy.FlowLocks.ActorSet
import Security.InfoFlow.Policy.FlowLocks.GlobalPolicy
import Security.InfoFlow.Policy.FlowLocks.Policy  as Policy
import Security.InfoFlow.Policy.FlowLocks.Datalog as Datalog

import Data.Maybe
import Control.Monad (filterM)


-- | Convert policy to Datalog program
polToDatalog :: (ActorSet m actset aid, Show name)
             => [DatalogClause name actset] 
             -> m [Datalog.Clause (PredicateName actset name) aid] 
polToDatalog pol = do
 clauses <- mapM (\(DatalogClause asets pr prs) -> do
     heads  <- predToAtom asets pr         -- list of heads
     bodies <- mapM (predToAtom asets) prs -- list of bodies
     setAts <- setsToAtoms asets           -- infinite sets
     return 
       [Datalog.Clause h (b ++ setAts) | h <- heads, b <- cart $ bodies])
            pol
 return $ concat clauses
 where
  -- | Folding carthesian product
  cart :: [[a]] -> [[a]]
  cart []     = [[]]
  cart (x:xs) = [y:ys | y <- x, ys <- cart xs]
  -- | Convert policy predicate to Datalog atom. Can be a set because of
  -- finite sets
  predToAtom :: ActorSet m actset aid
             => [actset]
             -> Predicate name 
             -> m [Datalog.Atom (PredicateName actset name) aid]
  predToAtom asets (FlowPred (QuantActor i)) = do
    setm <- enumSetMembers (asets !! i)
    case setm of
      Just s  -> return $ map (\aid -> Datalog.Atom 
                          FlowPredName [ConstantArg (Constant aid)]) s
      Nothing -> return $ [Datalog.Atom FlowPredName [Variable i]]
  predToAtom _ (FlowPred _) = 
    error "Non quantified flow predicate in policy?"
  predToAtom asets (AtomPred (Policy.Atom n acts)) = do
    argOpts <- mapM (argToAtom asets) acts
    return $ [Datalog.Atom (LockPredName n) args | args <- cart $ argOpts]

  argToAtom :: ActorSet m actset aid
            => [actset]
            -> ActorRep
            -> m [Datalog.Argument aid]
  argToAtom asets (QuantActor i) = do
    setm <- enumSetMembers (asets !! i)
    case setm of
      Just s  -> return $ map (\a -> ConstantArg (Constant a)) s
      Nothing -> return $ [Variable i]
  argToAtom _ HeadActor = error "All head actors should be gone"

  -- | Convert indexed list of actor sets to Datalog atoms, stating that
  -- each variable should be in its indexed actor set.
  setsToAtoms :: ActorSet m actset aid
              => [actset]
              -> m [Datalog.Atom (PredicateName actset name) aid]
  setsToAtoms as = do
    atoms <- mapM (\(a,i) -> do
                      sm <- enumSetMembers a
                      case sm of
                        Nothing -> return $ Just $ 
                           Datalog.Atom (ActSetPredName a) [Variable i]
                        Just _  -> return $ Nothing
                  ) $ zip as [0..]
    return $ catMaybes atoms

-- | For each actor id, create the set of facts that it belongs to the
-- actor sets as is dictated by the ActorSet class
addActsetFacts :: ActorSet m actset aid
               => [aid]
               -> [actset]
               -> m [Datalog.Fact (PredicateName actset name) aid]
addActsetFacts aIDs aSets = do
  -- facts for concrete actor IDs
  res1 <- mapM (\aID -> do 
          inS <- filterM (inSet aID) aSets
          return $
            map (\s -> Datalog.Fact (ActSetPredName s) [Constant aID]) inS
          ) aIDs
  -- facts for expanded finite sets
  res2 <- mapM(\s -> do
            aids <- enumSetMembers s
            case aids of
              Just as -> return 
                [Datalog.Fact (ActSetPredName s) [Constant a] | a <- as]
              Nothing -> return []
          ) aSets
  return $ concat res1 ++ concat res2

-- | Create datalog clauses representing the partial orders between
-- actorsets.
generateActSetRel :: ActorSet m actset aid => [actset] 
                  -> m [Datalog.Clause (PredicateName actset name) aid]
generateActSetRel aSets = do
  res <- mapM (\sA -> do
           inS <- filterM (leq sA) aSets
           return $ -- sA <= sB
             map (\sB -> Datalog.Clause 
                   (Datalog.Atom (ActSetPredName sA) [Variable 0]) 
                   [Datalog.Atom (ActSetPredName sB) [Variable 0]] ) inS
          ) aSets
  return $ concat res

-- | Convert a lock to a Datalog fact
lockToFact :: Lock name aid
           -> Datalog.Fact (PredicateName actset name) aid
lockToFact (Lock n a) = Datalog.Fact (LockPredName n) (map Constant a)
  

