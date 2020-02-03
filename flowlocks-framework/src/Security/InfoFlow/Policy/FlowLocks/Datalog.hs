-----------------------------------------------------------------------------
-- |
-- Module      :  Security.InfoFlow.Policy.FlowLocks.Datalog
-- Copyright   :  (c) Bart van Delft 2013
-- License     :  BSD-style (see the file LICENSE.txt)
--
-- Maintainer  :  Bart van Delft, vandeba@chalmers.se
-- Stability   :  transient
-- Portability :  portable
--
-- This module provides a data structure for Datalog and a uniform
-- containment check for Datalog programs.
--
-----------------------------------------------------------------------------
module Security.InfoFlow.Policy.FlowLocks.Datalog where

import Control.Monad (liftM2)
import Data.List (nub)
import Data.Maybe (fromMaybe, catMaybes)

-- import Debug.Trace

debugDL :: String -> a -> a
debugDL s = id -- trace s -- replace with id to have no tracing

data Constant a = Constant a | SkolemConstant Int
  deriving (Eq, Show)

data Argument a = Variable Int | ConstantArg (Constant a)
  deriving (Eq, Show)

data Atom pred a = Atom pred [Argument a]
  deriving (Eq, Show)

data Fact pred a = Fact pred [Constant a]
  deriving (Eq, Show)

data Clause pred a = Clause (Atom pred a) [Atom pred a]
  deriving (Eq, Show)

-- | Simple implementation of the uniform containment check by Sagiv ('88).
-- For each clause in the first argument, generate a ground substitution.
-- Add the facts from its body to the database provided, and see if the
-- program provided as second argument is able to derive the same head. If
-- this holds for each clause, we return True, otherwise False.
-- Assumes all clauses are safe (each variable occurring in the head is also
-- occurring in the body).
uniformContained :: (Eq pred, Eq a, Show pred, Show a)
                 => [Clause pred a]  -- ^ If this program is uniformly contained
                 -> [Clause pred a]  -- ^ in this program, assuming
                 -> [Fact pred a]    -- ^ a database of facts, this function
                 -> Bool             -- ^ returns true, false otherwise
uniformContained p1 p2 db = 
  let skp1 = nub $ map skolemize p1
  -- for each skolemized clause, add body to db, let p2 derive head
  in  debugDL ("Started UC, length p1: " ++ (show $ length skp1)) $
      and (map (\(h,b) -> canDerive (nub p2) (nub $ db ++ b) h) skp1)

-- | Creates a ground substitution for clauses, adding skolem instances for all
-- variables occurring in the clause. Returns a pair consisting of the head of
-- the clause after skolemization, and the body.
skolemize :: Clause pred a -> (Fact pred a, [Fact pred a])
skolemize (Clause h b) = (skolemizeA h, map skolemizeA b)
  where
    skolemizeA :: Atom pred a -> Fact pred a
    skolemizeA (Atom p arg) = Fact p (map skolemizeArg arg)
    skolemizeArg :: Argument a -> Constant a
    -- Due to our data representation, we simply replace each variable
    -- with a skolem constant.
    skolemizeArg (ConstantArg c) = c
    skolemizeArg (Variable x) = SkolemConstant x
 
-- | Simple implementation, a program can derive a fact from a database if this
-- fact is contained in the set of all facts derived by that program.
canDerive :: (Eq pred, Eq a, Show pred, Show a)
          => [Clause pred a] -> [Fact pred a] -> Fact pred a -> Bool
canDerive p db f = 
  debugDL ("Trying derive " ++ show f) $
  debugDL ("From db       " ++ show db) $
  debugDL ("With program  " ++ show p) $
  elem f (deriveAll p db)

-- | Return all the facts that this set of clauses can derive from the provided
-- database. Calls itself recursively as long as one iteration of applying each
-- clause once returns new facts.
deriveAll :: (Eq pred, Eq a, Show pred, Show a) 
          => [Clause pred a] -> [Fact pred a] -> [Fact pred a]
deriveAll p db = 
  let newdb = nub $ db ++ concatMap (deriveOneStep db) p
  in  debugDL ("Found new db: " ++ show newdb) $
      nub $ newdb ++ if length newdb == length db then [] else deriveAll p newdb

-- | For all possible sets of facts in the database that satisfy the body of the
-- clause, return the resulting head of that clause; throws an error if ruel is
-- unsafe and resulting head is not ground.
deriveOneStep :: (Eq pred, Eq a, Show pred, Show a) 
              => [Fact pred a] -> Clause pred a -> [Fact pred a]
deriveOneStep db (Clause h b) = 
  -- find all substitutions for the body that are in the db
  let subs = collectSubs b db
  -- add corresponding heads to result (throw error if clause was unsafe)
  in -- debugDL ("Found substitutions: " ++ show subs) $ 
     map (\s -> fromMaybe (error "Unsafe rule in uniform containment check!")
                           (applySubst h s)) subs

-- | Collects all substitutions that make the provided set of atoms ground,
-- such that all these facts are in the database.
collectSubs :: (Eq pred, Eq a, Show pred, Show a) 
            => [Atom pred a] -> [Fact pred a] -> [[(Int, Constant a)]]
collectSubs [] _ = [[]]
collectSubs (Atom prA argsA:ats) db =
  let _posSubs = map (zip argsA) [argsF | Fact prF argsF <- db,
                                    prF == prA, length argsF == length argsA]
      -- remove combinations where constants do not match
      posSubs  = catMaybes $ map (filterConst) _posSubs
      -- remove those substitutions that substitute the same variable to
      -- different constants:
      realSubs = catMaybes $ map (extendSub []) posSubs
      nextSubs = collectSubs ats db
  in  debugDL ("recursive subs, length " ++ show (length ats))  $ 
      catMaybes [extendSub r n | r <- realSubs, n <- nextSubs]
  where
    -- | When mapping arguments to constants, all variable arguments are
    -- fine, but constants should be mapped to the same constants.
    filterConst :: Eq a 
                => [(Argument a, Constant a)] -> Maybe [(Int, Constant a)]
    filterConst [] = Just []
    filterConst ((Variable i, c):xs) = fmap ((:) (i,c)) (filterConst xs)
    filterConst ((ConstantArg ca, c):xs) = 
      if ca == c then filterConst xs else Nothing


-- | Tries to extend the substitution with the supplied one. This might fail
-- if both substitutions substitute the same variable to a different constant.
extendSub :: (Eq a)
          => [(Int, Constant a)] -> [(Int, Constant a)] 
          -> Maybe [(Int, Constant a)]
extendSub sofar [] = Just sofar
extendSub sofar ((x, c):next) =
  case lookup x sofar of
    Nothing -> extendSub ((x,c):sofar) next
    Just _c -> if c == _c then extendSub sofar next
                          else Nothing

-- | Returns the same predicate with all variables changed to constants as
-- dictated by the substitution. Returns Nothing if a variable can not be
-- found in the substitution
applySubst :: (Eq a)
           => Atom pred a -> [(Int, Constant a)] -> Maybe (Fact pred a)
applySubst (Atom p args) s = fmap (Fact p) (applySubstArg args)
  where 
    applySubstArg []                 = Just []
    applySubstArg (Variable i   :xs) = liftM2 (:) (lookup i s) (applySubstArg xs)
    applySubstArg (ConstantArg c:xs) = fmap ((:) c) (applySubstArg xs)
