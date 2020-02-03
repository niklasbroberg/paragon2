-----------------------------------------------------------------------------
-- |
-- Module      :  Security.InfoFlow.Policy.FlowLocks.Testing.Datalog
-- Copyright   :  (c) Bart van Delft 2013
-- License     :  BSD-style (see the file LICENSE.txt)
--
-- Maintainer  :  Bart van Delft, vandeba@chalmers.se
-- Stability   :  transient
-- Portability :  portable
--
-- This module provides a test suite for
-- Security.InfoFlow.Policy.FlowLocks.Datalog
--
-----------------------------------------------------------------------------
{-# LANGUAGE FlexibleInstances #-}
module Datalog where

import Test.QuickCheck (Property, property, (==>), (.&&.),
                        Arbitrary(..), Gen, oneof, frequency, choose)

import Security.InfoFlow.Policy.FlowLocks.Datalog

import Control.Monad (liftM)

datalogTests :: Property
datalogTests =     property prop_UCSelf
              .&&. property prop_UCSelfExtraClause
              .&&. property prop_UCAddAtom
              .&&. property prop_UCAtomDB
              -- .&&. property prop_UCExtendDB

-------------------------
-- Tests
------------------------

type MyProgram = [Clause String Int]
type MyClause  = Clause String Int
type MyAtom    = Atom String Int
type MyFact    = Fact String Int

-- | Each datalog program is uniformly contained in itself for any database.
prop_UCSelf :: MyProgram -> [MyFact] -> Property
prop_UCSelf p db = property $ uniformContained p p db

-- | Each datalog program is u.c. in the same program with an additional clause
prop_UCSelfExtraClause :: MyProgram -> MyClause -> [MyFact] -> Property
prop_UCSelfExtraClause p c db = 
  property $ uniformContained p (c:p) db

-- | Each single-clause program is u.c. in the same program with an additional
-- atom.
prop_UCAddAtom :: MyClause -> MyAtom -> [MyFact] -> Property
prop_UCAddAtom c@(Clause h b) a db =
  property $ uniformContained [Clause h (a:b)] [c] db
  -- see, this one fails, as should be:
  --  property $ uniformContained [c] [(Clause h (a:b))] []

-- | Each single clause program of the form A :-  is contained in A :- B where
-- B is in the current database
prop_UCAtomDB :: MyFact -> MyFact -> [MyFact] -> Property
prop_UCAtomDB _a _b db = 
  let a = factToAtom _a
      b = factToAtom _b
  in  property $  uniformContained [Clause a []] [Clause a [b]] (_b:db)

-- | If a program is u.c. in another, then this still holds if the db is
-- extended
{- This one makes quickcheck discard many test cases
prop_UCExtendDB :: MyProgram -> MyProgram -> [MyFact] -> MyFact -> Property
prop_UCExtendDB p q db f =
  uniformContained p q db ==> uniformContained p q (f:db)
-}

-------------------------
-- Helper functions
-------------------------

factToAtom :: MyFact -> MyAtom
factToAtom (Fact p cs) = Atom p (map ConstantArg cs)

-------------------------
-- Generating arbitrary instances
-------------------------

-- When changing the code below, take note of the following.
-- * The generated programs should be /safe/
-- * Adding more variation in e.g. atom names or variable indexes does not imply
--   better test cases. Rather, there is a high chance that none of the names and
--   variables will overlap, giving trivial cases.
-- * On the other hand, limiting them too much might cause quickcheck to be
--   incapable of generating enough different programs, making it get stuck.

-- | Maximum number of clauses that can occur in a program
max_clauses :: Int
max_clauses = 10

-- | Maximum number of atoms appearing in the body of a clause
max_body_atoms :: Int
max_body_atoms = 6 

-- | Maximum number of different variable / skolem indices used.
-- Currently also used for maximum different constants used.
max_variable_index :: Int
max_variable_index = 3 

instance Arbitrary (Clause String Int) where
  arbitrary = arbitraryClause

-- | Generates a random clause, such that each variable in the head is
-- guaranteed to occur in the body as well (ie is safe).
arbitraryClause :: Gen (Clause String Int)
arbitraryClause = do head <- arbitrary 
                     lb <- choose (0,max_body_atoms)
                     body <- mapM (\_ -> arbitrary) [0..lb]
                     return $ Clause head (body ++ addSafety head)
  where -- | For each variable in the atom, return a unary atom on the predicate
        -- "Safe"
        addSafety :: Atom String Int -> [Atom String Int]
        addSafety (Atom _ arg) = map (\a -> Atom "Safe" [a]) (filter isVar arg)
        -- | Returns True iff provided argument is a variable
        isVar :: Argument Int -> Bool
        isVar (Variable _) = True
        isVar _            = False

instance Arbitrary (Argument Int) where
  arbitrary = arbitraryArgument

arbitraryArgument :: Gen (Argument Int)
arbitraryArgument = oneof [ liftM Variable arbitraryVar
                          , liftM ConstantArg arbitraryConst ]

arbitraryVar :: Gen Int
arbitraryVar = oneof $ map return [0..max_variable_index]

instance Arbitrary (Constant Int) where
  arbitrary = arbitraryConst

arbitraryConst :: Gen (Constant Int)
arbitraryConst = oneof [ liftM Constant arbitraryVar
                       , liftM SkolemConstant arbitraryVar ]

instance Arbitrary (Atom String Int) where
  arbitrary = arbitraryAtom

arbitraryAtom :: Gen (Atom String Int)
arbitraryAtom = do -- Generate three random arguments
                   arga <- arbitrary; argb <- arbitrary; argc <- arbitrary;
                   suff <- oneof $ map (\x -> return [x]) "ABCD" 
                   -- Choose the arity of the atom (0-3)
                   n <- arbitraryArity
                   case n of
                     0 -> return $ Atom ("Nullary" ++ suff) []
                     1 -> return $ Atom ("Unary"   ++ suff) [arga]
                     2 -> return $ Atom ("Binary"  ++ suff) [arga,argb]
                     3 -> return $ Atom ("Ternary" ++ suff) [arga,argb,argc]

-- | Generator for the arity of an atom, limits to be 0- upto 3-ary
arbitraryArity :: Gen Int
arbitraryArity = frequency [ (3, return 0)
                           , (3, return 1)
                           , (2, return 2)
                           , (1, return 3) ]

instance Arbitrary (Fact String Int) where
  arbitrary = arbitraryFact

arbitraryFact :: Gen (Fact String Int)
arbitraryFact = do -- Generate three random arguments
                   arga <- arbitrary; argb <- arbitrary; argc <- arbitrary;
                   suff <- oneof $ map (\x -> return [x]) "ABCD" 
                   -- Choose the arity of the atom (0-3)
                   n <- arbitraryArity
                   case n of
                     0 -> return $ Fact ("Nullary" ++ suff) []
                     1 -> return $ Fact ("Unary"   ++ suff) [arga]
                     2 -> return $ Fact ("Binary"  ++ suff) [arga,argb]
                     3 -> return $ Fact ("Ternary" ++ suff) [arga,argb,argc]

