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
module Security.InfoFlow.Policy.FlowLocks.Containment
    (
     Containment(..), ConstraintContainment(..), ActorSet(..), GlobalPolicy,
     polToDatalog
    ) where

import Security.InfoFlow.Policy.FlowLocks.Lattice
import Security.InfoFlow.Policy.FlowLocks.Lock
import Security.InfoFlow.Policy.FlowLocks.ActorSet
import Security.InfoFlow.Policy.FlowLocks.GlobalPolicy
import Security.InfoFlow.Policy.FlowLocks.Policy  as Policy
import Security.InfoFlow.Policy.FlowLocks.Datalog as Datalog
import Security.InfoFlow.Policy.FlowLocks.DatalogConvert as DatalogC
import {-# SOURCE #-} Security.InfoFlow.Policy.FlowLocks.Constraint

import Data.Maybe
import Data.List (nub)

class (Eq name, ActorSet m actset aid) => 
    Containment m pol name actset aid | pol -> name actset where
  lrt :: GlobalPolicy name actset 
      -> [Lock name aid] 
      -> pol -> pol 
      -> m Bool

{-
  lrt g ls p q = do
      eiBorC <- lrtC g ls p q
      case eiBorC of
        Left b -> return b
        Right _ -> return False
-}

class (Eq name, Eq mvar, Eq var, ActorSet m actset aid) =>
    ConstraintContainment m pol mvar var name actset aid 
        | pol -> mvar var name actset where

  lrtC :: GlobalPolicy name actset 
       -> [Lock name aid] 
       -> pol -> pol 
       -> m (Either Bool (Constraint mvar var name actset aid))

{-
  lrtC g ls p q = do
      b <- lrt g ls p q
      return $ Left b
-}

instance (Eq name, ActorSet m actset aid, Show name) =>
    Containment m (Policy name actset) name actset aid where

  lrt gpol ls (Policy _p) (Policy _q) = do
      -- Convert to policies proper Datalog programs and lock state to database
      let p       = map addFlowPredicate _p ++ gpol
          q       = map addFlowPredicate _q
          lsD     = map DatalogC.lockToFact ls
          -- Collect all actorIds and actorSets used
          aIDs  = nub $ concatMap (\(Lock _ a) -> a) ls 
          asets = nub $ concatMap (\(DatalogClause as _ _) -> as) (p ++ q)
      [pD,qD] <- mapM DatalogC.polToDatalog [p,q]
      -- Add facts to the database linking each actorId to its actorset(s)
      sFacts <- DatalogC.addActsetFacts aIDs asets
      -- Add clauses representing subset relation between actorsets
      asetRel <- DatalogC.generateActSetRel asets
      return $ Datalog.uniformContained qD (pD ++ asetRel) (sFacts ++ lsD)

instance (Eq name, Eq var, ActorSet m actset aid, Show name, Show var) =>
    Containment m (VarPolicy var name actset) name actset aid where

  lrt gpol ls p q =
      case (p,q) of
        -- Shortcut to avoid checking things like var(0) <= var(0)
        _ | p == q -> return True
        -- If both are policies at the base level, we just
        -- invoke the check at that level._ 
        (ConcretePolicy cp, ConcretePolicy cq) -> 
            lrt gpol ls cp cq

        -- For joins and meets appearing on the "right side",
        -- we simply decompose them into sub-constraints.
        (Join p1 p2, _) -> do
             ap1 <- lrt gpol ls p1 q
             if ap1 then lrt gpol ls p2 q
              else return False

        (_, Meet q1 q2) -> do
             ap1 <- lrt gpol ls p q1
             if ap1 then lrt gpol ls p q2
              else return False

        -- Otherwise, we start substituting
        _ | Just i <- firstRigid (Join p q) -> do
                 let --subi :: VarPolicy var name actset -> Policy name actset -> m (VarPolicy var name actset)
                     subi pol x = substVarPolicyM i x pol
                     -- bound :: Policy name actset
                 bound <- topM -- WITH BOUNDS: maybe top id $ lookup i bs
                 bottom <- bottomM
                 [[pb,pt],[qb,qt]] <-
                         mapM (\y -> mapM (subi y) [bottom, bound]) [p,q]
                 ap1 <- lrt gpol ls pb qb
                 if ap1 then lrt gpol ls pt qt else return False

        _ -> return False
                             
   where 
     firstRigid :: VarPolicy var name actset -> Maybe var
     firstRigid vp = 
         case vp of
           PolicyVar n -> Just n
           Join pv qv -> listToMaybe . catMaybes $ 
                           map firstRigid [pv,qv]
           Meet pv qv -> listToMaybe . catMaybes $ 
                           map firstRigid [pv,qv]
           _ -> Nothing


instance (Eq name, Eq var, Eq mvar, 
          Show name, Show var, Show mvar,
          ActorSet m actset aid) =>
--          Containment m (VarPolicy var name actset) mvar var name actset aid) =>
    ConstraintContainment m (MetaPolicy mvar var name actset) mvar var name actset aid where

  lrtC gpol ls p q =
      case (p,q) of
        -- Shortcut to avoid checking things like var(0) <= var(0)
        _ | p == q -> return $ Left True
        -- If both are policies at a lower level, we can just
        -- pass on the baton
        (VarPolicy vp1, VarPolicy vp2) -> do
                   b <- lrt gpol ls vp1 vp2
                   return $ Left b

        -- For joins and meets appearing on the "wrong side",
        -- we defer to the heuristics used in the constraint solver
        (_, MetaJoin{}) -> return $ Right $ LRT gpol ls p q
        (MetaMeet{}, _) -> return $ Right $ LRT gpol ls p q
        
        -- For joins and meets appearing on the "right side",
        -- we try to discharge as many sub-constraints as possible,
        -- only saving those that truly require the constraint solver
        (MetaJoin p1 p2, _) -> do
                    ap1 <- lrtC gpol ls p1 q
                    ap2 <- lrtC gpol ls p2 q
                    return $ 
                      case (ap1, ap2) of
                        (Left b, _) -> if b then ap2 else Left False
                        (_, Left b) -> if b then ap1 else Left False
                        _ -> Right $ LRT gpol ls p q
        (_, MetaMeet q1 q2) -> do
                    ap1 <- lrtC gpol ls p q1
                    ap2 <- lrtC gpol ls p q2
                    return $
                      case (ap1, ap2) of
                        (Left b, _) -> if b then ap2 else Left False
                        (_, Left b) -> if b then ap1 else Left False
                        _ -> Right $ LRT gpol ls p q

        -- Any (non-trivially equal) constraint involving
        -- meta-variables must be passed to the constraint solver
        (MetaVar{}, _) -> return $ Right $ LRT gpol ls p q
        (_, MetaVar{}) -> return $ Right $ LRT gpol ls p q

