{-# LANGUAGE MultiParamTypeClasses, FlexibleInstances, UndecidableInstances,
             DeriveDataTypeable #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  Security.InfoFlow.Policy.FlowLocks.Policy
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
module Security.InfoFlow.Policy.FlowLocks.Policy
    (
     -- $policy

     Policy(..), Clause(..), Atom(..), ActorRep(..),

     VarPolicy(..), MetaPolicy(..),

     substVarPolicy, substVarPolicyM, substVarInMetaPolicyM

    ) where


import Security.InfoFlow.Policy.FlowLocks.Lattice

import Control.Monad (filterM, liftM)
import Data.List (groupBy)
import Data.Generics (Data, Typeable)

-- $policy
--   The Flow Locks framework is parameterised over a
--   a domain of actors, and a notion of "distinguished
--   actor sets" - subsets of the powerset lattice of 
--   actors - that determine how actor sets may be
--   specified within the domain. 
--   We require that the distinguished actor sets form
--   a join semi-lattice.
--
--   We distinguish policies on three different levels.
--   At the first and most basic level we only allow 
--   concrete policies, i.e. sets of clauses.
--   At the second level we allow for policy variables,
--   and at the third level we also allow meta-variables.
--   The difference between policy variables and meta-
--   variables are that the former represent a specific
--   (but unknown) rigid policy, whereas the latter
--   are unification variables that an inference 
--   constraint solver should infer.


----------------------------------
{- Level one: Concrete policies -}
----------------------------------

-- | Policies are sets of clauses.
newtype Policy name actset = Policy [Clause name actset]
  deriving (Eq, Ord, Show, Data, Typeable)

-- | A clause is represented by three things:
--   1) the domain of the head variable
--   2) the domains of all quantified variables
--   3) the set of 'Atom's forming its body
data Clause name actset
    = Clause actset [actset] [Atom name]
      deriving (Eq, Ord, Show, Data, Typeable)

-- | 'Atom's are predicates on locks being
--   open, for certain actors. Actors
--   are not represented by concrete identities,
--   but rather by membership in actor sets,
--   referred to by the relevant 'ActorRep's.
--   An 'Atom' thus cannot be fully interpreted
--   outside the context of a clause where those
--   qualifier actor sets are specified.
data Atom name = Atom name [ActorRep]
  deriving (Eq, Ord, Show, Data, Typeable)

-- | An 'ActorRep' is little more than an index
--   pointer into the relevant list of actor sets,
--   except the actor mentioned in the head is
--   distinguished.
data ActorRep = HeadActor | QuantActor Int
                deriving (Eq, Ord, Show, Data, Typeable)


-- Clauses form a partial order
instance (Eq name, PartialOrder m actset) =>
    PartialOrder m (Clause name actset) where

  leq (Clause headA qualA bodyA) (Clause headB qualB bodyB) = do
      -- A clause A is less restrictive (enables more flows)
      -- than another clause B iff:
      -- 
      -- 1) The head of A is less restrictive than the head of B,
      --    i.e. A represents a superset of B in terms of actor sets
      --    (note the PartialOrder prerequisite on actor sets)
      bHead <- headA `leq` headB

      -- 2) Each atom (constraint) in the body of A is also a
      --    captured by the body of B: 
      --        \forall a \in A. \exists b \in B. a \leq b
      --    where we assume a partial order for atoms 
      --    (see 'subsumed' below).
      bsBody <- mapM subsumed bodyA -- could be made lazier
      return $ and (bHead:bsBody) -- 'and' since all these must hold

          -- Atoms sort of form a partial order, except it works only in 
          -- the context of en enclosing clause. The function here assumes
          -- as implicit arguments all the information from both clauses,
          -- in particular the body and qualifiers of B, and the
          -- qualifiers of A
          where subsumed (Atom nameA repsA) = do
                  -- First, find all the atoms that mention the same
                  -- lock. In the absence of global lock properties,
                  -- an atom can only ever be subsumed by an atom
                  -- mentioning the same lock, so these are our 
                  -- only possible candidates.
                  let candidates = [ repsB | Atom nameB repsB <- bodyB,
                                             nameB == nameA ]
                  -- Second, check if any of the candidate atoms found
                  -- mention actor reps that in turn form a no less 
                  -- restrictive sequence. For this we have two
                  -- requirements:
                  bs <- mapM (\repsB -> do
                                -- 1) Each actor rep in A must in 
                                --    isolation be less restrictive
                                --    than that on the corresponding
                                --    position in B.
                                bs <- mapM (uncurry subs) 
                                           (zip repsA repsB)
                                -- 2) Also, if any actor rep appears
                                --    more than once in A, the same
                                --    actor rep must appear in each
                                --    corresponding position in B.
                                --    (\exists F. F(A) = B).
                                let c = isConsistent repsA repsB
                                return $ and (c:bs))
                             candidates
                  return $ or bs -- 'or' since we only need one match.

                -- Check subsumption for actor reps:
                -- 1) if both mention their heads, this follows 
                --    from an earlier check on the heads
                subs HeadActor HeadActor = return True
                -- 2) A quantified actor in A may map to the
                --    head of B, if its domain is less restrictive.
                subs (QuantActor iA) HeadActor =
                     (qualA!!iA) `leq` headB
                -- 3) Same as for 2), but where both are quantified.
                subs (QuantActor iA) (QuantActor iB) = 
                     (qualA!!iA) `leq` (qualB!!iB)
                -- 4) The head of A may never map to a quantified
                --    actor rep in B.
                subs _ _ = return False

                -- checks that there is a functional map 
                -- from quantified reps in repsA to reps in
                -- repsB
                isConsistent repsA repsB 
                    = let pairs = zip repsA repsB
                          -- Group by the reps in A ...
                          groups = groupBy eqFsts pairs
                          eqFsts (f1,_) (f2,_) = f1 == f2
                          -- ... and check that those groups
                          -- are internally consistent.
                          allEqual ~(x:xs) = all (==x) xs
                      in and $ map allEqual groups
                    

-- Clauses form a join semi-lattice as long as the
-- actor sets form a join semi-lattice, but not a full
-- lattice, regardless of whether the actor sets
-- form a full lattice or not.
-- The reason is that clauses are not closed under
-- glb in general (requires disjunction, which is 
-- the power that policies give).
instance (Eq name, JoinSemiLattice m actset) =>
    JoinSemiLattice m (Clause name actset) where

  -- Formally, 
  --  { \forall a \in X.     -- clause head
  --     \forall b_1 \in B_1 ... b_n \in B_n.
  --      a : \Sigma_X } \lub
  --  { \forall a \in /.
  --     \forall c_1 \in C_1 ... c_n \in C_n.
  --      a : \Sigma_Y } =
  --  { \forall a \in (X \lub Y).
  --     \forall b_1 \in B_1 ... b_n \in B_n,
  --             c_1 \in C_1 ... c_m \in C_m.
  --      a : \Sigma_X \union \Sigma_Y }
  lub (Clause headA qualsA atomsA) (Clause headB qualsB atomsB) = do
      headC <- headA `lub` headB -- (X \lub Y)
      -- We offset the indexes in the second atom list (atomsB)
      -- to reflect the concatenation of the lookup lists (qualsA/B)
      let offset = length qualsA
          inc (Atom name reps) = Atom name (map incRep reps)
              where incRep HeadActor      = HeadActor
                    incRep (QuantActor i) = QuantActor (i+offset)
          atomsBoff = map inc atomsB

      return $ Clause 
                 headC                 -- (X \lub Y)
                 (qualsA ++ qualsB)    -- (B_1xB_2x...xC_1x...xC_m)
                 (atomsA ++ atomsBoff) -- (\Sigma_X \union \Sigma_Y)

  -- We can form a top element by appealing to that
  -- from the underlying domain of actor sets,
  -- which must be isomorphic to the empty set.
  topM = topM >>= \t -> return $ Clause t [] []

  -- ... but any clause with a head that is 
  -- isomorphic to the empty set is semantically
  -- equivalent to top, regardless of its body
  -- (it can never allow any flows).
  isTop (Clause headC _ _) = isTop headC



-- Policies for a partial order:
--  P \leq Q =
--    \forall d \in Q. 
--     \exists c \in P. c \leq d
instance (Eq name, PartialOrder m actset) =>
    PartialOrder m (Policy name actset) where
  
  --  P \leq Q =
  Policy clausesP `leq` Policy clausesQ = do
      -- \forall d \in Q. 
      forall clausesQ $ \d ->
          -- \exists c \in P. c \leq d
          exists clausesP $ \c -> c `leq` d

-- Policies, which are nothing more than sets of clauses,
-- in theory form a full lattice as long as the actor
-- sets form a join semi-lattice. In practice however,
-- we cannot represent the bottom element as the
-- (possibly infinite) list of clauses for all possible
-- heads, which is what we need unless the actor set
-- lattice has a bottom element (which means it is
-- a full lattice). 
-- We could, hypothetically, add a distinguished bottom
-- element to the policy data type, but since most (read:
-- all practical that we care about) actor set lattices
-- have a bottom element already, that would just
-- complicate things.
instance (Eq name, JoinSemiLattice m actset) => 
    JoinSemiLattice m (Policy name actset) where

  lub (Policy cs1) (Policy cs2) = do
      -- Try all possible combinations first.
      cartProd <- sequence [ c1 `lub` c2 | c1 <- cs1, c2 <- cs2 ]
      -- Since top-equivalent clauses never add anything
      -- semantically, we filter them out for succinctness.
      allNonTop <- filterM ((liftM not) . mustBeTop) cartProd
      return $ Policy allNonTop

  topM = return $ Policy []
  -- A policy can be equivalent to 'top' even if
  -- is not identical -
  -- it suffices that the heads of all clauses are 'top'
  isTop (Policy cs) = go (Just True) cs
    where go b [] = return b
          go b (cl:cls) = do
            clIsTop <- isTop cl
            case clIsTop of
              -- Finding just one non-top clause is
              -- sufficient to tell the whole policy
              -- is non-top
              Just False -> return $ Just False
              -- If this clause is definitely top,
              -- then all depends on the other clauses.
              Just True  -> go b cls
              -- If we can't tell what this clause is,
              -- we won't be able to tell what the whole
              -- policy is, unless we later encounter
              -- on that is definitely non-top.
              Nothing    -> go Nothing cls
      

instance (Eq name, Lattice m actset) => 
    Lattice m (Policy name actset) where
  -- Policies give the necessary disjunction needed to
  -- form the 'glb' by simply concatenating clauses.
  -- TODO: Remove subsumed clauses.
  glb (Policy cs1) (Policy cs2) = return $ Policy (cs1 ++ cs2)

  -- If the actor set has a bottom element, we can
  -- form the bottom element of the policy lattice,
  -- as discussed above.
  bottomM = bottomM >>= (\b -> return $ Policy [Clause b [] []])

  -- isBottom is the default instantiation

----------------------------------------
{- Level two: Policies with variables -}
----------------------------------------

-- | A 'VarPolicy' represents a term in a richer policy
--   algebra which also allows for variables as operands.
--   Unlike for concrete policies, we cannot compute
--   joins and meets of terms involving variables,
--   so we must represent them in the algebra.
data VarPolicy var name actset
    = ConcretePolicy (Policy name actset)
    | PolicyVar var
    | Join (VarPolicy var name actset) (VarPolicy var name actset)
    | Meet (VarPolicy var name actset) (VarPolicy var name actset)
  deriving (Eq, Ord, Show, Data, Typeable)


substVarPolicyM :: (Eq name, Eq var, Lattice m actset) =>
                   var
                -> Policy name actset
                -> VarPolicy var name actset
                -> m (VarPolicy var name actset)
substVarPolicyM n qpol = goSubst
    where
      --goSubst :: VarPolicy var name actset -> m (VarPolicy var name actset)
      goSubst pv =
          case pv of
            PolicyVar m
                | n == m -> return $ ConcretePolicy qpol
            Join pv1 pv2 -> do 
                    pol1 <- goSubst pv1
                    pol2 <- goSubst pv2
                    pol1 `lub` pol2
            Meet pv1 pv2 -> do 
                    pol1 <- goSubst pv1
                    pol2 <- goSubst pv2
                    pol1 `glb` pol2
            _ -> return pv

substVarPolicy :: (Eq name, Eq var) =>
                  var
               -> Policy name actset
               -> VarPolicy var name actset
               -> VarPolicy var name actset
substVarPolicy n qpol = goSubst
    where
      goSubst pv =
          case pv of
            PolicyVar m
                | n == m -> ConcretePolicy qpol
            Join pv1 pv2 -> let
                    pol1 = goSubst pv1
                    pol2 = goSubst pv2
                    in Join pol1 pol2
            Meet pv1 pv2 -> let 
                    pol1 = goSubst pv1
                    pol2 = goSubst pv2
                    in Meet pol1 pol2
            _ -> pv

{-
-- | 'RigidVar's denote variables representing some existing, 
--   concrete (constant) policy that we simply don't know the 
--   value of at this point. Such variables can be instantiated 
--   with an actual value, but where they exist during 
--   entailment, we must assume they could take on any value,
--   hence they are rigid (skolems).
data RigidVar name = RigidVar name
  deriving (Eq, Show)
-}

{-- | A 'VarPolicy' represents a term in a richer policy
--   algebra which also allows for variables as operands.
--   Note that we represent such terms on a normal form,
--   as a disjunction of conjunctions of variables and
--   concrete policies.
data VarPolicy name actset
    = Meet [ConjVarPolicy name actset]
  deriving (Eq, Show)

-- | A conjunction consists of a concrete policy (computed
--   through consecutive constant folding), a set of
--   rigid variables, and a set of meta-variables.
data ConjVarPolicy name actset
    = Join 
        (Policy name actset) 
        [RigidVar name] 
        [MetaVar name]
  deriving (Eq, Show)

-- We would have:

-- Convenient helper
subsetOf :: Eq a => [a] -> [a] -> Bool
subsetOf xs ys = all (`elem` ys) xs

-- Here we conservatively approximate the partial order
-- on policies, seeing how we cannot tell in general
-- what influence the meta-variables will have.
-- The only time we are "safe" is when all
-- meta-variables on the left-hand side also appear
-- on the right-hand side. Then it works for any
-- instantiation of those variables (which is
-- already the way we have to handle rigid vars).
instance (Eq name, PartialOrder m actset) =>
    PartialOrder m (ConjVarPolicy name actset) where
  leq (Join polP rigidVsP metaVsP)
      (Join polQ rigidVsQ metaVsQ) = do
          b1 <- polP `leq` polQ 
          let b2 = rigidVsP `subsetOf` rigidVsQ
              b3 = metaVsP  `subsetOf` metaVsQ
          return $ and [b1,b2,b3]

instance (Eq name, JoinSemiLattice m actset) =>
    JoinSemiLattice m (ConjVarPolicy name actset) where

  -- Forming the conjunction of conjunctions is
  -- easy - the only caveat is that we perform
  -- constant folding on the concrete policies.
  lub (Join polP rigidVsP metaVsP) 
      (Join polQ rigidVsQ metaVsQ) = do
          polC <- polP `lub` polQ
          return $ Join polC 
                     (rigidVsP ++ rigidVsQ) 
                     (metaVsP  ++ metaVsQ)

  top = Join top [] []


instance (Eq name, PartialOrder m actset) =>
    PartialOrder m (VarPolicy name actset) where

  -- This is beautiful.
  leq (Meet conjsP) (Meet conjsQ) =
      forall conjsQ $ \q ->
          exists conjsP $ \p ->
              p `leq` q

instance (Eq name, JoinSemiLattice m actset) =>
    JoinSemiLattice m (VarPolicy name actset) where

  -- For the conjunction of disjunctions, we
  -- need to distribute.
  lub (Meet conjsP) (Meet conjsQ) = do
      -- Compute a cartesian product of joins,
      -- which forms a distribution of the
      -- join over the disjunctions.
      conjsR <- sequence [ conP `lub` conQ |
                           conP <- conjsP, conQ <- conjsQ]
      return $ Meet conjsR

  top = Meet [top]
  -- TODO: isTop = ?


-- With the normal form for policies, we can
-- represent the bottom element even in the absence
-- of a bottom element for concrete policies,
-- as the degenerate empty disjunction.
instance (Eq name, JoinSemiLattice m actset) =>
    Lattice m (VarPolicy name actset) where
  
  glb (Meet conjsP) (Meet conjsQ) = 
      return $ Meet (conjsP ++ conjsQ)
  
  bottom = Meet []
  -- TODO: isBottom = ?

{-
If we do this then we can represent both top and bottom
in this algebra, regardless of whether the actor set has
a well-defined bottom:

  top    = Meet [Join top []]
  bottom = Meet [] 

We still can't say for sure if something is top/bottom
since we don't know the values of the variables -
but at least it's something. Not entirely sure what
we use isTop/isBottom for except to optimize policies,
which would be less of an issue with this NF representation.
Still, then we can give conservative approximative answers,
and optimize where we can.

We would then have (pseudo-code): 


  -- NB: I believe this is not "complete" in general. 
  Meet conjsP `leq` Meet conjsQ =
      forall (q <- conjsQ). exists (p <- conjsP). p `leq` q

  Join polP varsP `leq` polQ varsQ =
      polP `leq` polQ && varsP `subset` varsQ

Correct me if I'm wrong, but I believe that this should work
even when we involve lock states and global policies, with
only slightly more complexity.

  -- NB: Again, not "complete" in general.
  Meet conjsP `lrt{G,LS}` Meet conjsQ =
      forall (q <- conjsQ). exists (p <- conjsP). p `lrt{G,LS}` q

  -- No meta variables
  Join polP (varsP,[])    `lrt{G,LS}` Join polQ (varsQ,[])    =
      polP `lrt{G,LS}` polQ && varsP `subset` varsQ

  -- With meta variables
  Join polP (varsP,metaP) `lrt{G,LS}` Join polQ (varsQ,metaQ) =
      ???

OK, I don't actually know exactly what to put here other than for simple
cases. But it seems to me that in the presence of meta-variables,
with this normal form representation we should be able to get
much more precise constraints - albeit disjunctions of conjunctions
of constraints, which might be far less efficient than what we
currently have (exponentially so). But if we're doing approximations
now, we should be able to do at least as good approximations with this
representation, no?

At any case, this is all just food for thought at this point.

-}-}
{-
-- | We allow two forms of variables: 
data Var name 
    = RigidVar name 
    -- ^ 'PolicyVar's denote variables representing some existing, 
    --   concrete (constant) policy that we simply don't know the 
    --   value of at this point. Such variables can be instantiated 
    --   with an actual value, but where they exist during 
    --   entailment, we must assume they could take on any value,
    --   hence they are rigid (skolems).
    | MetaVar name
    -- ^ 'MetaVar's denote unification variables to be inferred.
    --   Such variables will not be rigid during entailment, but
    --   rather give rise to constraints that must later be solved.
      deriving (Eq, Show)
-}

instance (Eq name, Eq var, PartialOrder m actset) =>
    PartialOrder m (VarPolicy var name actset) where

  -- We cannot in general decide whether two
  -- policies are comparable, if they contain
  -- arbitrary combinations of joins and meets.
  -- The implementation here is a conservative
  -- approximation. 
  leq (ConcretePolicy p) (ConcretePolicy q) = leq p q
  leq (Join p1 p2) q = do
      b1 <- leq p1 q
      b2 <- leq p2 q
      return $ b1 && b2
  leq p (Meet q1 q2) = do
      b1 <- leq p q1
      b2 <- leq p q2
      return $ b1 && b2
  leq p (Join q1 q2) = do
      b1 <- leq p q1
      b2 <- leq p q2
      return $ b1 || b2
  leq (Meet p1 p2) q = do
      b1 <- leq p1 q
      b2 <- leq p2 q
      return $ b1 || b2
  leq p q | p == q = return True
  leq _ _ = return False


instance (Eq name, Eq var, Lattice m actset) =>
    JoinSemiLattice m (VarPolicy var name actset) where

  lub p1 p2 | p1 == p2 = return p1 -- fake shortcut
  lub (ConcretePolicy p) (ConcretePolicy q) = do
      pol <- p `lub` q
      return $ ConcretePolicy pol
  lub p q = returnFirstTrue
             [(isBottom p, return q),
              (isBottom q, return p),
              (isTop p,    return p),
              (isTop q,    return q)] $ return $ Join p q

  topM = topM >>= return . ConcretePolicy

  -- We cannot in general decide whether a
  -- policy with variables is top or not,
  -- so this operation is considered "unsafe".
  isTop (ConcretePolicy p) = isTop p
  isTop _ = return Nothing

instance (Eq name, Eq var, Lattice m actset) =>
    Lattice m (VarPolicy var name actset) where

  glb (ConcretePolicy p) (ConcretePolicy q) = do
      pol <- p `glb` q
      return $ ConcretePolicy pol
  glb p q = returnFirstTrue
            [(return $ Just $ p == q, return p),
             (isTop p, return q),
             (isTop q, return p),
             (isBottom p, return p),
             (isBottom q, return q)]
            $ return $ Meet p q

  -- We cannot in general decide whether a
  -- policy with variables is top or not,
  -- so this operation is considered "unsafe".
  bottomM = bottomM >>= return . ConcretePolicy
  isBottom (ConcretePolicy p) = isBottom p
  isBottom _ = return Nothing


-----------------------------------------------
{- Level three: Policies with meta-variables -}
-----------------------------------------------

data MetaPolicy mvar var name actset
    = VarPolicy (VarPolicy var name actset)
    | MetaJoin 
         (MetaPolicy mvar var name actset) 
         (MetaPolicy mvar var name actset)
    | MetaMeet 
         (MetaPolicy mvar var name actset) 
         (MetaPolicy mvar var name actset)
    | MetaVar mvar
  deriving (Eq, Ord, Show, Data, Typeable)


-- | Substitute all occurences of given rigid variable
--   with a 'MetaPolicy'.
substVarInMetaPolicyM :: (Eq name, Eq var, Eq mvar, Lattice m actset) =>
                         var
                      -> MetaPolicy mvar var name actset
                      -> MetaPolicy mvar var name actset
                      -> m (MetaPolicy mvar var name actset)
substVarInMetaPolicyM n qpol = goSubst
    where
      goSubst pm =
          case pm of
            MetaJoin pm1 pm2 -> do
                    pol1 <- goSubst pm1
                    pol2 <- goSubst pm2
                    pol1 `lub` pol2
            MetaMeet pm1 pm2 -> do
                    pol1 <- goSubst pm1
                    pol2 <- goSubst pm2
                    pol1 `glb` pol2
            VarPolicy pv -> 
                case pv of
                  PolicyVar m 
                      | n == m -> return qpol
                  Join pv1 pv2 -> do 
                          pol1 <- goSubst (VarPolicy pv1)
                          pol2 <- goSubst (VarPolicy pv2)
                          pol1 `lub` pol2
                  Meet pv1 pv2 -> do 
                          pol1 <- goSubst (VarPolicy pv1)
                          pol2 <- goSubst (VarPolicy pv2)
                          pol1 `glb` pol2
                  _ -> return $ VarPolicy pv
            _ -> return pm

{-
-- | 'MetaVar's denote unification variables to be inferred.
--   Such variables will not be rigid during entailment, but
--   rather give rise to constraints that must later be solved.
data MetaVar name = MetaVar name
  deriving (Eq, Show)
-}

instance (Eq name, Eq var, Eq mvar, PartialOrder m actset) =>
    PartialOrder m (MetaPolicy mvar var name actset) where

  leq (VarPolicy p) (VarPolicy q) = leq p q
  leq (MetaJoin p1 p2) q = do
      b1 <- leq p1 q
      b2 <- leq p2 q
      return $ b1 && b2
  leq p (MetaMeet q1 q2) = do
      b1 <- leq p q1
      b2 <- leq p q2
      return $ b1 && b2
  leq p (MetaJoin q1 q2) = do
      b1 <- leq p q1
      b2 <- leq p q2
      return $ b1 || b2
  leq (MetaMeet p1 p2) q = do
      b1 <- leq p1 q
      b2 <- leq p2 q
      return $ b1 || b2
  leq p q | p == q = return True
  leq _ _ = return False

instance (Eq name, Eq var, Eq mvar, Lattice m actset) =>
    JoinSemiLattice m (MetaPolicy mvar var name actset) where

  lub (VarPolicy p) (VarPolicy q) = do
      pol <- p `lub` q
      return $ VarPolicy pol
  lub p q = returnFirstTrue
            [(return $ Just $ p == q, return p),
             (isBottom p, return q),
             (isBottom q, return p),
             (isTop p, return p),
             (isTop q, return q)]
            $ return $ MetaJoin p q

  topM = topM >>= return . VarPolicy
  isTop (VarPolicy p) = isTop p
  isTop _ = return Nothing

instance (Eq name, Eq var, Eq mvar, Lattice m actset) =>
    Lattice m (MetaPolicy mvar var name actset) where

  glb (VarPolicy p) (VarPolicy q) = do
      pol <- p `glb` q
      return $ VarPolicy pol
  glb p q = returnFirstTrue
            [(return $ Just $ p == q, return p),
             (isTop p, return q),
             (isTop q, return p),
             (isBottom p, return p),
             (isBottom q, return q)]
            $ return $ MetaMeet p q

  bottomM = bottomM >>= return . VarPolicy
  isBottom (VarPolicy p) = isBottom p
  isBottom _ = return Nothing



-- Helper function
returnFirstTrue :: Monad m => [(m (Maybe Bool), m a)] -> m a -> m a
returnFirstTrue [] def = def
returnFirstTrue ((test,action):xs) def = do
  b <- test
  case b of
    Just True -> action
    _ -> returnFirstTrue xs def
  
