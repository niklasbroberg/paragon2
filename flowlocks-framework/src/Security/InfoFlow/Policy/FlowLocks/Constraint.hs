{-# LANGUAGE MultiParamTypeClasses, FlexibleContexts #-}
module Security.InfoFlow.Policy.FlowLocks.Constraint where

import Security.InfoFlow.Policy.FlowLocks.GlobalPolicy
import Security.InfoFlow.Policy.FlowLocks.Lock
import Security.InfoFlow.Policy.FlowLocks.Policy
import Security.InfoFlow.Policy.FlowLocks.Containment

import qualified Data.Map as Map
import Data.List (partition, union, nub)

-- TODO: Include error information
data Constraint mvar var name actset aid
    = LRT (GlobalPolicy name actset) 
          [Lock name aid] 
          (MetaPolicy mvar var name actset) 
          (MetaPolicy mvar var name actset)
  deriving (Eq, Show)


solve :: (Eq name, Eq mvar, Eq var, Ord mvar, Show mvar, Show var, Show name,
          ActorSet m actset aid) =>
         [Constraint mvar var name actset aid] -> m Bool
solve [] = return True
solve cs = do
    let wcs = nub $ concatMap normalizeConstraints cs -- TODO: FIX head!!
        -- wcs = normalizeConstraints $ head cs
        cVars = -- trace ("wcs length: " ++ show (length wcs)) $
                   filter isConstraintForVar wcs
        cVarMap = -- trace ("cVars length: " ++ show (length cVars)) $
                   foldr linker Map.empty cVars
        cSubsts = -- trace ("cVarMap size: " ++ show (Map.size cVarMap)) $
                   nub $
                    Map.foldrWithKey
                     (\x pxs cs' -> 
                          foldr (\px cs'' -> substitution x px cs'') 
                              cs' pxs) 
                             wcs cVarMap
        -- After substitution, this partition gives us the list
        -- of constraints from which we can infer concrete policies
        -- for the meta-variables, and the list of constraints,
        -- now void of meta-variables, that need to be solved in order
        -- for there to exist a solution in the first place.
        (_toInfer, ccstright) = -- trace ("cSubsts length: " ++ show (length cSubsts)) $
                                   partition isConstraintForVar cSubsts
        -- The substitution above will have ensured that we only
        -- need to look at comparisons between concrete policies.
        toBeChecked = filter noVarLeft ccstright

    bs <- -- trace ("toBeChecked length: " ++ show (length toBeChecked)) $
            mapM checkConstraint toBeChecked
    --trace (show bs ++ " : " ++ show (and bs)) $ 
    return $ and bs

       where 
         linker ~(LRTNF _ ls p (CMetaVar x)) = 
                  Map.insertWith (++) x [(ls,p)]


-- The aim is to get all constraints on a normal form
-- where both right- and left-hand sides either
-- single meta-variables, or policies not containing
-- any meta-variables. We capture this normal form
-- in a special (set of) data type(s).
data ConstraintNF mvar var name actset aid
    = LRTNF (GlobalPolicy name actset)
            [Lock name aid]
            (ConstraintPol mvar var name actset)
            (ConstraintPol mvar var name actset)
  deriving (Eq, Show)

-- This data type is a restriction of 'MetaPolicy',
-- which allows no joins or meets involving
-- meta-variables.
data ConstraintPol mvar var name actset
    = CMetaVar mvar
    | CVarPolicy (VarPolicy var name actset)
  deriving (Eq, Show)

{-- We use a naively conservative approach,
-- where in the case of meets/joins appearing on the "wrong"
-- side of the operator, we just pick one of the operands.
-- Example: 
--     x `glb` y `leq` z <= x `leq` z 
-- Note that => does not hold, so the algorithm is not complete.
--
-- UPDATE: No longer quite so naive, now instead we attempt
-- to be slightly more precise:
--     x `glb` y `leq` z <= x `leq` z || y `leq` z
--}
normalizeConstraints :: Constraint mvar var name actset aid 
                     -> [ConstraintNF mvar var name actset aid]
normalizeConstraints (LRT g ls p q) =
    [ LRTNF g ls x y | x <- splitLhs p, y <- splitRhs q ]

  where
    splitLhs :: MetaPolicy mvar var name actset 
             -> [ConstraintPol mvar var name actset]
    splitLhs (MetaJoin p1 p2) = let
      cs1 = splitLhs p1
      cs2 = splitLhs p2
      in cs1 ++ cs2
    splitLhs (MetaMeet p1 _p2) = splitLhs p1
    splitLhs (MetaVar n) = [CMetaVar n]
    splitLhs (VarPolicy vp) = [CVarPolicy vp]
      
    splitRhs :: MetaPolicy mvar var name actset 
             -> [ConstraintPol mvar var name actset]
    splitRhs (MetaJoin p1 _p2) = splitRhs p1
    splitRhs (MetaMeet p1 p2) = let
      cs1 = splitRhs p1
      cs2 = splitRhs p2
      in cs1 ++ cs2
    splitRhs (MetaVar n) = [CMetaVar n]
    splitRhs (VarPolicy vp) = [CVarPolicy vp]
{-
normalizeConstraints (LRT g ls p q) =
    [ [ LRTNF g ls x y | x <- xs, y <- ys ]
      | xs <- splitLhs p, ys <- splitRhs q ]

  where
    splitLhs :: MetaPolicy mvar var name actset 
             -> [[ConstraintPol mvar var name actset]]
    splitLhs (MetaJoin p1 p2) = do
      cs1 <- splitLhs p1
      cs2 <- splitLhs p2
      [ cs1 ++ cs2 ]
    splitLhs (MetaMeet p1 p2) = do
      cs1 <- splitLhs p1
      _cs2 <- splitLhs p2
      [ cs1 {-, cs2 -} ]
    splitLhs (MetaVar n) = [[CMetaVar n]]
    splitLhs (VarPolicy vp) = [[CVarPolicy vp]]
      
    splitRhs :: MetaPolicy mvar var name actset 
             -> [[ConstraintPol mvar var name actset]]
    splitRhs (MetaJoin p1 p2) = do
      cs1 <- splitRhs p1
      _cs2 <- splitRhs p2
      [ cs1 {-, cs2 -} ]
    splitRhs (MetaMeet p1 p2) = do
      cs1 <- splitRhs p1
      cs2 <- splitRhs p2
      [ cs1 ++ cs2 ]
    splitRhs (MetaVar n) = [[CMetaVar n]]
    splitRhs (VarPolicy vp) = [[CVarPolicy vp]]
-}


-- Checks whether the given constraint is on the form
-- pol `leq` x for some meta variable x, i.e. 
-- satisfies the first condition for the constraint
-- solver "normal form".
isConstraintForVar :: ConstraintNF mvar var name actset aid -> Bool
isConstraintForVar (LRTNF _ _ _ (CMetaVar _)) = True
isConstraintForVar _ = False


-- Checks whether the left-hand operand of the
-- constraint is free from meta-variables,
-- in which case it should be checked.
noVarLeft :: ConstraintNF mvar var name actset aid -> Bool
noVarLeft (LRTNF _ _ (CMetaVar _) _) = False
noVarLeft _ = True


-- Add to a set of constraints the ones obtained by 
-- substituting a policy to a MetaVariable
substitution :: (Eq name, Eq mvar, Eq aid, Show name) =>
                mvar 
             -> ([Lock name aid], ConstraintPol mvar var name actset) 
             -> [ConstraintNF mvar var name actset aid]
             -> [ConstraintNF mvar var name actset aid]
substitution x (ls, px) = goSubst
  where
    goSubst [] = []
    goSubst (c@(LRTNF g ls' p q):cs) =
        let newConstr =
                case substPol x (ls, px) (ls',p) of 
                  Nothing -> id --c : goSubst cs
                  Just (ls'', pSubst) -> (LRTNF g ls'' pSubst q :) 
        in newConstr $ c : goSubst cs


-- Given (ls, p) and (ls',q) s.t. (ls, p) <= X, 
-- returns (ls `union` ls', p) if q=X, (ls, p) otherwise
-- Wrap result in a 'Maybe', to flag if a change was made
substPol :: (Eq name, Eq mvar, Eq aid, Show name) => 
            mvar 
         -> ([Lock name aid], ConstraintPol mvar var name actset) 
         -> ([Lock name aid], ConstraintPol mvar var name actset) 
         -> Maybe ([Lock name aid], ConstraintPol mvar var name actset)
substPol x (ls, px) (ls', CMetaVar y) = 
    if x == y then Just (ls `union` ls', px) else Nothing
substPol _ _ _ = Nothing

checkConstraint :: 
    (Eq name, Eq var, Eq mvar, Show name, Show var, Show mvar,
     ActorSet m actset aid) => 
    ConstraintNF mvar var name actset aid -> m Bool
checkConstraint ~(LRTNF g ls (CVarPolicy p) (CVarPolicy q)) =
    lrt g ls p q


