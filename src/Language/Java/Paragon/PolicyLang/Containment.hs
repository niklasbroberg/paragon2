{-# LANGUAGE PatternGuards #-}
module Language.Java.Paragon.TypeCheck.Containment (lrt) where

import Language.Java.Paragon.Syntax
import Language.Java.Paragon.Error()
import Language.Java.Paragon.SourcePos
import Data.Generics.Uniplate.Data

import Language.Java.Paragon.TypeCheck.Actors
import Language.Java.Paragon.TypeCheck.Constraints
import Language.Java.Paragon.TypeCheck.Policy
import Language.Java.Paragon.TypeCheck.Locks

import Language.Java.Paragon.Interaction

-- import Debug.Trace

import qualified Data.ByteString.Char8 as B
import Data.List
import Data.Maybe

containmentModule :: String
containmentModule = typeCheckerBase ++ ".Containment"

lrt :: [(B.ByteString, ActorPolicy)] ->         -- upper bounds of rigid vars
       [TcClause TcAtom] ->                       -- global recursive properties
       [TcLock] ->                                -- current lock state
       TcPolicy TcActor ->                        -- p
       TcPolicy TcActor ->                        -- q
       Either Bool Constraint
lrt bs g ls p q =
    case (p, q) of
      _ | p == q -> Left True -- Shortcut to avoid checking things like var(0) <= var(0)
      (_, Join _ _) -> Right (LRT bs g ls p q)
      (Meet _ _, _) -> Right (LRT bs g ls p q)
      (RealPolicy rp, RealPolicy rq) -> lrtReal bs g ls rp rq
      (Join p1 p2, _) -> let
                    ap1 = lrt bs g ls p1 q
                    ap2 = lrt bs g ls p2 q
                    in case (ap1, ap2) of
                         _ | Left False `elem` [ap1, ap2] -> Left False
                         (Left True, _) -> ap2
                         (_, Left True) -> ap1 
                         _ -> Right (LRT bs g ls p q)
      (_, Meet q1 q2) -> let
                    ap1 = lrt bs g ls p q1
                    ap2 = lrt bs g ls p q2
                    in case (ap1, ap2) of
                         _ | Left False `elem` [ap1, ap2] -> Left False
                         (Left True, _) -> ap2
                         (_, Left True) -> ap1 
                         _ -> Right (LRT bs g ls p q)
      (VarPolicy _, _) -> Right (LRT bs g ls p q)
      (_, VarPolicy _) -> Right (LRT bs g ls p q)


lrtReal :: [(B.ByteString, ActorPolicy)]
        -> [TcClause TcAtom] 
        -> [TcLock]
        -> PrgPolicy TcActor 
        -> PrgPolicy TcActor 
        -> Either Bool Constraint
--lrtReal _ _ p q | any includesThis [p,q] =
--                    panic (containmentModule ++ ".lrtReal")
--                              $ "THIS in containment check: " ++ show (p,q)
lrtReal _bs g ls (TcPolicy p) (TcPolicy q) =  Left $ lrtC g ls p q
lrtReal bs g ls (TcJoin p1 p2) q = 
    lrt bs g ls (Join (RealPolicy p1) (RealPolicy p2)) (RealPolicy q)
lrtReal bs g ls p (TcMeet q1 q2) =
     lrt bs g ls (RealPolicy p) (Meet (RealPolicy q1) (RealPolicy q2))
lrtReal bs g ls p q
        | Just i <- firstRigid (TcJoin p q) = 
                    let subi pol x = substPolicy [(i, x)] pol
                        bound = top -- IF GENERIC: maybe top id $ lookup i bs
                        [[pb,pt],[qb,qt]] = map (\y -> map (subi y) [bottom, bound]) [p,q]
                        ap1 = lrt bs g ls pb qb
                        ap2 = lrt bs g ls pt qt
                    in case (ap1, ap2) of
                         _ | Left False `elem` [ap1, ap2] -> Left False
                         (Left True, _) -> ap2
                         (_, Left True) -> ap1 
                         _ -> Right (LRT bs g ls (RealPolicy p) (RealPolicy q))
        | any includesThis [p,q] =
                    let [[pb,pt],[qb,qt]] = map (\y -> map (flip substThis y) [bottom, top]) [p,q]
                        ap1 = lrt bs g ls pb qb
                        ap2 = lrt bs g ls pt qt
                    in case (ap1, ap2) of
                         _ | Left False `elem` [ap1, ap2] -> Left False
                         (Left True, _) -> ap2
                         (_, Left True) -> ap1 
                         _ -> Right (LRT bs g ls (RealPolicy p) (RealPolicy q))
lrtReal _ _ _ p q = 
    panic (containmentModule ++ ".lrtReal") 
    $ "Error: Non-computed policy provided to lrt: " ++ show (p, q)




-- If either p or q at least contain a policy variable, 
-- we know we'll send back a constraint
--lrt g ls p q = lrtV g ls p q

--lrtC :: (PrgPolicy TcAtom) -> [Lock] -> (PrgPolicy TcAtom) -> (PrgPolicy TcAtom) -> Bool
--lrtC 

-- Returns true iff under the given global policy and lock state, policy P
-- (the first argument) is less restrictive than policy Q (the second 
-- argument).
lrtC :: [TcClause TcAtom] -> 
        [TcLock] -> 
        [TcClause TcActor] -> 
        [TcClause TcActor] -> 
        Bool
lrtC globalPolicy lockState p q = let
    safeQ   = makeSafe (addFlowPredicate q)
    ruleSet = makeSafe (addFlowPredicate p) ++ makeSafe globalPolicy
    allCons = nub ([c | TcActor c <- universeBi ruleSet] ++
                   (concat [cs | TcLock _ cs <- universeBi lockState]) ++
                   [c | TcActor c <- universeBi safeQ])
    modLS = lockState ++ map (\c -> TcLock isActorLock [c]) allCons
    in foldl (\x r -> x && unifContains ruleSet modLS r) True safeQ

-- Changes the head of the rule from actor to atom = 
-- predicate Flow on that actor
addFlowPredicate :: [TcClause TcActor] -> [TcClause TcAtom]
addFlowPredicate = map (\(TcClause actor body) -> 
                           TcClause (TcAtom flow [actor]) body)
    where 
        flow    = Name defaultPos LName Nothing (Ident defaultPos (B.pack ">>Flow<<"))

isActorLock :: Name SourcePos		
isActorLock = Name defaultPos LName Nothing (Ident defaultPos (B.pack ">>IsActor<<"))

		
-- adds the IsActor(X) lock for each variable X in the head of the rule
makeSafe :: [TcClause TcAtom] -> [TcClause TcAtom]
makeSafe = map makeSafe' 
    where
        makeSafe' (TcClause (TcAtom p actors) body) = let
            iaB = nub (mapMaybe addLockIfVar actors)
            in (TcClause (TcAtom p actors) (iaB ++ body))
        addLockIfVar (TcActor _) = Nothing
        addLockIfVar (TcVar v) = Just (TcAtom isActorLock [TcVar v])
            


-- Returns True iff the provided set of rules in the given lockstate (and the
-- constants appearing in those two attributes) can derive any fact that the
-- provided single rule can derive.
unifContains :: [TcClause TcAtom] ->                
                [TcLock] ->
                TcClause TcAtom ->
                Bool
unifContains ruleSet lockState (TcClause rhead rbody) = let
    allVars      = nub [v | TcVar v <- universeBi rbody]
    -- ground substitution:
    s            = [ (allVars !! x, Fresh x "<freshConstant>") | x <- [0..(length allVars - 1)]]
    heads        = atomToLock $ applySubst s rhead 
    bodys        = map (atomToLock . applySubst s) rbody
    inpdb        = nub (bodys ++ lockState)
    in canDerive ruleSet inpdb inpdb heads

        
-- Replaces all variables with constants as they appear in the substitution.
applySubst :: [(B.ByteString, ActorId)] -> 
              TcAtom -> 
              TcAtom
applySubst s (TcAtom lName actors) = 
    TcAtom lName (map applySubstA actors)
    where
        applySubstA (TcActor i) = TcActor i
        applySubstA (TcVar v) = let
            c = lookup v s
            in maybe (TcVar v) TcActor c

-- Converts an atom to a lock.
-- Assumes all actors in TcAtom are constants!
atomToLock :: TcAtom ->
              TcLock
atomToLock (TcAtom lname actors) = TcLock lname (map conv actors)
    where conv (TcActor a) = a
          conv (TcVar _) = error "Unexpected actor variable in Lock!"

-- Preventing compiler warnings ;-)
ltrans :: ((Name SourcePos, [ActorId]) -> a) ->  
          TcLock -> 
		  a
ltrans f (TcLock n a) = f (n,a)
ltrans _ (TcLockVar _) = error "Unexpected TcLockVar in containment check!"
	  
-- Returns True iff the provided set of rules with the given database can derive
-- the desired lock.
canDerive :: [TcClause TcAtom] ->
             [TcLock] ->
             [TcLock] ->
             TcLock ->
             Bool
canDerive rules inpdb db target =
    (target `elem` db) || 
        let extendedDB = nub (oneStepDerive ++ db) in
            if length extendedDB == length db 
				then 
				{- trace ("Containment failed on database " ++ 
					       prettyPrint (filter (ltrans (\(n,_) ->  n /= isActorLock )) 
						                        inpdb)
					      ++ "\nWith desired lock: "++ prettyPrint target
					      ++ "\nWith rules: " ++ prettyPrint rules
					      ++ "\nWith db: " ++ prettyPrint db  )-}
					False 
				else 
					canDerive rules inpdb extendedDB target
    where oneStepDerive = foldl (\x y -> x ++ deriveAll y db) [] rules

-- Returns the list of all heads this rule can derive from the provided
-- database.
deriveAll :: TcClause TcAtom ->
             [TcLock] ->
             [TcLock]
deriveAll (TcClause rhead rbody) db = let
    -- generate all substitutions satisfying the body
    allSubs = generateSatSubs rbody db []
    -- apply each substitution and return the resulting heads
    in foldl (\x s -> atomToLock (applySubst s rhead) : x) [] allSubs
    
-- Returns a list of substitutions such that all atoms in the provided list are
-- mapped to locks in the provided database, building on the already existing
-- substitution. 
generateSatSubs :: [TcAtom] ->
                   [TcLock] ->
                   [(B.ByteString, ActorId)] ->
                   [[(B.ByteString, ActorId)]]
generateSatSubs [] _ s = [s]
generateSatSubs (b:bs) db s = let
    -- apply substitution so far
    nb = applySubst s b
    -- generate all substitutions possible for this atom in the body
    allSubs = generateSingSatSubs nb db
    -- branch for each possible substitution and the rest of the body
    in foldl (\x y -> x ++ generateSatSubs bs db (y ++ s)) [] allSubs
    
-- For each lock in the database into which the desired atom can be mapped, the
-- corresponding substitution is returned.
generateSingSatSubs :: TcAtom -> 
                       [TcLock] ->
                       [[(B.ByteString, ActorId)]]
generateSingSatSubs (TcAtom lName actors) db = let
    relevantDB = filter (ltrans (\(lN,_) -> lN == lName)) db
    subst = map (ltrans (\(_,a) -> genSub actors a)) relevantDB
    in catMaybes subst
    where genSub :: [TcActor] -> 
                    [ActorId] -> 
                    Maybe [(B.ByteString, ActorId)]
          genSub (_:_) [] = error "Locks of same name with different arity encountered!"
          genSub [] (_:_) = error "Locks of same name with different arity encountered!"
          genSub [] _ = Just []
          genSub (TcActor hA:hActors) (lA:lActors) = 
              if hA == lA then genSub hActors lActors else Nothing
          genSub (TcVar hA:hActors) (lA:lActors) = let
              ms = genSub hActors lActors
              in if isNothing ms then Nothing else let
                  s = fromJust ms
                  c = lookup hA s
                  -- if already substituted it should be the same as lA
                  in if isNothing c 
                      then
                          Just ((hA, lA) : s)
                      else if fromJust c == lA then 
                          Just s else Nothing

