{-# LANGUAGE Rank2Types, ImpredicativeTypes #-}

module Language.Java.Paragon.TypeCheck.Constraints where


import qualified Data.Map as Map

--import Language.Java.Paragon.Syntax (Ident) -- get rid of!

import Language.Java.Paragon.Error
import Language.Java.Paragon.TypeCheck.Policy
--import Language.Java.Paragon.TypeCheck.Containment
import Language.Java.Paragon.TypeCheck.Locks
--import Language.Java.Paragon.TypeCheck.Monad.TcCont
import Language.Java.Paragon.Interaction
import Data.List (union)
import qualified Data.ByteString.Char8 as B
--import Language.Java.Paragon.Syntax (Ident)

constraintsModule :: String
constraintsModule = typeCheckerBase ++ ".Constraints"

data Constraint = 
    LRT [(B.ByteString, ActorPolicy)] 
            [TcClause TcAtom] [TcLock] (TcPolicy TcActor) (TcPolicy TcActor)
  deriving (Show, Eq)

type ConstraintWMsg = (Constraint, Error)


splitCstrs :: Constraint -> [Constraint]
splitCstrs (LRT bs g ls p q) = [ LRT bs g ls x y | x <- disjoin p, y <- dismeet q ]
    where disjoin, dismeet :: (TcPolicy TcActor) -> [TcPolicy TcActor]
          disjoin (Join p1 p2) = (disjoin p1)++(disjoin p2)
          disjoin (Meet p1 _p2) = disjoin p1 -- TODO: Ugly strategy!!
          disjoin p' = [p']
          dismeet (Meet p1 p2) = (dismeet p1)++(dismeet p2)
          dismeet (Join p1 _p2) = dismeet p1 -- TODO: Ugly strategy!!
          dismeet p' = [p']




--Check if a given constraint p<=q verifies that q is an unknown policy of a variable
isCstrVar :: Constraint -> Bool
isCstrVar (LRT _ _ _ _ (RealPolicy _))    = False
isCstrVar (LRT _ _ _ _ (VarPolicy (TcMetaVar _ _))) = True
isCstrVar (LRT _ _ _ _ _) 
    = panic (constraintsModule ++ ".isCstrVar") 
      "Right-side of a constraint shouldn't be a join or meet!"

--Check if a given constraint p<=q verifies that q is an unknown policy of a variable
noVarLeft :: Constraint -> Bool
noVarLeft (LRT _ _ _ (RealPolicy _) _)    = True
noVarLeft (LRT _ _ _ (VarPolicy (TcMetaVar _ _)) _) = False
noVarLeft (LRT bs g ls (Join p q) r) = 
    noVarLeft (LRT bs g ls p r) || noVarLeft (LRT bs g ls q r)
noVarLeft (LRT bs g ls (Meet p q) r) = 
    noVarLeft (LRT bs g ls p r) || noVarLeft (LRT bs g ls q r)

{-
partitionM :: (Constraint -> IO Bool) -> [Constraint] -> IO([Constraint], [Constraint])
partitionM f xs = do
  xs' <- mapM (\x -> do 
                 b <- f x 
                 return (b, x)) 
         xs
  xs'' <- return $ partition fst xs'
  return $ ((map snd $ fst xs''), (map snd $ snd xs''))
-}

{-
filterM :: (Constraint -> IO Bool) -> [Constraint] -> IO([Constraint])
filterM f xs = do
  xs' <- mapM (\x -> do 
                 b <- f x 
                 return (b, x)) 
         xs
  xs'' <- return $ filter fst xs'
  return $ (map snd $ xs'')
-}

linker :: (Map.Map (TcMetaVar TcActor) [([TcLock], (TcPolicy TcActor))]) -> Constraint -> (Map.Map (TcMetaVar TcActor) [([TcLock], (TcPolicy TcActor))])
linker m (LRT _ _ ls p (VarPolicy x)) = case (Map.lookup x m) of
                                          Nothing -> Map.insert x [(ls, p)] m
                                          Just ps -> Map.insert x ((ls, p):ps) m
linker _ _                          = panic "linker shouldn't be called on a non-variable constraint" ""


-- Given (ls, p) and (ls',q) s.t. (ls, p) <= X, returns (ls `union` ls', p) if q=X, (ls, p) either
substPol :: (TcMetaVar TcActor) -> ([TcLock], (TcPolicy TcActor)) -> (([TcLock], TcPolicy TcActor)) -> ([TcLock], (TcPolicy TcActor))
substPol x (ls, px) (ls', p@(VarPolicy y)) = 
    case (x == y) of
      True  -> ((ls `union` ls'), px)
      False -> (ls', p)
substPol _ _ (_, (Join _ _)) = panic "substPol called on a Join !" ""
substPol _ _ p             = p

-- Add to a set of constraints the ones obtained by substituting a policy to a MetaVariable
substitution :: (TcMetaVar TcActor) -> ([TcLock], (TcPolicy TcActor)) -> [Constraint] -> [Constraint]
substitution _ _ [] = []
substitution x (ls, px) ((c@(LRT bs g ls' p q)):cs) = 
    let (ls'', psubst) = substPol x (ls, px) (ls',p) in
    case ((psubst == p) && (ls'' == ls')) of
      True  -> c:(substitution x (ls, px) cs)
      False -> (LRT bs g ls'' psubst q):c:(substitution x (ls, px) cs)
