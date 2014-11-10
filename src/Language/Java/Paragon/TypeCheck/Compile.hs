{-# LANGUAGE QuasiQuotes #-}
module Language.Java.Paragon.TypeCheck.Compile where

{-- Lives in TypeCheck since the compilation is partly type-driven.

import Language.Java.Paragon.Syntax
import Language.Java.Paragon.QuasiQuoter
import Language.Java.Paragon.TypeCheck.TcEnv
import Language.Java.Paragon.TypeCheck.Monad


import Data.Generics.Uniplate.Data
import Control.Applicative
import Control.Monad
import qualified Data.Map as Map
import Data.Char (toLower)
import Data.List (nub)
import Data.Maybe (fromJust)

-- shouldn't we add 'final' modifier to the actor fields?
-- what about other declarations using  primtype of policy and actor? not in method-body, not in class

compileTransform :: CompilationUnit -> TcCont r CompilationUnit
compileTransform = transformBiM compileClassDecl >=> transformBiM compileInterfaceDecl

compileInterfaceDecl :: InterfaceDecl -> TcCont r InterfaceDecl
compileInterfaceDecl = error "compileInterfaceDecl undefined"

-- 1. Remove Paragon modifiers
-- 2. Transform Paragon type params into ordinary params
-- 3. Transform body
compileClassDecl :: ClassDecl -> TcCont r ClassDecl
compileClassDecl (ClassDecl ms i tps mSuper impls cbody) =
  let ms' = removeParagonMods ms -- No lockstate mods allowed here
      (tps', tpMembers, tpPars, tpAsss) = splitTypeParams tps
  in ClassDecl ms' i tps' mSuper impls <$> 
       compileClassBody cbody tpMembers tpPars tpAsss

-- Paragon type parameters need to be replaced by runtime counterparts.
-- 1. Lock state parameters should be removed completed.
-- 2. Actor and Policy parameters need to be around at runtime. Each
--    parameter is translated into:
--     a) a field of the parameterized class
--     b) a parameter to every constructor of the class
--     c) an assignment of the parameter b) to the field a)
--        at the beginning of every constructor of the class
splitTypeParams :: [TypeParam] -> ([TypeParam],[MemberDecl],[FormalParam],[BlockStmt])
splitTypeParams = go ([],[],[],[]) -- error "compileTypeParams undefined"
    where 
      go (ttps,fds,fps,as) [] = (reverse ttps, reverse fds, reverse fps, reverse as)
      go (ttps,fds,fps,as) (tp:tps) = 
          case tp of
            TypeParam{}      -> go (tp:ttps,fds,fps,as) tps -- Retain
            LockStateParam{} -> go (   ttps,fds,fps,as) tps -- Ignore
            _ -> let (i,ty) = 
                         case tp of
                           ActorParam  i -> (i,[typeQQ| se.chalmers.paragon.ConcreteActor |])
                           PolicyParam i -> (i,[typeQQ| se.chalmers.paragon.Policy        |])
                     fd =   [fieldDeclQQ| public final #T#ty #i; |]
                     fp = [formalParamQQ| final #T#ty #i         |]
                     a  =   [blockStmtQQ| this.#i = #i;         |]
                 in go (ttps,fd:fds,fp:fps,a:as) tps
                                
compileClassBody :: ClassBody -> [MemberDecl] -> [FormalParam] -> [BlockStmt] -> TcCont r ClassBody
compileClassBody (ClassBody ds) tpMembers tpPars tpAsss = do
  ds' <- concat <$> mapM (compileDecl tpPars tpAsss) ds
  return $ ClassBody (map MemberDecl tpMembers ++ ds')

compileDecl :: [FormalParam] -> [BlockStmt] -> Decl -> TcCont r [Decl]
compileDecl _ _ (InitDecl _ _) = error "InitDecl not yet supported"
compileDecl tpPars tpAsss (MemberDecl md) = compileMemberDecl tpPars tpAsss md

compileMemberDecl :: [FormalParam] -> [BlockStmt] -> MemberDecl -> TcCont r [Decl]
compileMemberDecl tpPars tpAsss md =
    case md of
      LockDecl {} -> compileLockDecl md
      _ -> (:[]) . MemberDecl <$> compileSimpleMemberDecl tpPars tpAsss md

compileSimpleMemberDecl :: [FormalParam] -> [BlockStmt] -> MemberDecl -> TcCont r MemberDecl
compileSimpleMemberDecl tpPars tpAsss md =
    case md of
      -- Actors
      FieldDecl ms [typeQQ| actor |] varDecls -> 
          FieldDecl (removeParagonMods ms) [typeQQ| se.chalmers.paragon.ConcreteActor |] <$>
            mapM actorVarDecl varDecls
                where actorVarDecl (VarDecl (VarId i@(Ident rawI)) Nothing) 
                          = return -- [varDeclQQ| $$i = Actor.newConcreteActor($s$rawI) |]
                                   $ vDecl i $ call ["Actor","newConcreteActor"]
                                                    [Lit $ String rawI]
                      actorVarDecl vd = compileVarDecl vd

      FieldDecl ms [typeQQ| policy |] varDecls ->
          FieldDecl (removeParagonMods ms) [typeQQ| se.chalmers.paragon.Policy |] <$>
            mapM policyVarDecl varDecls
                 where policyVarDecl (VarDecl (VarId i@(Ident rawI)) 
                          (Just (InitExp (PolicyExp (PolicyLit cs)))))
                           = return $ vDecl i $ call ["Policy","newPolicy"]
                                                     (Lit (String rawI) : map clauseToExp cs)
                       policyVarDecl vd = compileVarDecl vd
          
      _ -> error $ show md

compileVarDecl :: VarDecl -> TcCont r VarDecl
compileVarDecl (VarDecl vid mInit) = VarDecl vid <$> compileVarInit mInit

compileVarInit :: Maybe VarInit -> TcCont r (Maybe VarInit)
compileVarInit Nothing = return Nothing
compileVarInit (Just (InitExp e)) = Just . InitExp <$> compileExp e
compileVarInit (Just (InitArray ai)) = Just . InitArray <$> compileArrayInit ai

compileArrayInit :: ArrayInit -> TcCont r ArrayInit
compileArrayInit _ = error "compileArrayInit: Not yet implemented"

compileExp :: Exp -> TcCont r Exp
compileExp = transformBiM compileExp'

compileExp' :: Exp -> TcCont r Exp
compileExp' (PolicyExp pe) = compilePolicyExp pe

-- For instance creation, we need to move type
-- arguments to actual arguments
compileExp' (InstanceCreation tas ct args mcbody) = do
  undefined
compileExp' (QualInstanceCreation e tas i args mcbody) = do
  undefined

compileExp' (MethodInv mi) = MethodInv <$> compileMethodInv mi

-- Lock names must be handled in a special way.
compileExp' (ExpName n) = do undefined
compileExp' (LockExp l) = return $ lockExpToExp l

compileExp' (BinOp e1 op e2) = compileBinOp op e1 e2

compileExp' e = return e

compileMethodInv :: MethodInvocation -> TcCont r MethodInvocation
compileMethodInv mi = undefined

-- Compiling binary operators. The interesting cases are
-- the ones where the operands are policies.
compileBinOp :: Op -> Exp -> Exp -> TcCont r Exp
compileBinOp = undefined

lockExpToExp :: Lock -> Exp
lockExpToExp (Lock n ans) = [expQQ| #N#n.isOpen() |]


--------------------------------------------
-- Compiling lock and policy declarations

-- Policies

compilePolicyExp :: PolicyExp -> TcCont r Exp
compilePolicyExp (PolicyLit cs) = return $
    call ["Policy","newPolicy"]
         (Lit (String "") : map clauseToExp cs)
compilePolicyExp (PolicyTypeVar i) = return $ ExpName (Name [i])
-- PolicyOf may only appear in modifiers, which will have been removed.
compilePolicyExp (PolicyOf (Ident rawI)) 
    = fail $ "compilePolicyExp: Unexpected expression policyof(" ++ rawI ++ ")"

-- Clauses and components

clauseToExp :: Clause Actor -> Exp
clauseToExp (Clause h body) = 
    let vs = nub [ a | Var a <- universeBi h ++ universeBi body ] `zip` [0..] -- Substs
        exps = actorToExp vs h : map (atomToExp vs) body
     in call ["Policy","newPClause"] exps

headToExp, atomToExp :: [(Ident,Int)] -> Atom -> Exp
headToExp vs (Atom _ acts) =
    call ["ActorList","newActorList"] (map (actorToExp vs) acts)
atomToExp vs (Atom n acts) = 
    call ["Atom","newAtom"] (ExpName n: map (actorToExp vs) acts)

actorToExp :: [(Ident,Int)] -> Actor -> Exp
actorToExp vs (Actor (ActorName n)) = ExpName n
actorToExp vs (Actor (ActorTypeVar tv)) = ExpName (Name [tv])
actorToExp vs (Var i) = 
    let k = fromIntegral $ fromJust (lookup i vs)
     in call ["Actor", "newActorVariable"] [Lit $ Int k]


-- Locks

-- Compile a lock declaration into a (static) Lock declaration 
-- plus (static) initialization of its lock properties.
-- Precondition: md is a LockDecl
compileLockDecl :: MemberDecl -> TcCont r [Decl]
compileLockDecl md =
    case md of
      LockDecl ms i@(Ident rawI) pars mLProps -> do
              let -- Properties defined in modifiers
                  lmExps = map (lockModToExp i) $ filter isLockMod ms
                  -- Properties defined explicitly
                  lpExps = maybe [] 
                             (map (lockPropToExp i) . (\(LockProperties cs) -> cs)) 
                             mLProps
                  lockE = call ["Lock","newLock"] 
                               [Lit $ String rawI, Lit $ Int (fromIntegral $ length pars)]
                  lockD = FieldDecl (Static:Final:removeParagonMods ms)
                            [typeQQ| se.chalmers.paragon.Lock |]
                            [vDecl i lockE]
              return $ MemberDecl lockD : 
                        lockExpsToInit i (lmExps ++ lpExps) -- map (uncurry $ lockRhsToMd i)
                                  -- ((lmExps ++ lpExps) `zip` [0..])
      _ -> fail $ "Internal error: compileLockDecl: " ++ show md


-- Initialization code for lock properties
lockExpsToInit :: Ident -> [Exp] -> [Decl]
lockExpsToInit _ [] = []
lockExpsToInit i es = [InitDecl True . Block $
                        map (BlockStmt . ExpStmt) es]
                        
lockPropToExp :: Ident -> Clause Atom -> Exp
lockPropToExp i@(Ident rawI) (Clause h body) =
    let vs = nub [ a | Var a <- universeBi (h:body) ] `zip` [0..] -- Substs
        exps = headToExp vs h : map (atomToExp vs) body

    in call [rawI,"addClause"] exps

lockModToExp :: Ident -> Modifier -> Exp
lockModToExp (Ident rawI) m = 
    let mname = map toLower (show m)
     in call [rawI,mname] []



isLockMod :: Modifier -> Bool
isLockMod m = case m of
  Reflexive -> True
  Transitive -> True
  Symmetric -> True
  _ -> False               

isParagonMod :: Modifier -> Bool
isParagonMod m = case m of
  Reflexive -> True
  Transitive -> True
  Symmetric -> True
  Reads _ -> True
  Writes _   -> True
  Opens _   -> True
  Closes _ -> True
  Expects _ -> True
  _ -> False

removeParagonMods :: [Modifier] -> [Modifier]
removeParagonMods = filter (not . isParagonMod) 


call :: [String] -> [Exp] -> Exp
call strs args = MethodInv $ MethodCall (Name $ map Ident strs) args

vDecl :: Ident -> Exp -> VarDecl
vDecl i init = VarDecl (VarId i) (Just $ InitExp init)

-}