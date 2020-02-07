{-# LANGUAGE PatternGuards #-}
module Language.Java.Paragon.PiGeneration where

import Language.Java.Paragon.Syntax
import Language.Java.Paragon.Interaction

import Data.Generics.Uniplate.Data
import Data.Data

piGenModule :: String
piGenModule = libraryBase ++ ".PiGeneration"


piTransform :: CompilationUnit () -> CompilationUnit ()
piTransform  = transformCompilationUnit
--for generating Pi there should be a package name
-- no imports
-- one type for each compilationUnit since the execution is for one class
-- but we can transform without considering that condition
transformCompilationUnit :: CompilationUnit () -> CompilationUnit ()
transformCompilationUnit (CompilationUnit _ mpDecl _  [tdecl])
  = let cu = CompilationUnit () mpDecl []  [transformTypeDecl tdecl]
    in expandLocals preName locals cu
        where prePre = fmap (\(PackageDecl _ n) -> n) mpDecl
              preName = Name () TName prePre i
              (i, locals) = gatherLocalAlps tdecl
transformCompilationUnit _ = panic (piGenModule ++ ".transformCompilationUnit")
                             "More than one type decl"

gatherLocalAlps :: TypeDecl () -> (Ident (), [Ident ()])
gatherLocalAlps td =
    case td of
      ClassTypeDecl _ (ClassDecl _ _ i _ _ _ (ClassBody _ ds)) ->
          (i, filterAlps (unDecl ds))
      InterfaceTypeDecl _ (InterfaceDecl _ _ i _ _ (InterfaceBody _ mds)) ->
          (i, filterAlps mds)
      _ -> panic (piGenModule ++ ".gatherLocalAlps") "Enum??"

-- disregard initializers
unDecl :: [Decl ()] -> [MemberDecl ()]
unDecl [] = []
unDecl (MemberDecl _ md : ds) = md : unDecl ds
unDecl (_ : ds) = unDecl ds

filterAlps :: [MemberDecl ()] -> [Ident ()]
filterAlps = go []
  where go :: [Ident ()] -> [MemberDecl ()] -> [Ident ()]
        go acc mds = foldl (flip filterAlp) acc mds

        filterAlp :: MemberDecl () -> [Ident ()] -> [Ident ()]
        filterAlp md =
            case md of
              FieldDecl _ ms (PrimType _ t) vds
                  | t `elem` [ActorT (), PolicyT ()],
                    Static () `elem` ms,
                    Final () `elem` ms ->
                      ([ i | VarDecl _ (VarId _ i) _ <- vds ] ++)
              LockDecl _ _ i _ _ -> (i:)
              _ -> id

----------------
transformTypeDecl :: TypeDecl () -> TypeDecl ()
transformTypeDecl (InterfaceTypeDecl _ (InterfaceDecl _ mods iden tparams refts ib))
  =  ClassTypeDecl () (ClassDecl () mods iden tparams Nothing refts (transformInterfaceBody ib)) -- Maybe typeDecl
transformTypeDecl (ClassTypeDecl _ (ClassDecl _ mods iden tparams mt refts (ClassBody _ dcls)))
  = ClassTypeDecl () (ClassDecl () mods iden tparams mt refts (ClassBody () $ concat $ transformDecl <$> dcls))
transformTypeDecl _ = panic (piGenModule ++ ".transformTypeDecl") "Enums not yet supported"
----------------
transformDecl :: Decl () -> [Decl ()]
transformDecl (MemberDecl _ md) = [MemberDecl () $ transformMemberDecl md]
transformDecl _ = []
----------------
transformInterfaceBody :: InterfaceBody () -> ClassBody ()
transformInterfaceBody (InterfaceBody _ mds) = ClassBody () $ (MemberDecl () . transformMemberDecl) <$> mds
-------------
transformMemberDecl :: MemberDecl () -> MemberDecl ()
transformMemberDecl f@(FieldDecl _ _ t _)
    | t == PrimType () (ActorT ()) || t == PrimType () (PolicyT ()) = f
--transformMemberDecl f@(FieldDecl _ _ [typeQQ| policy |] _) = f
transformMemberDecl (FieldDecl _ fmods ft vdecs) = FieldDecl () fmods ft (transformVarDecls vdecs)
transformMemberDecl m@(MethodDecl _ mmods mtparams mmaybet mident mformparams mexceptionspecs mb)
  | Typemethod () `elem` mmods  = m
  | otherwise  = MethodDecl () mmods mtparams mmaybet mident mformparams mexceptionspecs (transformMethodBody mb)
transformMemberDecl (ConstructorDecl _ cmods ctparams cident cformparams cexceptionspecs cb)
  = ConstructorDecl () cmods ctparams cident cformparams cexceptionspecs (transformConstructorBody cb)
transformMemberDecl x = x
-- I assumed the LockDecl and PolicyDecl should not be touch
-- Also I didnt write code for inner classes/interfaces
------
transformVarDecls :: [VarDecl ()] -> [VarDecl ()]
transformVarDecls vds = vds -- [ VarDecl () varDeclId Nothing | (VarDecl _ varDeclId _) <- vds]
-------
transformMethodBody :: MethodBody () -> MethodBody ()
transformMethodBody = const $ MethodBody () Nothing -- [methodBodyQQ|{}|]
-- maybe we have to add nothing instead of "just emptyMethodBody"
-------
transformConstructorBody ::  ConstructorBody () -> ConstructorBody ()
transformConstructorBody (ConstructorBody _ _eci _bs) = ConstructorBody () Nothing [] -- second argument nothing ?

expandLocals :: Data a => Name () -> [Ident ()] -> a -> a
expandLocals pre is = transformBi (expandLocalAlps pre is)

expandLocalAlps :: Name () -> [Ident ()] -> Name () -> Name ()
expandLocalAlps pre is n@(Name _ nt Nothing i)
    | i `elem` is = Name () nt (Just pre) i
    | otherwise   = n
expandLocalAlps _ _ n = n -- panic (piGenModule ++ ".expandLocalAlps") $ show n
