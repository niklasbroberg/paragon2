module Language.Java.Paragon.TypeCheck.TcTypeDecl where

import Language.Java.Paragon.Syntax

import Language.Java.Paragon.TypeCheck.Monad
import Language.Java.Paragon.TypeCheck.Types
import Language.Java.Paragon.TypeCheck.Locks

import Language.Java.Paragon.TypeCheck.TcDecl
import Language.Java.Paragon.TypeCheck.TcExp


-----------------------------------------
-- TODO: The module structure needs refactoring

typeCheckTd :: TypeDecl -> TcBase ()
typeCheckTd (ClassTypeDecl cd) = typeCheckCd cd

typeCheckCd :: ClassDecl -> TcBase ()
typeCheckCd (ClassDecl ms i tps _super _impls (ClassBody decls)) =
  mapM_ typeCheckDecl


skolemTypeDecl :: TypeDecl -> TcType
skolemTypeDecl = undefined
------------------------------------------


skolemType :: Ident -> [TypeParam] -> (TcType, [(TypeParam,TcTypeArg)])
skolemType i tps =
    let args = map skolemParam tps
    in (clsTypeWArg [(i, args)], zip tps args)

skolemParam :: TypeParam -> TcTypeArg
skolemParam tp = case tp of
                   TypeParam i _    -> TcActualType (TcClsRefT (TcClassT [(i,[])]))
                   ActorParam  i    -> TcActualType (TcClsRefT (TcClassT [(i,[])]))
                   PolicyParam i    -> TcActualType (TcClsRefT (TcClassT [(i,[])]))
                   LockStateParam i -> TcActualLockState [TcLockVar i]


