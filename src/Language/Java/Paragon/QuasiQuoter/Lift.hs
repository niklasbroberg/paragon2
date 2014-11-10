{-# LANGUAGE QuasiQuotes, TemplateHaskell #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}
module Language.Java.Paragon.QuasiQuoter.Lift where

import qualified Language.Haskell.TH as TH
import Language.Haskell.TH.Quote
import Language.Haskell.TH.Lift
--import Language.Haskell.TH.Lib

import Language.Java.Paragon.Syntax

import Language.Java.Paragon.QuasiQuoter.Derive

import Data.Generics (extQ)
import Data.Data


instance Lift Double where
  lift d = let s = show d 
               cs = lift s
           in  [|(read $cs)::Double|]


-- Anti-quoting

antiQ :: Data b => b -> Maybe (TH.Q TH.Exp)
antiQ = const Nothing
        `extQ` (antiCaseExp   :: Exp   () -> Maybe (TH.Q TH.Exp))
        `extQ` (antiCaseType  :: Type  () -> Maybe (TH.Q TH.Exp))
        `extQ` (antiCaseName  :: Name  () -> Maybe (TH.Q TH.Exp))
        `extQ` (antiCaseIdent :: Ident () -> Maybe (TH.Q TH.Exp))
        

-- Idents
instance (Data a, Lift a) => Lift (Ident a) where
  lift = dataToExpQ antiQ

antiCaseIdent :: Ident a -> Maybe (TH.Q TH.Exp)
antiCaseIdent (AntiQIdent _ s) = Just $ TH.varE $ TH.mkName s
antiCaseIdent _ = Nothing

-- Names
instance (Data a, Lift a) => Lift (Name a) where
  lift = dataToExpQ antiQ

antiCaseName :: Name a -> Maybe (TH.Q TH.Exp)
antiCaseName (AntiQName _ s) = Just $ TH.varE $ TH.mkName s
antiCaseName _ = Nothing

-- Types
instance (Data a, Lift a) => Lift (Type a) where
  lift = dataToExpQ antiQ

antiCaseType :: Type a -> Maybe (TH.Q TH.Exp)
antiCaseType (AntiQType _ s) = Just $ TH.varE $ TH.mkName s
antiCaseType _ = Nothing

-- Exps
instance (Data a, Lift a) => Lift (Exp a) where
  lift = dataToExpQ antiQ

antiCaseExp :: Exp a -> Maybe (TH.Q TH.Exp)
antiCaseExp (AntiQExp _ s) = Just $ TH.varE $ TH.mkName s
antiCaseExp _ = Nothing

{-               
deriveLiftAll :: [TH.Name] -> TH.Q [TH.Dec]
deriveLiftAll ns = do
  is <- mapM (addDataCx <=< TH.reify) ns
  deriveLiftMany' is

addDataCx :: TH.Info -> TH.Q TH.Info
addDataCx i = 
    case i of
      TH.TyConI (TH.DataD dcx n vsk cons _) -> do
          dp <- dataPred $ head vsk
          return $ TH.TyConI (TH.DataD (dp:dcx) n vsk cons [])
      TH.TyConI (TH.NewtypeD dcx n vsk con _) -> do
          dp <- dataPred $ head vsk
          return $ TH.TyConI (TH.NewtypeD (dp:dcx) n vsk con [])
      _ -> error $ "Unhandled Dec: " ++ show i
  where dataPred (TH.PlainTV n) = TH.classP ''Data [TH.varT n]
-}

$(deriveLiftAll [''Literal,''ClassType,''TypeArgument,
       ''ClassBody,''ArrayInit,''MethodInvocation,''Op,       
       ''AssignOp,''PolicyExp,''Lhs,''RefType,
       ''ArrayIndex,''FieldAccess,''NonWildTypeArgument,
       ''WildcardBound,''Decl,''VarInit,
       ''Clause, ''LClause,
       ''PrimType,
       ''ReturnType,
       ''Atom,
       ''Actor,
       ''ActorName,
       ''Lock,
       ''Block,
       ''MemberDecl,
       ''MethodBody,
       ''FormalParam,
       ''ExceptionSpec,
       ''ConstructorBody,
       ''InterfaceDecl,
       ''BlockStmt,
       ''Modifier,
       ''LockProperties,
       ''ClassDecl,
       ''TypeParam,
       ''VarDecl,
       ''InterfaceBody,
       ''VarDeclId,
       ''ExplConstrInv,
       ''Stmt,
       ''ImportDecl,
       ''EnumConstant, ''ForInit, ''SwitchBlock, ''Catch,
       ''SwitchLabel, ''EnumBody])

