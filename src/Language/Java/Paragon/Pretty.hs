{-# LANGUAGE TupleSections #-}
module Language.Java.Paragon.Pretty
    (
     prettyPrint, Pretty(..),
     opt,
     module Text.PrettyPrint
    ) where

import Text.PrettyPrint
import Data.Char (toLower)
import Control.Arrow (first)
import Prelude hiding ((<>))

import Language.Java.Paragon.Syntax

import qualified Data.ByteString.Char8 as B


prettyPrint :: Pretty a => a -> String
prettyPrint = show . pretty

class Pretty a where
  pretty :: a -> Doc
  pretty = prettyPrec 0

  prettyPrec :: Int -> a -> Doc
  prettyPrec _ = pretty

instance Pretty a => Pretty [a] where
  pretty as = brackets $ hcat (punctuate (char ',') $ map pretty as)

instance Pretty B.ByteString where
  pretty bs = text (B.unpack bs)

-----------------------------------------------------------------------
-- Packages

instance Pretty (CompilationUnit a) where
  pretty (CompilationUnit _ mpd ids tds) =
    vcat $ maybePP mpd: map pretty ids ++ map pretty tds

instance Pretty (PackageDecl a) where
  pretty (PackageDecl _ name) = text "package" <+> pretty name <> semi

instance Pretty (ImportDecl a) where
--  pretty (ImportDecl _ st name wc) =
--    text "import" <+> opt st (text "static")
--                  <+> pretty name <> opt wc (text ".*")
--                  <> semi

  pretty imp =
      let (st, name, mId, dem) = aux imp
      in text "import" <+> opt st (text "static")
             <+> pretty name
             <> maybe empty (\i -> char '.' <> pretty i) mId
             <> opt dem (text ".*")
             <> semi

    where aux (SingleTypeImport     _ n)   = (False, n, Nothing, False)
          aux (TypeImportOnDemand   _ n)   = (False, n, Nothing, True )
          aux (SingleStaticImport   _ n i) = (True,  n, Just i,  False)
          aux (StaticImportOnDemand _ n)   = (True,  n, Nothing, True )


-----------------------------------------------------------------------
-- Declarations

instance Pretty (TypeDecl a) where
  pretty (ClassTypeDecl     _ cdecl) = pretty cdecl
  pretty (InterfaceTypeDecl _ idecl) = pretty idecl

instance Pretty (ClassDecl a) where
  pretty (EnumDecl _ mods ident impls body) =
    hsep [hsep (map pretty mods)
          , text "enum"
          , pretty ident
          , ppImplements impls
         ] $$ pretty body

  pretty (ClassDecl _ mods ident tParams mSuper impls body) =
    hsep [hsep (map pretty mods)
          , text "class"
          , pretty ident
          , ppTypeParams tParams
          , ppExtends (maybe [] return mSuper)
          , ppImplements impls
         ] $$ pretty body

instance Pretty (ClassBody a) where
  pretty (ClassBody _ ds) =
    braceBlock (map pretty ds)

instance Pretty (EnumBody a) where
  pretty (EnumBody _ cs ds) =
    braceBlock $
        punctuate comma (map pretty cs) ++
        opt (not $ null ds) semi : map pretty ds

instance Pretty (EnumConstant a) where
  pretty (EnumConstant _ ident args mBody) =
    pretty ident
        -- needs special treatment since even the parens are optional
        <> opt (not $ null args) (ppArgs args)
      $$ maybePP mBody

instance Pretty (InterfaceDecl a) where
  pretty (InterfaceDecl _ mods ident tParams impls body) =
    hsep [hsep (map pretty mods)
          , text "interface"
          , pretty ident
          , ppTypeParams tParams
          , ppImplements impls
         ] $$ pretty body

instance Pretty (InterfaceBody a) where
  pretty (InterfaceBody _ mds) =
    braceBlock (map pretty mds)

instance Pretty (Decl a) where
  pretty (MemberDecl _ md) = pretty md
  pretty (InitDecl _ b bl) =
    opt b (text "static") <+> pretty bl

instance Pretty (MemberDecl a) where
  pretty (FieldDecl _ mods t vds) =
    hsep (map pretty mods ++ pretty t:map pretty vds) <> semi

  pretty (MethodDecl _ mods tParams ret ident fParams throws body) =
    hsep [hsep (map pretty mods)
          , ppTypeParams tParams
          , pretty ret
          , pretty ident <> ppArgs fParams
          , ppThrows throws
         ] $$ pretty body

  pretty (ConstructorDecl _ mods tParams ident fParams throws body) =
    hsep [hsep (map pretty mods)
          , ppTypeParams tParams
          , pretty ident
          , ppArgs fParams
          , ppThrows throws
         ] $$ pretty body

  pretty (MemberClassDecl     _ cdecl) = pretty cdecl
  pretty (MemberInterfaceDecl _ idecl) = pretty idecl

-- Paragon
  pretty (LockDecl _ mods ident arity lockProps) =
    hsep [hsep (map pretty mods)
          , text "lock"
          , pretty ident <> ppArity arity
         ] <> maybe empty (\lp -> char ' ' <> pretty lp) lockProps <> semi

ppArity :: [RefType x] -> Doc
ppArity [] = empty
ppArity mis = parens $ hsep $ punctuate comma $ map pretty mis

instance Pretty (VarDecl a) where
  pretty (VarDecl _ vdId mInitz) =
    pretty vdId
        <+> maybe empty (\initz -> char '=' <+> pretty initz) mInitz

instance Pretty (VarDeclId a) where
  pretty (VarId _ ident) = pretty ident
  pretty (VarDeclArray _ vId) = pretty vId

instance Pretty (VarInit a) where
  pretty (InitExp   _ e)       = pretty e
  pretty (InitArray _ arrInit) = pretty arrInit

instance Pretty (FormalParam a) where
  pretty (FormalParam _ mods t b vId) =
    hsep [hsep (map pretty mods)
          , pretty t <> opt b (text "...")
          , pretty vId
         ]

instance Pretty (MethodBody a) where
  pretty (MethodBody _ mBlock) = maybe semi pretty mBlock

instance Pretty (ConstructorBody a) where
  pretty (ConstructorBody _ mECI stmts) =
    braceBlock $ maybePP mECI : map pretty stmts

instance Pretty (ExplConstrInv a) where
  pretty (ThisInvoke _ rts args) =
    ppTypeParams rts <+> text "this" <> ppArgs args <> semi
  pretty (SuperInvoke _ rts args) =
    ppTypeParams rts <+> text "super" <> ppArgs args <> semi
  pretty (PrimarySuperInvoke _ e rts args) =
    pretty e <> char '.' <>
      ppTypeParams rts <+> text "super" <> ppArgs args <> semi

instance Pretty (Modifier a) where
  pretty m = case m of
                 Reads   _ pol   -> char '?' <> pretty pol
                 Writes  _ pol   -> char '!' <> pretty pol
                 Expects _ locks -> char '~' <> prettyLocks locks
                 Opens   _ locks -> char '+' <> prettyLocks locks
                 Closes  _ locks -> char '-' <> prettyLocks locks

                 Typemethod _ -> text "typemethod"
                 Reflexive  _ -> text "reflexive"
                 Transitive _ -> text "transitive"
                 Symmetric  _ -> text "symmetric"
                 Readonly   _ -> text "readonly"
                 Notnull    _ -> text "notnull"

                 Public    _ -> text "public"
                 Private   _ -> text "private"
                 Protected _ -> text "protected"
                 Abstract  _ -> text "abstract"
                 Final     _ -> text "final"
                 Static    _ -> text "static"
                 StrictFP  _ -> text "strictfp"
                 Transient _ -> text "transient"
                 Volatile  _ -> text "volatile"
                 Native    _ -> text "native"


-----------------------------------------------------------------------
-- Statements


instance Pretty (Block a) where
  pretty (Block _ stmts) = braceBlock $ map pretty stmts

instance Pretty (BlockStmt a) where
  pretty (BlockStmt _ stmt) = pretty stmt
  pretty (LocalClass _ cd) = pretty cd
  pretty (LocalVars _ mods t vds) =
    hsep (map pretty mods) <+> pretty t <+>
      hsep (punctuate comma $ map pretty vds) <> semi

-- Paragon
  pretty (LocalLock _ mods ident arity lockProps) =
    hsep [hsep (map pretty mods)
          , text "lock"
          , pretty ident <> ppArity arity
         ] <> maybe empty (\lp -> char ' ' <> pretty lp) lockProps <> semi

{-  pretty (LocalPolicy mods ident pol) =
    hsep [hsep (map pretty mods)
          , text "policy"
          , pretty ident
          , char '='
          , pretty pol
         ] <> semi

  pretty (LocalActor mods ident mInit) =
    hsep [hsep (map pretty mods)
          , text "actor"
          , pretty ident
          , maybe empty (\init -> char '=' <+> pretty init) mInit
         ] <> semi -}

instance Pretty (Stmt a) where
  pretty (StmtBlock _ block) = pretty block
  pretty (IfThen _ c th) =
    hsep [text "if", parens (pretty c)] $$ pretty th


  pretty (IfThenElse _ c th el) =
    hsep [text "if", parens (pretty c)]
    $$ pretty th $$ text "else" $$ pretty el


  pretty (While _ c stmt) =
    hsep [text "while", parens (pretty c), pretty stmt]

  pretty (BasicFor _ mInit mE mUp stmt) =
    hsep [text "for"
          , parens $ hsep [maybePP mInit, semi
                           , maybePP mE, semi
                           , maybe empty (hsep . punctuate comma . map pretty) mUp
                          ]] $$ pretty stmt

  pretty (EnhancedFor _ mods t ident e stmt) =
    hsep [text "for"
          , parens $ hsep [
                  hsep (map pretty mods)
                , pretty t
                , pretty ident
                , colon
                , pretty e
               ]] $$ pretty stmt

  pretty (Empty _) = semi

  pretty (ExpStmt _ e) = pretty e <> semi

  pretty (Assert _ ass mE) =
    text "assert" <+> pretty ass
      <+> maybe empty ((colon <>) . pretty) mE <> semi

  pretty (Switch _ e sBlocks) =
    text "switch" <+> parens (pretty e)
      $$ braceBlock (map pretty sBlocks)

  pretty (Do _ stmt e) =
    hsep [text "do", pretty stmt, text "while"
          , parens (pretty e)] <> semi

  pretty (Break _ mIdent) =
    text "break" <+> maybePP mIdent <> semi

  pretty (Continue _ mIdent) =
    text "continue" <+> maybePP mIdent <> semi

  pretty (Return _ mE) =
    text "return" <+> maybePP mE <> semi

  pretty (Synchronized _ e block) =
    text "synchronized" <+> parens (pretty e) $$ pretty block

  pretty (Throw _ e) =
    text "throw" <+> pretty e <> semi

  pretty (Try _ block catches mFinally) =
    text "try" $$ pretty block $$
      vcat (map pretty catches ++ [ppFinally mFinally])
   where ppFinally Nothing = empty
         ppFinally (Just bl) = text "finally" <+> pretty bl

  pretty (Labeled _ ident stmt) =
    pretty ident <> colon <+> pretty stmt

-- Paragon
  pretty (Open  _ lock) = text "open"  <+> pretty lock <> semi
  pretty (Close _ lock) = text "close" <+> pretty lock <> semi

  pretty (OpenBlock  _ lock block) = text "open"  <+> pretty lock <+> pretty block
  pretty (CloseBlock _ lock block) = text "close" <+> pretty lock <+> pretty block


{-  pretty (WhenThen lock th) =
    hsep [text "when", parens (pretty lock)
          ,text "then", pretty th
         ]
  pretty (WhenThenElse lock th el) =
    hsep [text "when", parens (pretty lock)
          , text "then", pretty th
          , text "else", pretty el
         ]
-}

instance Pretty (Catch a) where
  pretty (Catch _ fParam block) =
    hsep [text "catch", parens (pretty fParam)] $$ pretty block

instance Pretty (SwitchBlock a) where
  pretty (SwitchBlock _ lbl stmts) =
    vcat (pretty lbl : map (nest 2 . pretty) stmts)

instance Pretty (SwitchLabel a) where
  pretty (SwitchCase _ e) =
    text "case" <+> pretty e <> colon
  pretty (Default _) = text "default:"

instance Pretty (ForInit a) where
  pretty (ForLocalVars _ mods t vds) =
    hsep $ map pretty mods ++
            pretty t: punctuate comma (map pretty vds)
  pretty (ForInitExps _ es) = hsep $ punctuate comma $ map pretty es


-----------------------------------------------------------------------
-- Expressions

instance Pretty (Exp a) where
  pretty (Lit _ l) = pretty l

  pretty (ClassLit _ mT) =
    maybe (text "void") pretty mT <> text ".class"

  pretty (This _) = text "this"

  pretty (ThisClass _ name) =
    pretty name <> text ".this"

  pretty (Paren _ e) = parens (pretty e)

  pretty (InstanceCreation _ tArgs ct args mBody) =
    hsep [text "new"
          , ppTypeParams tArgs
          , pretty ct <> ppArgs args
         ] $$ maybePP mBody

  pretty (QualInstanceCreation _ e tArgs ident args mBody) =
    hsep [pretty e <> char '.' <> text "new"
          , ppTypeParams tArgs
          , pretty ident <> ppArgs args
         ] $$ maybePP mBody

  pretty (ArrayCreate _ t eps ps) =
    text "new" <+>
         hcat (pretty t :
                      map ppArrayDim
                              (map (first Just) eps ++
                               map (Nothing,) ps))
--      hcat (pretty t : map (brackets . pretty) es
--                ++ replicate k (text "[]"))

  pretty (ArrayCreateInit _ t ps ainit) =
    text "new"
        <+> hcat (pretty t : map (ppArrayDim . (Nothing,)) ps)
        <+> pretty ainit

  pretty (FieldAccess _ fa) = pretty fa

  pretty (MethodInv _ mi) = pretty mi

  pretty (ArrayAccess _ ain) = pretty ain

  pretty (ExpName _ name) = pretty name

  pretty (PostIncrement _ e) = pretty e <> text "++"

  pretty (PostDecrement _ e) = pretty e <> text "--"

  pretty (PreIncrement _ e)  = text "++" <> pretty e

  pretty (PreDecrement _ e)  = text "--" <> pretty e

  pretty (PrePlus _ e) = char '+' <> pretty e

  pretty (PreMinus _ e) = char '-' <> pretty e

  pretty (PreBitCompl _ e) = char '~' <> pretty e

  pretty (PreNot _ e) = char '!' <> pretty e

  pretty (Cast _ t e) = parens (pretty t) <+> pretty e

  pretty (BinOp _ e1 op e2) =
    hsep [pretty e1, pretty op, pretty e2]

  pretty (InstanceOf _ e rt) =
    hsep [pretty e, text "instanceof", pretty rt]

  pretty (Cond _ c th el) =
    hsep [pretty c, char '?', pretty th, colon, pretty el]

  pretty (Assign _ lhs aop e) =
    hsep [pretty lhs, pretty aop, pretty e]

-- Paragon
  pretty (PolicyExp _ pl) = pretty pl

--  pretty (PolicyOf i) = text "policyof" <> parens (pretty i)

  pretty (LockExp _ l) = char '?' <> pretty l

  pretty (AntiQExp _ s) = text "#E#" <> text s

instance Pretty (Literal a) where
  pretty (Int     _ i) = text (show i)
  pretty (Word    _ i) = text (show i) <> char 'L'
  pretty (Float   _ f) = text (show f) <> char 'F'
  pretty (Double  _ d) = text (show d)
  pretty (Boolean _ b) = text . map toLower $ show b
  pretty (Char    _ c) = text (show c)
  pretty (String  _ s) = text (show s)
  pretty (Null    _  ) = text "null"

instance Pretty (Op a) where
  pretty op = text $ case op of
    Mult    _ -> "*"
    Div     _ -> "/"
    Rem     _ -> "%"
    Add     _ -> "+"
    Sub     _ -> "-"
    LShift  _ -> "<<"
    RShift  _ -> ">>"
    RRShift _ -> ">>>"
    LThan   _ -> "<"
    GThan   _ -> ">"
    LThanE  _ -> "<="
    GThanE  _ -> ">="
    Equal   _ -> "=="
    NotEq   _ -> "!="
    And     _ -> "&"
    Xor     _ -> "^"
    Or      _ -> "|"
    CAnd    _ -> "&&"
    COr     _ -> "||"

instance Pretty (AssignOp a) where
  pretty aop = text $ case aop of
    EqualA   _ -> "="
    MultA    _ -> "*="
    DivA     _ -> "/="
    RemA     _ -> "%="
    AddA     _ -> "+="
    SubA     _ -> "-="
    LShiftA  _ -> "<<="
    RShiftA  _ -> ">>="
    RRShiftA _ -> ">>>="
    AndA     _ -> "&="
    XorA     _ -> "^="
    OrA      _ -> "|="

instance Pretty (Lhs a) where
  pretty (NameLhs  _ name) = pretty name
  pretty (FieldLhs _ fa)   = pretty fa
  pretty (ArrayLhs _ ain)  = pretty ain

instance Pretty (ArrayIndex a) where
  pretty (ArrayIndex _ ref e) = pretty ref <> brackets (pretty e)

instance Pretty (FieldAccess a) where
  pretty (PrimaryFieldAccess _ e ident) =
    pretty e <> char '.' <> pretty ident
  pretty (SuperFieldAccess _ ident) =
    text "super." <> pretty ident
  pretty (ClassFieldAccess _ name ident) =
    pretty name <> text ".super." <> pretty ident

instance Pretty (MethodInvocation a) where
  pretty (MethodCallOrLockQuery _ name args) =
    pretty name <> ppArgs args

  pretty (PrimaryMethodCall _ e tArgs ident args) =
    hcat [pretty e, char '.', ppTypeParams tArgs,
           pretty ident, ppArgs args]

  pretty (SuperMethodCall _ tArgs ident args) =
    hcat [text "super.", ppTypeParams tArgs,
           pretty ident, ppArgs args]

  pretty (ClassMethodCall _ name tArgs ident args) =
    hcat [pretty name, text ".super.", ppTypeParams tArgs,
           pretty ident, ppArgs args]

  pretty (TypeMethodCall _ name tArgs ident args) =
    hcat [pretty name, char '.', ppTypeParams tArgs,
           pretty ident, ppArgs args]

instance Pretty (ArrayInit a) where
  pretty (ArrayInit _ vInits) =
    braces $ hsep (punctuate comma (map pretty vInits))


ppArgs :: Pretty a => [a] -> Doc
ppArgs = parens . hsep . punctuate comma . map pretty

ppArrayDim :: (Maybe (Exp a), Maybe (Policy a)) -> Doc
ppArrayDim (mE, mP) =
    brackets (maybe empty pretty mE) <>
    maybe empty (angles . pretty) mP

-----------------------------------------------------------------------
-- Types

instance Pretty (Type a) where
  pretty (PrimType  _ pt) = pretty pt
  pretty (RefType   _ rt) = pretty rt
  pretty (AntiQType _ s)  = text "#T#" <> text s

instance Pretty (RefType a) where
  pretty (ClassRefType _ ct) = pretty ct
  pretty (TypeVariable _ i)  = pretty i
  pretty (ArrayType _ ty mPols) =
      pretty ty <> hcat ((flip map) mPols
                     (\mP -> brackets empty <> maybe empty (angles . pretty) mP))

instance Pretty (ClassType a) where
  pretty (ClassType _ n tas) =
    pretty n <> ppTypeParams tas
--    hcat . punctuate (char '.') $
--      map (\(i,tas) -> pretty i <> ppTypeParams tas) itas

instance Pretty (TypeArgument a) where
  pretty (ActualArg _ aa) = pretty aa
  pretty (Wildcard _ mBound) = char '?' <+> maybePP mBound

instance Pretty (NonWildTypeArgument a) where
  pretty (ActualName   _ n) = pretty n
  pretty (ActualType   _ t) = pretty t
  pretty (ActualExp _ e) = pretty e
  pretty (ActualLockState _ ls) = {- text "lock[]" <+> -} ppArgs ls -- HACK ALERT

instance Pretty (WildcardBound a) where
  pretty (ExtendsBound _ rt) = text "extends" <+> pretty rt
  pretty (SuperBound   _ rt) = text "super"   <+> pretty rt

instance Pretty (PrimType a) where
  pretty (BooleanT _) = text "boolean"
  pretty (ByteT    _) = text "byte"
  pretty (ShortT   _) = text "short"
  pretty (IntT     _) = text "int"
  pretty (LongT    _) = text "long"
  pretty (CharT    _) = text "char"
  pretty (FloatT   _) = text "float"
  pretty (DoubleT  _) = text "double"

  -- Paragon
  pretty (ActorT   _) = text "actor"
  pretty (PolicyT  _) = text "policy"

instance Pretty (TypeParam a) where
  pretty (TypeParam _ ident rts) =
    pretty ident
      <+> opt (not $ null rts)
           (hsep $ text "extends":
                    punctuate (text " &") (map pretty rts))
  pretty (ActorParam _ rt ident) =
      text "actor" <+> pretty rt <+> pretty ident
  pretty (PolicyParam _ ident) = text "policy" <+> pretty ident
  pretty (LockStateParam _ ident) = text "lock[]" <+> pretty ident

ppTypeParams :: Pretty a => [a] -> Doc
ppTypeParams [] = empty
ppTypeParams tps = angles $ hsep (punctuate comma (map pretty tps))

ppImplements :: [ClassType x] -> Doc
ppImplements [] = empty
ppImplements rts = text "implements"
    <+> hsep (punctuate comma (map pretty rts))

ppExtends :: [ClassType x] -> Doc
ppExtends [] = empty
ppExtends rts = text "extends"
    <+> hsep (punctuate comma (map pretty rts))

ppThrows :: [ExceptionSpec x] -> Doc
ppThrows [] = empty
ppThrows ess = text "throws"
    <+> hsep (punctuate comma (map pretty ess))

instance Pretty (ExceptionSpec a) where
  pretty (ExceptionSpec _ mods t) =
      hsep (map pretty mods) <+> pretty t

instance Pretty (ReturnType a) where
  pretty (VoidType _) = text "void"
  pretty (LockType _) = text "lock"
  pretty (Type _ ty ) = pretty ty

--ppResultType :: Maybe (Type x) -> Doc
--ppResultType Nothing = text "void"
--ppResultType (Just a) = pretty a

-----------------------------------------------------------------------
-- Paragon Policies

instance Pretty (PolicyExp a) where
  pretty (PolicyLit _ []) = braces (char ':')
  pretty (PolicyLit _ cs) = braces $ hcat (punctuate (char ';') $ map pretty cs)
  pretty (PolicyOf _ i) = text "policyof" <> parens (pretty i)
  pretty (PolicyThis _) = text "policyof" <> parens (text "this")
  pretty (PolicyTypeVar _ i) = pretty i

-- HERE
instance Pretty (Clause a) where
  pretty (Clause _ qs h b) =
      (if not (null qs)
       then parens $ hcat $ punctuate comma $ map pretty qs
       else empty) <+>
             pretty h <> char ':' <+>
             hcat (punctuate comma $ map pretty b)

instance Pretty (LClause a) where
  pretty (LClause _ qs h b) =
      parens (hcat $ punctuate comma $ map pretty qs) <+>
             pretty h <> char ':' <+>
             hcat (punctuate comma $ map pretty b)
  pretty (ConstraintClause _ qs b) =
      parens (hcat $ punctuate comma $ map pretty qs) <+>
             char '-' <> char ':' <+>
             hcat (punctuate comma $ map pretty b)

instance Pretty (ClauseVarDecl a) where
  pretty (ClauseVarDecl _ rt i) = pretty rt <+> pretty i

instance Pretty (ClauseHead a) where
  pretty (ClauseDeclHead _ cvd) = pretty cvd
  pretty (ClauseVarHead _ ca) = pretty ca

instance Pretty (Actor a) where
  pretty (Actor _ str) = pretty str
  pretty (Var   _ str) = pretty str

instance Pretty (ActorName a) where
  pretty (ActorName    _ n) = pretty n
  pretty (ActorTypeVar _ _rt i) = pretty i

instance Pretty (Atom a) where
  pretty (Atom _ pr vs) = pretty pr <>
    opt (not $ null vs) (parens (hcat (punctuate (char ',') $ map pretty vs)))

instance Pretty (Lock a) where
  pretty (Lock _ i as) = pretty i <>
    opt (not $ null as) (parens (hcat (punctuate (char ',') $ map pretty as)))
  pretty (LockVar _ i) = pretty i

instance Pretty (LockProperties a) where
  pretty (LockProperties _ cs) = braces $ hcat (punctuate (char ';') $ map pretty cs)

prettyLocks :: [Lock x] -> Doc
--prettyLocks [l] = pretty l
prettyLocks ls  = parens . hsep . punctuate (char ',') $ map pretty ls

--instance Pretty (LockExp a) where
--  pretty (LockExp ls) = parens $ hcat (map pretty ls)
--  pretty (LockVar v)  = pretty v

-----------------------------------------------------------------------
-- Names and identifiers

instance Pretty (Name a) where
  pretty (Name _ _ mPrefix i) =
      maybe empty (\pre -> pretty pre <> char '.') mPrefix
                <> pretty i
  pretty (AntiQName _ s) = text "#N#" <> text s

instance Pretty NameType where
  pretty EName = text "expression name"
  pretty TName = text "type name"
  pretty PName = text "package name"
  pretty LName = text "lock name"
  pretty MName = text "method name"
  pretty POrTName = text "package or type name"
  pretty MOrLName = text "method or lock name"
  pretty EOrLName = text "expression or lock name"
  pretty AmbName = text "name"

{-
instance Pretty (Name a) where
  pretty (Name _ is) =
    hcat (punctuate (char '.') $ map pretty is)
  pretty (AntiQName _ s) = text "#N#" <> text s
  pretty n = pretty (flattenName n)

flattenName :: Name a -> Name a
flattenName n@(Name{}) = n
flattenName n@(AntiQName{}) = n
flattenName n =
    let is = reverse $ flName n
    in case is of
         i:_ -> Name (ann i) is
         [] -> panic "flattenName" "empty name"

  where flName :: Name a -> [Ident a]
        flName (EName _ mPre i) = i : maybe [] flName mPre
        flName (MName _ mPre i) = i : maybe [] flName mPre
        flName (TName _ mPre i) = i : maybe [] flName mPre
        flName (PName _ mPre i) = i : maybe [] flName mPre
        flName (LName _ mPre i) = i : maybe [] flName mPre
        flName (POrTName _ mPre i) = i : maybe [] flName mPre
        flName (MOrLName _ mPre i) = i : maybe [] flName mPre
        flName _ = panic "flattenName" ("Malformed name in parser")
-}
instance Pretty (Ident a) where
  pretty (Ident _ s) = text $ B.unpack s
  pretty (AntiQIdent _ s) = text "#" <> text s

-----------------------------------------------------------------------
-- Help functionality

maybePP :: Pretty a => Maybe a -> Doc
maybePP = maybe empty pretty

opt :: Bool -> Doc -> Doc
opt x a = if x then a else empty

braceBlock :: [Doc] -> Doc
braceBlock xs = char '{'
    $+$ nest 2 (vcat xs)
    $+$ char '}'

angles :: Doc -> Doc
angles d = char '<' <> d <> char '>'
