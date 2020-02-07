{-# LANGUAGE DeriveDataTypeable, FlexibleInstances, FlexibleContexts #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}
module Language.Java.Paragon.TypeCheck.TypeMap where

import Language.Java.Paragon.Syntax
import Language.Java.Paragon.Pretty
import Language.Java.Paragon.Interaction
import Language.Java.Paragon.SourcePos

import Language.Java.Paragon.PolicyLang

import Language.Java.Paragon.TypeCheck.Types

import qualified Data.Map as Map
import Data.List (intersperse)
import Data.Generics.Uniplate.Data
import qualified Data.ByteString.Char8 as B

import Data.Data

typeMapModule :: String
typeMapModule = typeCheckerBase ++ ".TypeMap"


data VarFieldSig = VSig {
      varType   :: TcType,
      varPol    :: ActorPolicy,
      varParam  :: Bool,
      varStatic :: Bool,
      varFinal  :: Bool,
      varNotnull:: Bool
    }
  deriving (Show, Data, Typeable)

data MethodSig = MSig {
      mRetType   :: TcType,
      mModifiers :: [Modifier ()],
      mRetPol    :: ActorPolicy,
      mPars      :: [B.ByteString],
      mParBounds :: [ActorPolicy],
      mWrites    :: ActorPolicy,
      mExpects   :: [TcLock],
      mLMods     :: TcLockDelta,
      mExns      :: [(TcType, ExnSig)],
      mNNPars    :: [B.ByteString],
      mIsNative  :: Bool
    }
  deriving (Show, Data, Typeable)

data ExnSig = ExnSig {
      exnReads :: ActorPolicy,
      exnWrites :: ActorPolicy,
      exnMods :: TcLockDelta -- ([TcLock],[TcLock])
    }
  deriving (Show, Data, Typeable)

data ConstrSig = CSig {
      cPars      :: [B.ByteString],
      cParBounds :: [ActorPolicy],
      cWrites    :: ActorPolicy,
      cExpects   :: [TcLock],
      cLMods     :: TcLockDelta,
      cExns      :: [(TcType, ExnSig)],
      cNNPars    :: [B.ByteString],
      cIsNative  :: Bool
    }
  deriving (Show, Data, Typeable)

data LockSig = LSig {
      lPol     :: ActorPolicy,
      -- lArity   :: Int,
      lArgs    :: [TcRefType],
      lProps   :: GlobalPol
    }
  deriving (Show, Data, Typeable)

data TypeSig = TSig {
      tType       :: TcRefType,
      tIsClass    :: Bool,
      tIsFinal    :: Bool,
      tSupers     :: [TcClassType],
      tImpls      :: [TcClassType],
      tMembers    :: TypeMap
    }
  deriving (Show, Data, Typeable)


type Map = Map.Map

type MethodMap = Map ([TypeParam SourcePos], [TcType], Bool) MethodSig
type ConstrMap = Map ([TypeParam SourcePos], [TcType], Bool) ConstrSig

data TypeMap = TypeMap {
      -- signatures
      fields      :: Map B.ByteString VarFieldSig,
      methods     :: Map B.ByteString MethodMap,
      constrs     :: ConstrMap,
      locks       :: Map B.ByteString LockSig,
      -- known policy-level entities
      policies    :: Map B.ByteString PrgPolicy,
      actors      :: Map B.ByteString TypedActorIdSpec,
      -- typemethod eval info
      typemethods :: Map B.ByteString ([B.ByteString], Block SourcePos),
      -- types and packages
      types       :: Map B.ByteString ([TypeParam SourcePos], [(RefType SourcePos, B.ByteString)], TypeSig),
      packages    :: Map B.ByteString TypeMap
    }
  deriving (Show, Data, Typeable)

emptyTM :: TypeMap
emptyTM = TypeMap {
                fields      = Map.empty,
                methods     = Map.empty,
                constrs     = Map.empty,
                locks       = Map.empty,
                policies    = Map.empty,
                actors      = Map.empty,
                typemethods = Map.empty,
                types       = Map.empty,
                packages    = Map.empty
              }

hardCodedArrayTM :: TcType -> ActorPolicy -> TypeSig
hardCodedArrayTM ty p =
    let memTM = emptyTM {
                  fields = Map.fromList [(B.pack "length", VSig intT (VarPolicy thisP) False False True False)]
                , methods = Map.fromList [] -- TODO
                }
    in TSig {
             tType = TcArrayT ty p,
             tIsClass = False,
             tIsFinal = False,
             tSupers  = [], -- TODO: what's the super type of an array?
             tImpls   = [], -- TODO: Iterable etc
             tMembers = memTM
           }

clearToPkgs :: TypeMap -> TypeMap
clearToPkgs tm = emptyTM { packages = packages tm }

clearToTypes :: TypeMap -> TypeMap
clearToTypes tm = emptyTM { packages = packages tm, types = types tm }

pkgsAndTypes :: TypeMap -> Map B.ByteString TypeMap
pkgsAndTypes tm = Map.union (packages tm)
                    -- disregard type parameters
                    (Map.map (tMembers . (\(_,_,x) -> x)) $ types tm)


merge :: TypeMap -> TypeMap -> TypeMap
merge tm1 tm2 = TypeMap {
                  fields      = Map.union (fields      tm1) (fields      tm2),
                  methods     = Map.union (methods     tm1) (methods     tm2),
                  constrs     = Map.union (constrs     tm1) (constrs     tm2),
                  locks       = Map.union (locks       tm1) (locks       tm2),
                  policies    = Map.union (policies    tm1) (policies    tm2),
                  actors      = Map.union (actors      tm1) (actors      tm2),
                  typemethods = Map.union (typemethods tm1) (typemethods tm2),
                  types       = Map.union (types       tm1) (types       tm2),
                  packages    = Map.union (packages    tm1) (packages    tm2)
                }

--------------------------------------------
--       Working with extensions          --
--------------------------------------------

extendTypeMapP :: Name a -> TypeMap -> TypeMap -> TypeMap
extendTypeMapP = go . map unIdent . flattenName
  where
    go :: [B.ByteString] -> TypeMap -> TypeMap -> TypeMap
    go [] _ _ = panic (typeMapModule ++ ".extendTypeMapP") "Empty ident list"
    go [i] leafTm tm =
        tm { packages = Map.insert i leafTm (packages tm) }
    go (i:is) leafTm tm =
        let mTm = packages tm
            eTm = case Map.lookup i mTm of
                    Just innerTm -> innerTm
                    Nothing -> emptyTM
            newTm = go is leafTm eTm
        in tm { packages = Map.insert i newTm mTm }

extendTypeMapT :: Name SourcePos
               -> [TypeParam SourcePos]
               -> [(RefType SourcePos, B.ByteString)]
               -> TypeSig
               -> TypeMap
               -> TypeMap
extendTypeMapT = go . map unIdent . flattenName
  where
    go :: [B.ByteString]
       -> [TypeParam SourcePos]
       -> [(RefType SourcePos, B.ByteString)]
       -> TypeSig -> TypeMap -> TypeMap
    go [] _ _ _ _ = panic (typeMapModule ++ ".extendTypeMapT")
                    "Empty ident list"
    go [i] tps iaps tSig tm =
        tm { types = Map.insert i (tps,iaps,tSig) (types tm) }
    go (i:is) tps iaps tSig tm =
        let mTm = packages tm
            eTm = case Map.lookup i mTm of
                    Just innerTm -> innerTm
                    Nothing -> emptyTM
            newTm = go is tps iaps tSig eTm
        in tm { packages = Map.insert i newTm mTm }

extendTypeMapN :: Name SourcePos -> (TypeMap -> TypeMap) -> TypeMap -> TypeMap
extendTypeMapN = go . map unIdent . flattenName
  where
    go :: [B.ByteString] -> (TypeMap -> TypeMap) -> TypeMap -> TypeMap
    go [] _ _ = panic (typeMapModule ++ ".extendTypeMapN")
                "Empty ident list"
    go [i] tmf tm =
        let mTm = types tm
            (tps,iaps,tSig) = case Map.lookup i mTm of
                                Just tyInfo -> tyInfo
                                Nothing -> panic (typeMapModule ++ ".extendTypeMapN") $
                                           "Type not yet initialized: " ++ prettyPrint i
            tTm = tMembers tSig
            newSig = tSig { tMembers = tmf tTm }
        in tm { types = Map.insert i (tps,iaps,newSig) mTm }

    go (i:is) tmf tm =
        let mTm = packages tm
            eTm = case Map.lookup i mTm of
                    Just innerTm -> innerTm
                    Nothing -> panic (typeMapModule ++ ".extendTypeMapN") $
                               "Package not yet initialized: " ++ prettyPrint i
            newTm = go is tmf eTm
        in tm { packages = Map.insert i newTm mTm }

--------------------------------------
--    Working with the lookups      --
--------------------------------------

-- TODO: This is an anomaly!!!
lookupNamed :: (TypeMap -> Map B.ByteString a) -> Name SourcePos -> TypeMap -> Maybe a
lookupNamed recf (Name _ _ Nothing i) tm = Map.lookup (unIdent i) (recf tm)
lookupNamed recf nam@(Name _ _ (Just pre) i) tm = do
    newTm <- case nameType pre of
               TName -> do
                 (_tps, _iaps, tsig) <- lookupNamed types pre tm
                 --if not (null tps)
                  --then Nothing
                  --else
                 return $ tMembers tsig
               PName -> lookupNamed packages pre tm
{-               EName -> do
                 vsig <- lookupNamed fields pre tm
                 case lookupTypeOfT (varType vsig) tm of
                   Left _ -> Nothing
                   Right newTm -> return newTm -}
               _ -> panic (typeMapModule ++ ".lookupNamed") $
                    "Prefix is not a package or type: " ++ show nam
    Map.lookup (unIdent i) $ recf newTm

lookupNamed _ _ _ = panic (typeMapModule ++ ".lookupNamed")
                    "AntiQName should not appear in AST being type-checked"


lookupTypeOfStateT :: TcStateType -> TypeMap -> Either (Maybe String) TypeSig
lookupTypeOfStateT (TcInstance (TcClsRefT (TcClassT n tas)) _ iaas _) startTm =
    case n of
      Name _ TName _ _ ->
          let mSig = lookupNamed types n startTm
          in case mSig of
               Nothing -> Left Nothing
               Just (tps, iaps, tsig)
                   -- TODO: Type argument inference
                   | length tps /= length tas -> Left $ Just $
                             "Wrong number of type arguments in class type.\n" ++
                             "Type " ++ prettyPrint n ++ " expects " ++ show (length tps) ++
                             " arguments but has been given " ++ show (length tas)
                   | length iaps /= length iaas -> panic (typeMapModule ++ ".lookupTypeOfStateT")
                                                   $ "Too few implicit arguments: " ++ show (iaps, iaas)
                   | otherwise -> let itps = map (\(rt,s) -> ActorParam defaultPos rt (Ident defaultPos s)) iaps
                                      itas = map TcActualActor iaas
                                  in Right $ instantiate (zip (tps++itps) (tas++itas)) tsig

      Name _ _ _ _ -> Left Nothing
      _ -> panic (typeMapModule ++ ".lookupTypeOfT") $ show n

lookupTypeOfStateT (TcType (TcRefT (TcClsRefT (TcClassT n _tas))) _) startTm =
    case n of
      Name _ TName _ _ ->
          let mSig = lookupNamed types n startTm
          in case mSig of
               Nothing -> Left Nothing
               Just (_tps, _iaps, tsig) -> Right tsig

      --Name _ _ _ _ -> Left Nothing
      _ -> panic (typeMapModule ++ ".lookupTypeOfT") $ show n

lookupTypeOfStateT (TcType t _) tm =
    case lookupTypeOfT t tm of
      Right (is, tsig) | null is -> Right tsig
                       | otherwise -> panic (typeMapModule ++ ".lookupTypeOfStateT")
                                      $ "Needs implicit actor arguments: " ++ show (t, is)
      Left err -> Left err

lookupTypeOfStateT _ _ = Left Nothing

-- | lookupTypeOfT will, given a type T and a top-level type environment,
--   return the type environment for T tagged with Right.
--   Left denotes an error, which wraps:
--   * If T is not a refType, return Nothing
--   * If T is given the wrong number of type arguments, return Just errorMessage.
lookupTypeOfT :: TcType -> TypeMap -> Either (Maybe String) ([(RefType SourcePos, B.ByteString)], TypeSig)
lookupTypeOfT (TcRefT refT) = lookupTypeOfRefT refT
lookupTypeOfT _ = const $ Left Nothing

lookupTypeOfRefT :: TcRefType -> TypeMap -> Either (Maybe String) ([(RefType SourcePos, B.ByteString)], TypeSig)
lookupTypeOfRefT (TcArrayT ty pol) _ = Right ([], hardCodedArrayTM ty pol)
lookupTypeOfRefT (TcTypeVar _ ) _ = panic (typeMapModule ++ ".lookupTypeOfRefT")
                                    "TcTypeVar should have been instantiated"
lookupTypeOfRefT TcNullT _ = Left $ Just "Cannot dereference null"
lookupTypeOfRefT _rt@(TcClsRefT (TcClassT n tas)) startTm =
    case n of
      Name _ TName _ _ ->
          let mSig = lookupNamed types n startTm
          in case mSig of
               Nothing -> Left Nothing
               Just (tps, iaps, tsig)
                   -- TODO: Type argument inference
                   | length tps /= length tas -> Left $ Just $
                             "Wrong number of type arguments in class type.\n" ++
                             "Type " ++ prettyPrint n ++ " expects " ++ show (length tps) ++
                             " arguments but has been given " ++ show (length tas)
--                   | not (null iaps) -> panic (typeMapModule ++ ".lookupTypeOfRefT")
--                                        $ "Too many implicit arguments: " ++ show iaps
                   | otherwise -> Right (iaps, instantiate (zip tps tas) tsig)

      Name _ _ _ _ -> Left Nothing
      _ -> panic (typeMapModule ++ ".lookupTypeOfRefT") $ show n

--------------------------------------
--   Type argument instantiation    --
--------------------------------------

instantiate :: Data a => [(TypeParam SourcePos,TcTypeArg)] -> a -> a
instantiate pas = transformBi instT
                     . transformBi instA
                     . transformBi instP
                     . transformBi instLs
    where instT :: TcRefType -> TcRefType
          instT tv@(TcTypeVar i) =
              case lookup i typs of
                Just rt -> rt
                Nothing -> tv
          instT rt = rt

          instA :: TypedActorIdSpec -> TypedActorIdSpec
          instA av@(TypedActorIdSpec rt (ActorTPVar i)) =
              case lookup i as of
                Just (TypedActorIdSpec _ aid) -> TypedActorIdSpec rt aid
                -- Here ^ we mask out any occurence of 'undefined' induced
                -- by skolemization.
                Nothing -> av
          instA a = a

          instP :: ActorPolicy -> ActorPolicy
          instP p = case p of
                      VarPolicy rp -> instRP rp
                      MetaJoin _p q -> MetaJoin (instP _p) (instP q) -- instP _p `lub` instP q
                      MetaMeet _p q -> MetaMeet (instP _p) (instP q) -- instP _p `glb` instP q
                      _ -> p
          instRP :: PrgPolicy -> ActorPolicy
          instRP rp = case rp of
                        PolicyVar (PolicyTypeParam i) ->
                            case lookup i ps of
                              Just p -> p
                              Nothing -> VarPolicy rp
                        Join p q -> let -- instRP p `lub` instRP q
                                  pNew = instRP p
                                  qNew = instRP q
                                  in case (pNew, qNew) of
                                       (VarPolicy vp, VarPolicy vq) -> VarPolicy (Join vp vq)
                                       _ -> MetaJoin pNew qNew
                        Meet p q -> let -- instRP p `glb` instRP q
                                  pNew = instRP p
                                  qNew = instRP q
                                  in case (pNew, qNew) of
                                       (VarPolicy vp, VarPolicy vq) -> VarPolicy (Meet vp vq)
                                       _ -> MetaMeet pNew qNew
                        _ -> VarPolicy rp

          instLs :: [LockSpec] -> [LockSpec]
          instLs = concatMap instL

          instL :: LockSpec -> [LockSpec]
          instL lv@(LockTypeParam i) =
              case lookup i locs of
                Just le -> le
                Nothing -> [lv]
          instL l = [l]

          typs = [ (unIdent i, rt) | (TypeParam    _ i _, TcActualType      rt) <- pas ]
          as   = [ (unIdent i, n ) | (ActorParam     _ _rt i, TcActualActor      n) <- pas ]
          ps   = [ (unIdent i, p ) | (PolicyParam    _ i, TcActualPolicy     p) <- pas ]
          locs = [ (unIdent i, ls) | (LockStateParam _ i, TcActualLockState ls) <- pas ]


--instThis :: (Functor  m, Data a) => ActorPolicy -> a -> m a
instThis ::  (Data from, HasSubTyping m, Lattice m ActorSetRep) =>
                           ActorPolicy -> from -> m from
instThis p = transformBiM instThisPol
  where --instThisPol :: ActorPolicy -> m ActorPolicy
        instThisPol = substVarInMetaPolicyM ThisVar p


-----------------------------------------------
-- Pretty
-- TODO is orphan
instance (Pretty k, Pretty v) => Pretty (Map.Map k v) where
  pretty mp = let as = Map.toList mp
              in myCat mp [ char '{',
                            nest 2 $ vcat $ map ppEntry as,
                            char '}'
                          ]
                  where ppEntry (k, v) = vcat [pretty k <+> text "-->",
                                               nest 2 $ pretty v]



instance Pretty VarFieldSig where
    pretty (VSig ty pol p st fin mnull) =
        vcat [text "VSig {",
              nest 2 $ vcat [text "varType: " <+> pretty ty,
                             text "varPol: " <+> pretty pol,
                             text "bools: " <+> text (show [p,st,fin,mnull])],
              char '}']

instance Pretty MethodSig where
    pretty (MSig retT _mods retP pars bs _w _exps _lms _xs _nnp _isN) = --text (show csig)
        vcat [text "MSig {",
              nest 2 $ vcat [text "mRetType: " <+> pretty retT,
                             text "mRetPol: " <+> pretty retP <+> text (show retP),
                             text "mPars: " <+> pretty pars,
                             text "mParBounds: " <+> pretty bs],
              char '}']

instance Pretty ExnSig where
    pretty esig = text (show esig)

instance Pretty ConstrSig where
    pretty (CSig pars bs _w _exps _lms _xs _nnp _isN) = --text (show csig)
        vcat [text "CSig {",
              nest 2 $ vcat [text "cPars: " <+> pretty pars,
                             text "cParBounds: " <+> pretty bs],

              char '}']

instance Pretty LockSig where
    pretty lsig = text (show lsig)

instance Pretty TypeSig where
    pretty (TSig ty cl fin sups impls mems) =
        vcat [text "TSig {",
              nest 2 $ vcat [text "tType: " <+> pretty ty,
                             text "tSupers: " <+>
                                  hcat (intersperse (text ", ") (map pretty sups)),
                             text "tImpls: " <+>
                                  hcat (intersperse (text ", ") (map pretty impls)),
                             text "bools: " <+> text (show [cl, fin]),
                             vcat [text "tMembers: ", pretty mems]],
              char '}']

instance Pretty ([TypeParam a], [TcType], Bool) where
    pretty (tps, tys, b) = hcat [char '(',
                                 pretty tps,
                                 char ',',
                                 pretty tys,
                                 char ',',
                                 text (show b),
                                 char ')']

instance Pretty ([B.ByteString], Block SourcePos) where
    pretty (pars, _body) = hcat [pretty pars, text "{ ... }"]

instance Pretty ([TypeParam SourcePos], [(RefType SourcePos, B.ByteString)], TypeSig) where
    pretty (tps, iaps, tsig) = vcat [ pretty tps <+> hcat (punctuate comma $ map ppIap iaps),
                                      pretty tsig ]
      where ppIap (rt,b) = pretty rt <+> pretty b

instance Pretty TypeMap where
    pretty tm = vcat [
                 text "TypeMap {",
                 nest 2 contents,
                 text "}"]

        where contents = vcat [
                          mapCat "fields =>" (fields tm),
                          mapCat "methods =>"     (methods tm),
                          mapCat "constrs =>"     (constrs tm),
                          mapCat "locks =>"       (locks tm),
                          mapCat "policies =>"    (policies tm),
                          mapCat "actors =>"      (actors tm),
                          mapCat "typemethods =>" (typemethods tm),
                          mapCat "types =>"       (types tm),
                          mapCat "packages =>"    (packages tm)]

mapCat :: (Pretty k, Pretty v) => String -> Map k v -> Doc
mapCat lbl mp = myCat mp [text lbl, nest 2 $ pretty mp]

myCat :: Map k v -> [Doc] -> Doc
myCat mp = if Map.size mp == 0 then hcat else vcat
