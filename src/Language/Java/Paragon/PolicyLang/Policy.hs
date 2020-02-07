{-# LANGUAGE CPP, DeriveDataTypeable, MultiParamTypeClasses, FlexibleInstances, UndecidableInstances #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}
module Language.Java.Paragon.PolicyLang.Policy (
  module Language.Java.Paragon.PolicyLang.Policy,
  HasSubTyping(..)
{-    (
     IsPolicy(..),
     bottom, top, thisP, joinWThis, isTop, isBottom,
     TcPolicy(..), PrgPolicy(..), PolicyBounds(..),
     TcClause(..), TcAtom(..), TcActor(..), TcMetaVar(..),
     {- toPolicyLit, -} {-toRecPolicy,-}
     lockToAtom, specialConstraintAtom,
     {-zonkPolicy,-} substPolicy, firstRigid, substThis,
     flowAtomString,

     ActorPolicy, AtomPolicy, ActorPolicyBounds
    ) -} ) where

--import Language.Java.Paragon.Syntax (Name)
import Language.Java.Paragon.Pretty
import Language.Java.Paragon.TypeCheck.Types
--import Language.Java.Paragon.Error()
--import Language.Java.Paragon.SourcePos
import Language.Java.Paragon.PolicyLang.Actors


import Security.InfoFlow.Policy.FlowLocks

--import Language.Java.Paragon.TypeCheck.Actors
--import Language.Java.Paragon.TypeCheck.Locks

import Control.Applicative
import qualified Data.ByteString.Char8 as B
--import Data.List ( (\\) {-, groupBy, nub-}  )
--import Data.Maybe

#ifdef BASE4
import Data.Data
#else
import Data.Generics (Data(..),Typeable(..))
#endif

import Prelude hiding ((<>))

--flowAtomString :: String
--flowAtomString = "$FLOW$"

--policyModule :: String
--policyModule = typeCheckerBase ++ ".Policy"

---------------------------------------------------------------
-- Basic policies
{-
data TcPolicy a = RealPolicy (PrgPolicy a)
                | Join (TcPolicy a) (TcPolicy a)
                | Meet (TcPolicy a) (TcPolicy a)
                | VarPolicy (TcMetaVar a)
  deriving (Eq, Ord, Show, Data, Typeable)

data PrgPolicy a = TcPolicy [TcClause a]
                 | TcRigidVar Bool B.ByteString
                 | TcThis
                 | TcJoin (PrgPolicy a) (PrgPolicy a)
                 | TcMeet (PrgPolicy a) (PrgPolicy a)
  deriving (Eq,Ord,Show,Data,Typeable)
-}

{-- TODO: This should go into the analysis instead,
-- leaving this module all but pointless.
data PolicyBounds a
    = KnownPolicy (TcPolicy a)
    -- | Invariant: For 'PolicyBounds p q', p <= q
    | PolicyBounds (TcPolicy a) (TcPolicy a)
  deriving (Eq, Ord, Show, Data, Typeable)
-}
{-- | Policies used in Paragon to label sources and sinks describe information
-- flows to actors, as opposed to the 'Global Policy' that describes lock
-- properties, see @AtomPolicy@
type ActorPolicy = TcPolicy TcActor
type ActorPolicyBounds = PolicyBounds TcActor

type AtomPolicy = TcPolicy TcAtom
-}
data MetaVarRep = MetaVarRep Int B.ByteString
  deriving (Data, Typeable, Eq, Ord, Show)

data PolicyVarRep
    = ThisVar
    | PolicyTypeParam B.ByteString
    | PolicyOfVar B.ByteString
  deriving (Data, Typeable, Eq, Ord, Show)


data ActorSetRep
    = TypedActor TcRefType B.ByteString
    | SingletonActor TypedActorIdSpec
    | NoActor
  deriving (Ord, Show, Data, Typeable)

instance Eq ActorSetRep where
  TypedActor rt1 _ == TypedActor rt2 _ = rt1 == rt2
  SingletonActor aid1 == SingletonActor aid2 = aid1 == aid2
  NoActor == NoActor = True
  _ == _ = False

instance HasSubTyping m =>
          PartialOrder m ActorSetRep where
    TypedActor rt1 _ `leq` TypedActor rt2 _ = rt2 `subTypeOf` rt1 -- in Monad.hs
    TypedActor rt1 _ `leq` SingletonActor (TypedActorIdSpec rt2 _) =
        rt2 `subTypeOf` rt1
    TypedActor _ _ `leq` _ = return True
    SingletonActor aid1 `leq` SingletonActor aid2 = return $
        aid1 == aid2
    _ `leq` NoActor = return True
    _ `leq` _ = return False

--subTypeOf = undefined

instance HasSubTyping m =>
          JoinSemiLattice m ActorSetRep where
    topM = return NoActor

    NoActor `lub` _ = return NoActor
    _ `lub` NoActor = return NoActor

    ta1@(TypedActor rt1 _) `lub` ta2@(TypedActor rt2 _) = do
      b1 <- rt1 `subTypeOf` rt2
      if b1 then return ta1
       else do
         b2 <- rt2 `subTypeOf` rt1
         if b2 then return ta2
          else return NoActor

    TypedActor rt1 _ `lub` a@(SingletonActor (TypedActorIdSpec rt2 _)) = do
      b <- rt2 `subTypeOf` rt1
      return $ if b then a else NoActor

    a@(SingletonActor (TypedActorIdSpec rt1 _)) `lub` TypedActor rt2 _ = do
      b <- rt1 `subTypeOf` rt2
      return $ if b then a else NoActor

--    a `lub` TypedActor {} = return a
--    TypedActor {} `lub` a = return a

    SingletonActor aid1 `lub` SingletonActor aid2
                       | aid1 == aid2 = return $ SingletonActor aid1
                       | otherwise    = return NoActor

instance HasSubTyping m =>
          Lattice m ActorSetRep where
    bottomM = return $ TypedActor (TcClsRefT objectT) $ B.pack "x"

    NoActor `glb` a = return a
    a `glb` NoActor = return a

    ta1@(TypedActor rt1 _) `glb` ta2@(TypedActor rt2 _) = do
      b1 <- rt1 `subTypeOf` rt2
      if b1 then return ta2
       else do
         b2 <- rt2 `subTypeOf` rt1
         if b2 then return ta1
          else bottomM

    aa@(TypedActor rt1 _) `glb` SingletonActor (TypedActorIdSpec rt2 _) = do
      b <- rt2 `subTypeOf` rt1
      if b then return aa else bottomM
    SingletonActor (TypedActorIdSpec rt1 _) `glb` aa@(TypedActor rt2 _) = do
      b <- rt1 `subTypeOf` rt2
      if b then return aa else bottomM

--    aa@(TypedActor{}) `glb` _a = return aa
--    _a `glb` aa@(TypedActor{}) = return aa

    SingletonActor aid1 `glb` SingletonActor aid2
                       | aid1 == aid2 = return $ SingletonActor aid1
                       | otherwise    = bottomM


instance HasSubTyping m =>
          ActorSet m ActorSetRep TypedActorIdSpec where

  inSet aid1 (SingletonActor aid2) = return $ aid1 == aid2
  inSet (TypedActorIdSpec rt1 _) (TypedActor rt2 _) =
      rt1 `subTypeOf` rt2
  inSet _aid NoActor      = return False

  enumSetMembers (SingletonActor aid) = return $ Just [aid]
  enumSetMembers TypedActor{} = return Nothing
  enumSetMembers NoActor = return $ Just []


--  deriving (Data, Typeable)

{-
instance Data (TcMetaVar a) where
    gunfold    = panic (policyModule ++ ": instance Data TcMetaVar (gunfold)")
                 "Meta variables should never be reified"
    toConstr   = panic (policyModule ++ ": instance Data TcMetaVar (toConstr)")
                 "Meta variables should never be reified"
    dataTypeOf = panic (policyModule ++ ": instance Data TcMetaVar (dataTypeOf)")
                 "Meta variables should never be reified"

instance Typeable (TcMetaVar a) where
    typeOf = panic (policyModule ++ ": instance Typeable TcMetaVar (typeOf)")
             "Meta variables should never be reified"

instance Eq (TcMetaVar a) where
  (TcMetaVar i1 _) == (TcMetaVar i2 _) = i1 == i2

instance Ord (TcMetaVar a) where
  compare (TcMetaVar i1 _) (TcMetaVar i2 _) = compare i1 i2

instance Show (TcMetaVar a) where
  show (TcMetaVar i _) = "$$" ++ show i
-}
{-
data TcClause a = TcClause a [TcAtom]
  deriving (Eq,Ord,Show,Data,Typeable)

data TcAtom = TcAtom (Name SourcePos) [TcActor]
  deriving (Eq,Ord,Show,Data,Typeable)

data TcActor = TcActor ActorId
             | TcVar B.ByteString
  deriving (Eq,Ord,Show,Data,Typeable)

specialConstraintAtom :: TcAtom
specialConstraintAtom = TcAtom (mkSimpleName LName (mkIdent_ "-")) []
-}
---------------------------------------------
-- Pretty printing

instance (Pretty name) =>
    Pretty (Policy name ActorSetRep) where
  pretty (Policy []) = braces $ char ':'
  pretty (Policy cs) = text "{ " <> (hcat (punctuate (text "; ") $ map pretty cs)) <> text "}"

instance (Pretty var, Pretty name) =>
    Pretty (VarPolicy var name ActorSetRep) where
  pretty (ConcretePolicy p) = pretty p
  pretty (PolicyVar v) = pretty v
--  pretty (TcThis)         = text "policyof" <> parens (text "this")
  pretty (Join p1 p2)   = pretty p1 <+> char '*' <+> pretty p2
  pretty (Meet p1 p2)   = pretty p1 <+> char '+' <+> pretty p2

instance Pretty PolicyVarRep where
  pretty ThisVar = text "policyof" <> parens (text "this")
  pretty (PolicyOfVar bs) = text "policyof" <> parens (pretty bs)
  pretty (PolicyTypeParam n) = pretty n

instance (Pretty mvar, Pretty var, Pretty name) =>
    Pretty (MetaPolicy mvar var name ActorSetRep) where
  pretty (VarPolicy p)    = pretty p
  pretty (MetaJoin p1 p2) = pretty p1 <+> char '*' <+> pretty p2
  pretty (MetaMeet p1 p2) = pretty p1 <+> char '+' <+> pretty p2
  pretty (MetaVar mv)     = pretty mv

instance Pretty MetaVarRep where
  pretty (MetaVarRep k i) = text "$$" <> pretty i <> text (show k)

instance (Pretty name) =>
    Pretty (Clause name ActorSetRep) where
  pretty (Clause h es b) =
      let qs = [ ta | ta@TypedActor{} <- es ]
      in (if null qs
          then id
          else (parens (hcat (punctuate comma $ map pretty qs)) <+>)) $
           pretty h <+> text ":" <+>
             hcat (punctuate (char ',') $ map (prettyAtom h es) b)

prettyAtom :: (Pretty name) =>
              ActorSetRep -> [ActorSetRep] -> Atom name -> Doc
prettyAtom hdom doms (Atom n reps) =
    pretty n <>
           opt (not $ null reps)
                   (parens (hcat (punctuate (text ", ") $ map prettyRep reps)))

  where prettyRep HeadActor = prettySetRep hdom
        prettyRep (QuantActor i) = prettySetRep $ doms!!i

prettySetRep :: ActorSetRep -> Doc
prettySetRep (TypedActor _ bx) = pretty bx
prettySetRep as = pretty as

instance Pretty ActorSetRep where
    pretty (TypedActor rty bx) = pretty rty <+> pretty bx
    pretty (SingletonActor aid) = pretty aid
    pretty NoActor = text "-"

{-
instance Pretty TcAtom where
  pretty (TcAtom n as) = pretty n <> opt (not $ null as) (parens (hcat (punctuate (text ", ") $ map pretty as)))
-}
{-
instance Pretty TcActor where
  pretty (TcActor aid) = pretty aid
  pretty (TcVar i) = char '\'' <> pretty i

instance Pretty a => Pretty (PolicyBounds a) where
  pretty (KnownPolicy p) = pretty p
  pretty (PolicyBounds p q) = pretty p <> char '/' <> pretty q
-}
{-
mkSimpleLName :: Ident SourcePos -> Name SourcePos
mkSimpleLName i@(Ident sp _) = Name sp LName Nothing i

--------------------------------------
-- Converting policies to recursive --
-- ones, i.e. with the head flow    --
--------------------------------------
-}

{-TO FIX
toRecPolicy :: TcPolicy -> TcPolicyRec
toRecPolicy (TcPolicy cs)  = TcPolicyRec $ map toRecClause cs
  where toRecClause (TcClause act ats) = TcClause (TcAtom (mkSimpleLName (Ident () flowAtomString)) [act]) ats
toRecPolicy (TcJoin p1 p2) = TcJoinRec (toRecPolicy p1) (toRecPolicy p2)
toRecPolicy (TcMeet p1 p2) = TcMeetRec (toRecPolicy p1) (toRecPolicy p2)
toRecPolicy _ = panic (policyModule ++ "toRecPolicy")
                "Cannot convert non-literal policy to a recursive one"
-}



{-----------------------------------
-- Turning type-level policies   --
-- back to their source reps     --
-----------------------------------

toActor :: TcActor -> Actor
toActor (TcVar i) = Var i
toActor (TcActor aid) = Actor $ ActorName $ Name $ [Ident $ "a" ++ show (getId aid)] -- reprName aid

toActorName :: ActorId -> ActorName
toActorName (Fresh k) = ActorName $ Name $ [Ident $ "a" ++ show k]
toActorName (Alias k) = ActorName $ Name $ [Ident $ "a" ++ show k]

toAtom :: TcAtom -> Atom
toAtom (TcAtom n acts) = Atom n $ map toActor acts

toClause :: TcClause TcActor -> Clause ActorName
toClause (TcClause h ats) = Clause (toActor h) $ map toAtom ats

toPolicyLit :: TcPolicy -> PolicyExp
toPolicyLit (TcPolicy cs) = PolicyLit $ map toClause cs

----------------------------------}
-- Basic policies
{-
class IsPolicy p where
  toPolicy :: PrgPolicy a -> p a
  fromPolicy :: p a -> Maybe (PrgPolicy a)
  includesThis :: p a -> Bool
  join :: p TcActor -> p TcActor -> p TcActor
  meet :: p TcActor -> p TcActor -> p TcActor

instance IsPolicy PrgPolicy where
  toPolicy = id
  fromPolicy = Just

  includesThis TcThis = True
  includesThis (TcJoin p q) = any includesThis [p,q]
  includesThis (TcMeet p q) = any includesThis [p,q]
  includesThis _ = False

  join = lub
  meet = glb

instance IsPolicy TcPolicy where
  toPolicy = RealPolicy
  fromPolicy (RealPolicy p) = Just p
  fromPolicy _ = Nothing

  includesThis (Join p q) = any includesThis [p,q]
  includesThis (RealPolicy p) = includesThis p
  includesThis _ = False

  join (RealPolicy p) (RealPolicy q) = RealPolicy $ p `lub` q
  join p q
      | p == q = p
      | isBottom p = q
      | isBottom q = p
      | isTop p || isTop q = top
  join p q = Join p q

  meet (RealPolicy p) (RealPolicy q) = RealPolicy $ glb p q
  meet p q
       | p == q = p
       | isTop p = q
       | isTop q = p
       | isBottom p || isBottom q = bottom
  meet p q = Meet p q

instance IsPolicy PolicyBounds where
  toPolicy = KnownPolicy . toPolicy
  fromPolicy (KnownPolicy p) = fromPolicy p
  fromPolicy _ = Nothing

  includesThis (KnownPolicy p) = includesThis p
  includesThis (PolicyBounds pb pt) = any includesThis [pb,pt]

  join pb qb = case (pb,qb) of
      (KnownPolicy p, KnownPolicy q) -> KnownPolicy $ p `join` q
      (PolicyBounds p1 p2, PolicyBounds q1 q2) -> mkBounds p1 q1 p2 q2
      (KnownPolicy  p,     PolicyBounds q1 q2) -> mkBounds p  q1 p  q2
      (PolicyBounds p1 p2, KnownPolicy  q    ) -> mkBounds p1 q  p2 q
    where mkBounds a b c d = PolicyBounds (a `join` b) (c `join` d)
  meet pb qb = case (pb,qb) of
      (KnownPolicy p, KnownPolicy q) -> KnownPolicy $ p `meet` q
      (PolicyBounds p1 p2, PolicyBounds q1 q2) -> mkBounds p1 q1 p2 q2
      (KnownPolicy  p,     PolicyBounds q1 q2) -> mkBounds p  q1 p  q2
      (PolicyBounds p1 p2, KnownPolicy  q    ) -> mkBounds p1 q  p2 q
    where mkBounds a b c d = PolicyBounds (a `meet` b) (c `meet` d)


bottom, top, thisP :: IsPolicy pol => pol TcActor
bottom = toPolicy $ TcPolicy [TcClause (TcVar $ B.singleton 'x') []]
top = toPolicy $ TcPolicy []
thisP = toPolicy TcThis

isTop, isBottom :: IsPolicy pol => pol TcActor -> Bool
isTop pol | Just (TcPolicy []) <- fromPolicy pol = True
isTop _ = False

isBottom pol | Just (TcPolicy cs) <- fromPolicy pol = any isBottomC cs
  where isBottomC (TcClause (TcVar _) []) = True
        isBottomC _ = False
isBottom _ = False

----------------------------------
-- meet and join

joinWThis :: (TcPolicy TcActor) -> (TcPolicy TcActor) -> (TcPolicy TcActor)
joinWThis (RealPolicy p) (RealPolicy q) = RealPolicy $ lubWThis p q
joinWThis p q = Join p q

lubWThis :: (PrgPolicy TcActor) -> (PrgPolicy TcActor) -> (PrgPolicy TcActor)
lubWThis TcThis q = q
lubWThis p TcThis = p
lubWThis p q = lub p q

lub :: (PrgPolicy TcActor) -> (PrgPolicy TcActor) -> (PrgPolicy TcActor)
lub p1 p2 | p1 == p2 = p1 -- fake shortcut, we can do better!
lub (TcPolicy cs1) (TcPolicy cs2) =
      let sameFixedCs = [ TcClause (TcActor aid) (as ++ substAll senv bs)
                              | TcClause (TcActor aid) as <- cs1,
                                TcClause (TcActor aid') bs <- cs2,
                                aid == aid',
                                let senv = zip (fuv bs) (map TcVar $ allBinders \\ fuv as)]
          bothVarCs   = [ TcClause a1 (as ++ substAll senv bs)
                              | TcClause a1@(TcVar _) as <- cs1,
                                TcClause (TcVar i2) bs <- cs2,
                                let senv = (i2,a1): zip (fuv bs) (map TcVar $ allBinders \\ fuv as) ]
          fstVarCs    = [ TcClause a1 (as ++ substAll senv bs)
                              | TcClause a1@(TcActor _) as <- cs1,
                                TcClause (TcVar i2) bs <- cs2,
                                let senv = (i2,a1): zip (fuv bs) (map TcVar $ allBinders \\ fuv as) ]
          sndVarCs    = [ TcClause a2 (bs ++ substAll senv as)
                              | TcClause (TcVar i1) as <- cs1,
                                TcClause a2@(TcActor _) bs <- cs2,
                                let senv = (i1,a2): zip (fuv as) (map TcVar $ allBinders \\ fuv bs) ]
      in {- return $ -} TcPolicy $ sameFixedCs ++ bothVarCs ++ fstVarCs ++ sndVarCs

lub p1 p2
    | isBottom p1 = p2
    | isBottom p2 = p1
    | isTop p1 || isTop p2 = top
lub p1 p2 = TcJoin p1 p2


type Subst = [(B.ByteString, TcActor)]

--subst :: Ident () -> TcActor -> [TcAtom] -> [TcAtom]
--subst i1 i2 = substAll [(i1,i2)]

substAll :: Subst -> [TcAtom] -> [TcAtom]
substAll s = map (substAtom s)
    where substAtom env (TcAtom n acts) = TcAtom n (map (substA env) acts)

substA :: Subst -> TcActor -> TcActor
substA env (TcVar i) = case lookup i env of
                         Nothing -> TcVar i
                         Just a -> a
substA _ act = act

fuv :: [TcAtom] -> [B.ByteString]
fuv = concatMap fuv'
    where fuv' (TcAtom _ as) = concatMap fuvA as

fuvA :: TcActor -> [B.ByteString]
fuvA (TcActor _) = []
fuvA (TcVar i) = [i]

allBinders :: [B.ByteString]
allBinders = map B.pack $
              [ show c | c <- ['a' .. 'z']] ++
               [ c : show (i :: Int) | c <- ['a' .. 'z'], i <- [0..]]


glb :: (PrgPolicy TcActor) -> (PrgPolicy TcActor) -> (PrgPolicy TcActor)
-- This one could be smartified
glb (TcPolicy as) (TcPolicy bs) = TcPolicy $ as ++ bs
glb p1 p2
    | p1 == p2 = p1
    | isTop p1 = p2
    | isTop p2 = p1
    | isBottom p1 || isBottom p2 = bottom
glb p1 p2 = TcMeet p1 p2

{-
includesVar :: ActorPolicy -> Bool
includesVar (VarPolicy _) = True
includesVar (Join p q) = includesVar p || includesVar q
includesVar (Meet p q) = includesVar p || includesVar q
includesVar _ = False
-}
-}
----------------------------------------------
{-- Specialisation

specialise :: [TcLock] -> PrgPolicy TcActor -> PrgPolicy TcActor
specialise ls (TcPolicy cs) = TcPolicy $ concatMap (specClause ls) cs
specialise _ p = p

specClause :: [TcLock] -> TcClause TcActor -> [TcClause TcActor]
specClause ls (TcClause h atoms) =
    -- Step 1: generate possible substitutions from each atom
    let substss = map (genSubst ls) atoms -- :: [[Subst]]
        substs  = joinSubsts $ map ([]:) substss
    in remSubsumed [] $
           [ TcClause (substA sub h) (substAll sub atoms \\ map lockToAtom ls)
             | sub <- substs ]

  where genSubst :: [TcLock] -> TcAtom -> [Subst]
        genSubst locks (TcAtom n acts) =
            [ subst' | (TcLock ln aids) <- locks,
                       n == ln,
                       let mS = fmap concat $ sequence $ map (uncurry matchesActor) (zip acts aids),
                       isJust mS,
                       let sub = fromJust mS
                           mSubst = toConsistent sub,
                       isJust mSubst, -- is this redundant?
                       let Just subst' = mSubst ]

        joinSubsts :: [[Subst]] -> [Subst]
        joinSubsts sss =
            let allS = map concat $ cartesian sss -- [Subst]
                conS = catMaybes $ map toConsistent allS      -- [Subst]
            in conS

        remSubsumed :: [TcClause TcActor] -> [TcClause TcActor] -> [TcClause TcActor]
        remSubsumed acc [] = acc
        remSubsumed acc (x:xs) = if any (subsumes x) (acc ++ xs)
                                  then remSubsumed acc xs
                                  else remSubsumed (x:acc) xs

        subsumes :: TcClause TcActor -> TcClause TcActor -> Bool
        subsumes (TcClause h1 as1) (TcClause h2 as2) =
            h1 == h2 && null (as2 \\ as1)

        cartesian :: [[Subst]] -> [[Subst]]
        cartesian [] = [[]]
        cartesian (xs:xss) = [ y:ys | y <- xs, ys <- cartesian xss ]

matchesActor :: TcActor -> ActorId -> Maybe [(Ident SourcePos, TcActor)]
matchesActor (TcActor aid1) aid2 | aid1 == aid2 = Just []
matchesActor (TcVar i) aid = Just [(i, TcActor aid)]
matchesActor _ _ = Nothing

toConsistent :: Subst -> Maybe Subst
toConsistent sub =
    let bndrs = groupBy (\a b -> fst a == fst b) sub
    in  sequence $ map checkConsistent bndrs
        where checkConsistent :: Subst -> Maybe (Ident SourcePos, TcActor)
              checkConsistent s = case nub s of
                                    [x] -> Just x
                                    _   -> Nothing

-}
{-
-- | Converts a lock to an atom so that it can be used in a policy.
-- TODO: check what TcLockVar is for (type methods?), and if needs to
-- have a position (probably not, because it is not named).
lockToAtom :: TcLock -> TcAtom
lockToAtom (TcLock n aids) = TcAtom n $ map TcActor aids
lockToAtom (TcLockVar i)   = TcAtom (mkSimpleLName $ Ident defaultPos i) []

{-
---------------------------
-- Zonking

zonkPolicy :: TcPolicy -> IO TcPolicy
zonkPolicy p@(TcPolicyVar (TcMetaVar _i ref)) = do
  mPol <- readIORef ref
  case mPol of
    Just pol -> do pol' <- zonkPolicy pol
                   writeIORef ref (Just pol') -- short-circuit
                   return pol'
    Nothing -> return p

zonkPolicy (TcJoin p1 p2) = do
  p1' <- zonkPolicy p1
  p2' <- zonkPolicy p2
  return $ p1' `join` p2'

zonkPolicy (TcMeet p1 p2) = do
  p1' <- zonkPolicy p1
  p2' <- zonkPolicy p2
  return $ p1' `meet` p2'

zonkPolicy p = return p
-}
-------------------------------
-- Policy substitution

-- Invariant: policies are always closed by the env
substPolicy :: [(B.ByteString, ActorPolicy)] -> PrgPolicy TcActor -> ActorPolicy
substPolicy env (TcRigidVar _ i)
    | Just q <- lookup i env = q
substPolicy env (TcJoin p1 p2) =
    let pol1 = substPolicy env p1
        pol2 = substPolicy env p2
    in pol1 `join` pol2
substPolicy env (TcMeet p1 p2) =
    let pol1 = substPolicy env p1
        pol2 = substPolicy env p2
    in pol1 `meet` pol2
substPolicy _ p = RealPolicy p

firstRigid :: PrgPolicy a -> Maybe B.ByteString
firstRigid (TcRigidVar _ i) = Just i
firstRigid (TcJoin p q) = listToMaybe $ catMaybes $ map firstRigid [p,q]
firstRigid (TcMeet p q) = listToMaybe $ catMaybes $ map firstRigid [p,q]
firstRigid _ = Nothing

substThis :: ActorPolicy -> PrgPolicy TcActor -> ActorPolicy
substThis p TcThis = p
substThis p (TcJoin p1 p2) =
    let pol1 = substThis p p1
        pol2 = substThis p p2
    in pol1 `join` pol2
substThis p (TcMeet p1 p2) =
    let pol1 = substThis p p1
        pol2 = substThis p p2
    in pol1 `meet` pol2
substThis _ p = RealPolicy p

{-
mkPolicySubst :: [TcPolicy] -> [TcPolicy] -> [(Ident (), TcPolicy)]
mkPolicySubst pPars pArgs = catMaybes $ map aux $ zip pPars pArgs
  where aux (TcRigidVar i, p) = Just (i,p)
        aux _ = Nothing
-}
-}

