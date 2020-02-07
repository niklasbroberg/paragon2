{-# LANGUAGE TemplateHaskell, FlexibleInstances #-}
module Language.Java.Paragon.Annotated where

import Language.Haskell.TH
import Control.Monad ((<=<), void)

class Functor ast => Annotated ast where
  ann :: ast l -> l
  amap :: (l -> l) -> ast l -> ast l

modName :: String
modName = "Language.Java.Paragon.Annotated"

-- | Derive Annotated instances for the given datatype.
deriveAnn :: Name -> Q [Dec]
deriveAnn = deriveAnn' <=< reify

-- | Derive Annotated instances for many datatypes.
deriveAnnMany :: [Name] -> Q [Dec]
deriveAnnMany = deriveAnnMany' <=< mapM reify

-- | Obtain Info values through a custom reification function. This is useful
-- when generating instances for datatypes that have not yet been declared.
deriveAnn' :: Info -> Q [Dec]
deriveAnn' = fmap (:[]) . deriveAnnOne

deriveAnnMany' :: [Info] -> Q [Dec]
deriveAnnMany' = mapM deriveAnnOne

deriveAnnOne :: Info -> Q Dec
deriveAnnOne i =
  case i of
    TyConI (DataD dcx n vsk _ cons _) ->
      annInstance dcx n (map unTyVarBndr vsk) (map doCons cons)
    TyConI (NewtypeD dcx n vsk _ con _) ->
      annInstance dcx n (map unTyVarBndr vsk) [doCons con]
    _ -> error (modName ++ ".deriveAnn: unhandled: " ++ pprint i)
  where annInstance _ _ [] _ = error (modName ++ ".annInstance: unhandled " ++ pprint i)
        annInstance dcx n vs cases =
            let (anns, amaps) = unzip cases
            in instanceD (ctxt dcx (init vs)) (conT ''Annotated `appT` typ n (init vs)) [funD 'ann anns, funD 'amap amaps]
        typ n = foldl appT (conT n) . map varT
        ctxt dcx = fmap (dcx ++) . cxt . map annPred
        unTyVarBndr (PlainTV v) = v
        unTyVarBndr (KindedTV v _) = v
        annPred n = classP ''Annotated [varT n]

doCons :: Con -> (ClauseQ, ClauseQ)
doCons (NormalC c vs@((_,VarT n):sts)) =
  let annDef = clause [conP c (varP n : map (const wildP) sts)] (normalB (varE n)) []

      nams = [ mkName x | x <- zipWith (\_ i -> "x" ++ show i) vs ([0..]::[Int]) ]
      f    = mkName "f"
      arg1 = [| $(varE f) $(varE (head nams)) |]
      args = [ varE nam | nam <- tail nams ]
      rhs  = foldl appE (conE c) (arg1:args)
      amapDef = clause [varP f, conP c (map varP nams)] (normalB rhs) []
  in (annDef, amapDef)
doCons (RecC c sts) = doCons $ NormalC c [(s, t) | (_, s, t) <- sts]
-- doCons (InfixC sty1 c sty2) =
--  let con = [| conE c |]
--      left = [| lift $(varE (mkName "x0")) |]
--      right = [| lift $(varE (mkName "x1")) |]
--      e = [| infixApp $left $con $right |]
--  clause [infixP (varP (mkName "x0")) c (varP (mkName "x1"))] (normalB e) [] -}
doCons c = error (modName ++ ".doCons: Unhandled constructor: " ++ pprint c)

removeAnnotation :: Annotated ast => ast l -> ast ()
removeAnnotation = void

removeAnnotationMany :: Annotated ast => [ast l] -> [ast ()]
removeAnnotationMany = map removeAnnotation

