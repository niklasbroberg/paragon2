{-# LANGUAGE QuasiQuotes, TemplateHaskell #-}
module Language.Java.Paragon.QuasiQuoter.Derive where

import Language.Haskell.TH
import Language.Haskell.TH.Lift

import Data.Data (Data)

import Control.Monad ((<=<))

deriveLiftAll :: [Name] -> Q [Dec]
deriveLiftAll ns = do
  is <- mapM (addDataCx <=< reify) ns
  deriveLiftMany' is

addDataCx :: Info -> Q Info
addDataCx i = 
    case i of
      TyConI (DataD dcx n vsk cons _) -> do
          dp <- dataPred $ head vsk
          return $ TyConI (DataD (dp:dcx) n vsk cons [])
      TyConI (NewtypeD dcx n vsk con _) -> do
          dp <- dataPred $ head vsk
          return $ TyConI (NewtypeD (dp:dcx) n vsk con [])
      _ -> error $ "Unhandled Dec: " ++ show i
  where dataPred (PlainTV  n)   = classP ''Data [varT n]
        dataPred (KindedTV n _) = classP ''Data [varT n]
