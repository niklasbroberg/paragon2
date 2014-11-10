{-# LANGUAGE CPP #-}
module Language.Java.Paragon.PolicyLang.Locks where

import Language.Java.Paragon.Pretty

#ifdef BASE4
import Data.Data
#else
import Data.Generics (Data(..),Typeable(..))
#endif

-- | In some places we allow a lock to be represented
--   via a lock(-state) type parameter
data LockSpec
instance Eq LockSpec
instance Ord LockSpec
instance Show LockSpec
instance Data LockSpec
instance Typeable LockSpec
instance Pretty LockSpec
