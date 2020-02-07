{-# LANGUAGE CPP, DeriveDataTypeable, FlexibleInstances #-}
module Language.Java.Paragon.TypeCheck.NullAnalysis
    (
     NullType, NullAnnot(..), NullModif(..),
     nullable, committed, free,
     joinNT
    ) where
import Language.Java.Paragon.Pretty

#ifdef BASE4
import Data.Data
#else
import Data.Generics (Data(..),Typeable(..))
#endif

import Prelude hiding ((<>))


data NullAnnot = NotNull | MaybeNull
                 deriving (Eq, Show, Data, Typeable)

data NullModif = Free | Committed | Unclassified
                 deriving (Eq, Show, Data, Typeable)

type NullType = (NullAnnot, NullModif)


instance Ord NullAnnot where
    MaybeNull <= NotNull = False
    _ <= _ = True

instance Ord NullModif where
    _ <= Unclassified = True
    nm1 <= nm2 = nm1 == nm2

instance Pretty NullAnnot where
    pretty = text . show

instance Pretty NullModif where
    pretty = text . show

instance Pretty NullType where
    pretty (na, nm) = text "(" <> pretty na <> text ", " <> pretty nm <> text ")"

nullable :: NullType -> Bool
nullable (MaybeNull, _) = True
nullable _ = False

committed :: NullType -> Bool
committed (_, Committed) = True
committed _ = False

free :: NullType -> Bool
free (_, Free) = True
free _ = False

joinNA :: NullAnnot -> NullAnnot -> NullAnnot
joinNA MaybeNull _ = MaybeNull
joinNA NotNull a   = a

joinNM :: NullModif -> NullModif -> NullModif
joinNM Committed Committed = Committed
joinNM _ _ = Free

joinNT :: NullType -> NullType -> NullType
joinNT (an1, mod1) (an2, mod2) = (an1 `joinNA` an2, mod1 `joinNM` mod2)

