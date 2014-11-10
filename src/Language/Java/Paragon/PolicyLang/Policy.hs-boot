{-# LANGUAGE CPP, MultiParamTypeClasses, 
    FlexibleInstances, UndecidableInstances #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}
module Language.Java.Paragon.PolicyLang.Policy 
    (
      module Language.Java.Paragon.PolicyLang.Policy
    , HasSubTyping(..)                                      
    )where

import Language.Java.Paragon.Pretty
import {-# SOURCE #-} Language.Java.Paragon.PolicyLang.Actors
import {-# SOURCE #-} Language.Java.Paragon.TypeCheck.Types

import Security.InfoFlow.Policy.FlowLocks

import Control.Applicative

#ifdef BASE4
import Data.Data
#else
import Data.Generics (Data(..),Typeable(..))
#endif

data MetaVarRep
instance Data MetaVarRep
instance Typeable MetaVarRep
instance Eq MetaVarRep
instance Ord MetaVarRep
instance Show MetaVarRep
instance Pretty MetaVarRep


data PolicyVarRep
instance Data PolicyVarRep
instance Typeable PolicyVarRep
instance Eq PolicyVarRep
instance Ord PolicyVarRep
instance Show PolicyVarRep
instance Pretty PolicyVarRep

data ActorSetRep
instance Data ActorSetRep
instance Typeable ActorSetRep
instance Eq ActorSetRep
instance Ord ActorSetRep
instance Show ActorSetRep
instance Pretty ActorSetRep

instance HasSubTyping m =>
          PartialOrder m ActorSetRep

instance HasSubTyping m =>
          JoinSemiLattice m ActorSetRep

instance HasSubTyping m =>
          Lattice m ActorSetRep

instance HasSubTyping m =>
          ActorSet m ActorSetRep TypedActorIdSpec


---------------------------------------------
-- Pretty printing

instance (Pretty name) => 
    Pretty (Policy name ActorSetRep) 

instance (Pretty var, Pretty name) => 
    Pretty (VarPolicy var name ActorSetRep)

instance (Pretty mvar, Pretty var, Pretty name) => 
    Pretty (MetaPolicy mvar var name ActorSetRep) 

instance (Pretty name) => 
    Pretty (Clause name ActorSetRep)

