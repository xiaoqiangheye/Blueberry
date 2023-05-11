{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE DeriveGeneric #-}

module Front.Ast where

import Data.Function (on)
import Data.Maybe (fromMaybe)
import Data.Set (Set)
import Unbound.Generics.LocallyNameless qualified as Unbound
import GHC.Generics (Generic, from)
import Data.Typeable (Typeable)


type Type = Term


newtype Program = Program [Decl]
    deriving (Show, Typeable)


data Term =
      Type
	| Var String
	| Lam String Term
	| App Term Term
	| PI String Type Type
	| Ann Term Type
	| Prod Term Term
	| VBool Bool
	| TBool
	| Sum Term Term
	| TyEq Term Term
	| Refl
	| Contra Term
	| Subst Term Term
	| VUnit
	| TUnit
	| Let String Term Term
	| If Term Term Term
	| Sigma String Term Term
	| Pair Term Term
	-- | Let (Unbound.Bind TName Term) Term
	-- | LetPair Term String Term
    deriving (Show, Generic, Typeable, Eq)


data Sig = Sig {sigName :: String, sigType :: Type}
	deriving (Show)

data Decl =
	 TypeSig Sig
   | Def String Term
   | RecDef String Term
   | Data String [ConstructorDef]
   deriving (Show)



data ConstructorDef = ConstructorDef String Term
	deriving (Show)

mkSig :: String -> Type -> Decl
mkSig name typ = TypeSig (Sig {sigName = name, sigType = typ})


wildcard :: String
wildcard = "_"


-- instance Unbound.Alpha Term where
--   aeq' ctx (Ann a _) b = Unbound.aeq' ctx a b
--   aeq' ctx a (Ann b _) = Unbound.aeq' ctx a b
--   aeq' ctx a b = (Unbound.gaeq ctx `on` from) a b

 
-- instance Unbound.Subst Term Term where
--   isvar (Var x) = Just (Unbound.SubstName x)
--   isvar _ = Nothing
