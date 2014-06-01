{- PiForall language, OPLSS, Summer 2013 -}

{-# LANGUAGE TemplateHaskell, FlexibleInstances, MultiParamTypeClasses, FlexibleContexts, UndecidableInstances, ViewPatterns, EmptyDataDecls #-}

{-# OPTIONS_GHC -Wall -fno-warn-unused-matches -fno-warn-orphans #-}

-- | The abstract syntax of the simple dependently typed language
-- See comment at the top of 'Parser' for the concrete syntax

module Syntax where

import Generics.RepLib hiding (Data,Refl)
import Unbound.LocallyNameless hiding (Data,Refl)
import Unbound.LocallyNameless.Ops (unsafeUnbind)
import Text.ParserCombinators.Parsec.Pos
import Data.Set (Set)
import qualified Data.Set as S
import Data.Maybe (fromMaybe)

-----------------------------------------
-- * Variable names
-----------------------------------------

-- | module names
type MName  = Name Module

-- | term names
type TName = Name Term

-- | type constructor names
data TyCon
type TCName = Name TyCon

-- | data constructor names
type DCName = String

-----------------------------------------
-- * Core language
-----------------------------------------

data Term =
     Var TName                          -- ^ variables
   | Lam (Bind (TName, Embed Annot) Term)
                                        -- ^ abstraction
   | App Term Arg                       -- ^ application
   | Type Int                           -- ^ universe level
   | Pi  (Bind (TName, Embed Term) Term) -- ^ function type

   | Quotient Term Term        -- ^ quotient type `A // R`
   | QBox Term Annot           -- ^ quotient introduction `<x:Q>`
   | QElim Term Term Term Term -- ^ quotient elimination

   -- practical matters for surface language
   | Ann Term Term         -- ^ Annotated terms `( x : A )`
   | Pos SourcePos Term    -- ^ marked source position, for error messages

   -- conveniences
   | TrustMe Annot         -- ^ an axiom 'TRUSTME', inhabits all types
   | Hole TName Annot

   -- empty
   | TyEmpty               -- ^ The type with no inhabitant

   -- unit
   | TyUnit                -- ^ The type with a single inhabitant `One`
   | LitUnit               -- ^ The inhabitant, written tt

   | TySquash Term         -- ^ Squash types

   | Let (Bind (TName, Embed Term) Term)
     -- ^ let expression, introduces a new definition in the ctx

   | Sigma (Bind (TName, Embed Term) Term)
     -- ^ sigma type '{ x : A | B }'
   | Prod Term Term Annot
     -- ^ introduction for sigmas '( a , b )'
   | Pcase Term (Bind (TName, TName) Term) Annot
     -- ^ elimination form  'pcase p of (x,y) -> p'

   -- equality
   | Refl Annot Term
   | TyEq Term Term Annot Annot
   | Subst Term Term (Maybe (Bind TName Term)) -- ^ equality elimination
   | Contra Term Annot  -- ^ witness to contradiction

   -- tactics
   | Trivial Annot
   | Induction Annot [Term]

   -- inductive datatypes
   | TCon TCName [Term]      -- ^ type constructors (fully applied)
   | DCon DCName [Arg] Annot -- ^ term constructors (fully applied)
   | Case Term [Match] Annot -- ^ case analysis

   | Smaller Term Term
      -- ^ The structural order type, @a < b@
   | OrdAx Annot
      -- ^ Constructor for ord type:  x < C .. x ..
   | Ind (Bind (TName, TName) Term) Annot
      -- ^ inductive definition, binds function name and argument in term
   | PiC (Bind (TName, Embed Term)
          (Term,Term))
      -- ^ constrained function type '[ x : Nat | x < y ] -> B'
   deriving Show

-- | An 'Annot' is optional type information
newtype Annot = Annot (Maybe Term) deriving Show

-- | A 'Match' represents a case alternative
data Match = Match (Bind Pattern Term) deriving (Show)

-- | The patterns of case expressions bind all variables
-- in their respective branches.
data Pattern = PatCon DCName [Pattern]
             | PatVar TName deriving (Show, Eq)

data Arg  = Arg Term deriving (Show)

-----------------------------------------
-- * Modules and declarations
-----------------------------------------

-- | A Module has a name, a list of imports, a list of declarations,
--   and a set of constructor names (which affect parsing).
data Module = Module { moduleName         :: MName,
                       moduleImports      :: [ModuleImport],
                       moduleEntries      :: [Decl],
                       moduleConstructors :: ConstructorNames
                     }
  deriving (Show)

newtype ModuleImport = ModuleImport MName
  deriving (Show,Eq)

data ConstructorNames = ConstructorNames {
                          tconNames :: Set TCName,
                          dconNames :: Set DCName
                        }
  deriving (Show, Eq)

-- | Declarations are the components of modules
data Decl = Sig     TName  Term
           -- ^ Declaration for the type of a term
          | Axiom   TName  Term
            -- ^ An theorem that can be assumed to be true
          | Def     TName  Term
            -- ^ The definition of a particular name, must
            -- already have a type declaration
          | Data    TCName Telescope Int [ConstructorDef]
            -- ^ Declaration for a datatype including all of
            -- its data constructors
  deriving Show

-- | A Data constructor has a name and a telescope of arguments
data ConstructorDef = ConstructorDef SourcePos DCName Telescope
  deriving Show

-------------
-- * Telescopes
-------------

-- | A telescope is like a first class context. It binds each name
-- in the rest of the telescope.  For example
--     Delta = x:* , y:x, z :y = w, empty
data Telescope = Empty
               | Cons (Rebind (TName, Embed Term) Telescope)
  deriving (Show)

-------------
-- * Auxiliary functions on syntax
-------------

-- | empty set of constructor names
emptyConstructorNames :: ConstructorNames
emptyConstructorNames = ConstructorNames S.empty S.empty

-- | Default name for '_' occurring in patterns
wildcardName :: TName
wildcardName = string2Name "_"

-- | empty Annotation
noAnn :: Annot
noAnn = Annot Nothing

-- | Extract the term from an Arg
unArg :: Arg -> Term
unArg (Arg t) = t

-- | Partial inverse of Pos
unPos :: Term -> Maybe SourcePos
unPos (Pos p _) = Just p
unPos _         = Nothing

-- | Tries to find a Pos anywhere inside a term
unPosDeep :: Term -> Maybe SourcePos
unPosDeep = something (mkQ Nothing unPos)

-- | Tries to find a Pos inside a term, otherwise just gives up.
unPosFlaky :: Term -> SourcePos
unPosFlaky t = fromMaybe (newPos "unknown location" 0 0) (unPosDeep t)

-- | Is this the syntax of a literal (natural) number
isNumeral :: Term -> Maybe Int
isNumeral (Pos _ t) = isNumeral t
isNumeral (DCon c [] _) | c== "Zero" = Just 0
isNumeral (DCon c [Arg t] _) | c==  "Succ" =
  do n <- isNumeral t ; return (n+1)
isNumeral _ = Nothing

-- | Is this pattern a variable
isPatVar :: Pattern -> Bool
isPatVar (PatVar _) = True
isPatVar _          = False

-----------------
-- * Alpha equivalence, free variables and substitution.
------------------

{- We use the unbound library to mark the binding occurrences of
   variables in the syntax. That allows us to automatically derive
   functions for alpha-equivalence, free variables and substitution
   using the template haskell directives and default class instances
   below.
-}

-- Defining SourcePos abstractly means that they get ignored
-- when comparing terms.
derive_abstract [''SourcePos]
instance Alpha SourcePos
instance Subst b SourcePos

derive [''Term, ''Match,
        ''Pattern, ''Telescope, ''Module, ''TyCon, ''Decl,
        ''ConstructorNames, ''ModuleImport, ''ConstructorDef,
        ''Arg, ''Annot]

-- Among other things, the Alpha class enables the following
-- functions:
--    aeq :: Alpha a => a -> a -> Bool
--    fv  :: Alpha a => a -> [Name a]

instance Alpha Term
instance Alpha Match
instance Alpha Pattern
instance Alpha Telescope
instance Alpha Arg
instance Alpha ConstructorDef
instance Alpha Annot


-- The subst class derives capture-avoiding substitution
-- It has two parameters because the sort of thing we are substiting
-- for may not be the same as what we are substituting into:

-- class Subst b a where
--    subst  :: Name b -> b -> a -> a       -- single substitution
--    substs :: [(Name b, b)] -> a -> a     -- multiple substitution

instance Subst Term Term where
  isvar (Var x) = Just (SubstName x)
  isvar _ = Nothing

instance Subst Term Match
instance Subst Term Pattern
instance Subst Term Telescope
instance Subst Term Arg
instance Subst Term ConstructorDef
instance Subst Term Annot

-- | Substitute a list of terms for the variables bound in a telescope
-- This is used to instantiate the parameters of a data constructor
-- to find the types of its arguments.
substTele :: Telescope -> [ Term ] -> Telescope -> Telescope
substTele tele args = substs (mkSubst tele args) where
  mkSubst Empty [] = []
  mkSubst (Cons (unrebind->((x,_),tele'))) (tm : tms) =
       (x,tm) : mkSubst tele' tms
  mkSubst _ _ = error "Internal error: substTele given illegal arguments"


