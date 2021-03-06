{- Metavariable conventions:
  A, B    range over abstraction kinds
  C       range over kind classes
  AA, BB  range over lists of abstraction kinds
  E, F, G range over subexpressions
  K, L    range over expression kinds including variable kinds
  M, N, P range over expressions
  U, V, W range over alphabets -}
open import Level
open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open import Function
open import Data.List
open import Prelims
open import Grammar.Taxonomy

module Grammar.Base where

record IsGrammar (T : Taxonomy) : Set₁ where
  open Taxonomy T
  field
    Con    : ConKind → Set
    parent : VarKind → ExpKind

record Grammar : Set₁ where
  field
    taxonomy : Taxonomy
    isGrammar : IsGrammar taxonomy
  open Taxonomy taxonomy public
  open IsGrammar isGrammar public

  data Subexp (V : Alphabet) : ∀ C → Kind C → Set
  Expression : Alphabet → ExpKind → Set
  VExpression : Alphabet → VarKind → Set
  Abs : Alphabet → AbsKind → Set
  ListAbs : Alphabet → List AbsKind → Set

  Expression V K = Subexp V -Expression K
  VExpression V K = Expression V (varKind K)
  Abs V (SK AA K) = Expression (extend V AA) K
  ListAbs V AA = Subexp V -ListAbs AA

  infixr 5 _∷_
  data Subexp V where
    var : ∀ {K} → Var V K → VExpression V K
    app : ∀ {AA} {K} → Con (SK AA K) → 
      ListAbs V AA → Expression V K
    [] : ListAbs V []
    _∷_ : ∀ {A} {AA} → Abs V A → 
      ListAbs V AA → ListAbs V (A ∷ AA)

  var-inj : ∀ {V} {K} {x y : Var V K} → var x ≡ var y → x ≡ y
  var-inj refl = refl

  data Types : Alphabet → List VarKind → Set where
    [] : ∀ {V} → Types V []
    _,_ : ∀ {V K AA} → Expression V (parent K) → Types (V , K) AA → Types V (K ∷ AA)

  data snocTypes : Alphabet → snocList VarKind → Set where
    [] : ∀ {V} → snocTypes V []
    _snoc_ : ∀ {V AA K} → snocTypes V AA → Expression (snoc-extend V AA) (parent K) → snocTypes V (AA snoc K)
