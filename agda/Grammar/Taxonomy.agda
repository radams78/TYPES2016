module Grammar.Taxonomy where
open import Data.List
open import Prelims

record Taxonomy : Set₁ where
  field
    VarKind : Set
    NonVarKind : Set

  data ExpKind : Set where
    varKind : VarKind → ExpKind
    nonVarKind : NonVarKind → ExpKind

  infixl 55 _,_
  data Alphabet : Set where
    ∅ : Alphabet
    _,_ : Alphabet → VarKind → Alphabet

  extend : Alphabet → List VarKind → Alphabet
  extend V [] = V
  extend V (K ∷ KK) = extend (V , K) KK

  snoc-extend : Alphabet → snocList VarKind → Alphabet
  snoc-extend V [] = V
  snoc-extend V (KK snoc K) = snoc-extend V KK , K

  data Var : Alphabet → VarKind → Set where
    x₀ : ∀ {V} {K} → Var (V , K) K
    ↑ : ∀ {V} {K} {L} → Var V L → Var (V , K) L

  x₁ : ∀ {V} {K} {L} → Var (V , K , L) K
  x₁ = ↑ x₀

  x₂ : ∀ {V} {K} {L} {L'} → Var (V , K , L , L') K
  x₂ = ↑ x₁

  record SimpleKind (A B : Set) : Set where
    constructor SK
    field
      dom : List A
      cod : B

  infix 71 _✧
  _✧ : ∀ {A} {B} → B → SimpleKind A B
  b ✧ = SK [] b

  infixr 70 _⟶_
  _⟶_ : ∀ {A} {B} → A → SimpleKind A B → SimpleKind A B
  a ⟶ SK dom cod = SK (a ∷ dom) cod

  AbsKind = SimpleKind VarKind ExpKind
  ConKind = SimpleKind AbsKind ExpKind

  data KindClass : Set where
    -Expression : KindClass
    -ListAbs : KindClass

  Kind : KindClass → Set
  Kind -Expression = ExpKind
  Kind -ListAbs = List AbsKind

