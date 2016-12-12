module PHOML.Canon.Proof where
open import Relation.Binary.PropositionalEquality
open import Data.Product renaming (_,_ to _,p_)
open import PHOML.Grammar
open import PHOML.Neutral

data CanonP (V : Alphabet) : Set where
  neutral : NeutralP V → CanonP V

decode-CanonP : ∀ {V} → CanonP V → Proof V
decode-CanonP (neutral δ) = decode-NeutralP δ

app-canonl' : ∀ {V} {δ ε : Proof V} {χ : CanonP V} → appP δ ε ≡ decode-CanonP χ → Σ[ χ' ∈ CanonP V ] δ ≡ decode-CanonP χ'
app-canonl' {χ = neutral (var _)} ()
app-canonl' {χ = neutral (app δ _)} δε≡δε = neutral δ ,p appP-injl δε≡δε
app-canonl' {χ = neutral (dirN _ _)} ()
