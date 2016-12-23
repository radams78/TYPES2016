module PHOML.Meta.Gen.Term where
open import Relation.Binary.PropositionalEquality
open import Data.Product renaming (_,_ to _,p_)
open import PHOML.Grammar
open import PHOML.Rules

generation-ΛT : ∀ {V} {Γ : Context V} {A M B} →
  Γ ⊢ ΛT A M ∶ ty B → Σ[ C ∈ Type ] Γ ,T A ⊢ M ∶ ty C × B ≡ A ⇛ C
generation-ΛT (ΛTR {B = B} Γ,A⊢M∶B) = B ,p Γ,A⊢M∶B ,p refl

