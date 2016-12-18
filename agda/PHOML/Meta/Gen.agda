module PHOML.Meta.Gen where
open import Data.Product renaming (_,_ to _,p_)
open import PHOML.Grammar
open import PHOML.Rules

generation-appT : ∀ {V} {Γ : Context V} {M N : Term V} {B} →
  Γ ⊢ appT M N ∶ ty B → Σ[ A ∈ Type ] Γ ⊢ M ∶ ty (A ⇛ B) × Γ ⊢ N ∶ ty A
generation-appT (appR {V} {Γ} {M} {N} {A} {B} Γ⊢M∶A⇛B Γ⊢N∶A) = A ,p Γ⊢M∶A⇛B ,p Γ⊢N∶A

generation-⊃₂ : ∀ {V} {Γ : Context V} {φ} {ψ} {A} → Γ ⊢ φ ⊃ ψ ∶ A → Γ ⊢ ψ ∶ ty Ω
generation-⊃₂ (⊃R _ Γ⊢ψ∶Ω) = Γ⊢ψ∶Ω

