module PHOML.Meta.Gen where
open import PHOML.Grammar
open import PHOML.Rules

⊃-gen₂ : ∀ {V} {Γ : Context V} {φ} {ψ} {A} → Γ ⊢ φ ⊃ ψ ∶ A → Γ ⊢ ψ ∶ ty Ω
⊃-gen₂ (⊃R _ Γ⊢ψ∶Ω) = Γ⊢ψ∶Ω

