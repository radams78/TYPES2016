module PHOML.Meta.Gen where
open import Data.Product renaming (_,_ to _,p_)
open import Prelims
open import PHOML.Grammar
open import PHOML.Red.Conv
open import PHOML.Rules

generation-ΛT : ∀ {V} {Γ : Context V} {A M B} →
  Γ ⊢ ΛT A M ∶ ty B → Σ[ C ∈ Type ] Γ ,T A ⊢ M ∶ ty C × B ≡ A ⇛ C
generation-ΛT (ΛTR {B = B} Γ,A⊢M∶B) = B ,p Γ,A⊢M∶B ,p refl

generation-appT : ∀ {V} {Γ : Context V} {M N : Term V} {B} →
  Γ ⊢ appT M N ∶ ty B → Σ[ A ∈ Type ] Γ ⊢ M ∶ ty (A ⇛ B) × Γ ⊢ N ∶ ty A
generation-appT (appTR {V} {Γ} {M} {N} {A} {B} Γ⊢M∶A⇛B Γ⊢N∶A) = A ,p Γ⊢M∶A⇛B ,p Γ⊢N∶A

generation-⊃₁ : ∀ {V} {Γ : Context V} {φ} {ψ} {A} → Γ ⊢ φ ⊃ ψ ∶ ty A → Γ ⊢ φ ∶ ty Ω
generation-⊃₁ (⊃R Γ⊢φ∶Ω _) = Γ⊢φ∶Ω

generation-⊃₂ : ∀ {V} {Γ : Context V} {φ} {ψ} {A} → Γ ⊢ φ ⊃ ψ ∶ ty A → Γ ⊢ ψ ∶ ty Ω
generation-⊃₂ (⊃R _ Γ⊢ψ∶Ω) = Γ⊢ψ∶Ω

generation-⊃₃ : ∀ {V} {Γ : Context V} {φ} {ψ} {A} → Γ ⊢ φ ⊃ ψ ∶ ty A → A ≡ Ω
generation-⊃₃ (⊃R _ _) = refl

generation-appP : ∀ {V} {Γ : Context V} {δ ε φ} → Γ ⊢ appP δ ε ∶ φ → 
  Σ[ ψ ∈ Term V ] Σ[ χ ∈ Term V ] Γ ⊢ δ ∶ ψ ⊃ χ × Γ ⊢ ε ∶ ψ × χ ≃ φ
generation-appP (appPR Γ⊢δ∶ψ⊃φ Γ⊢ε∶ψ) = _ ,p _ ,p Γ⊢δ∶ψ⊃φ ,p Γ⊢ε∶ψ ,p ref
generation-appP (convPR Γ⊢δε∶φ _ φ≃φ') = 
  let ψ ,p χ ,p Γ⊢δ∶ψ⊃χ ,p Γ⊢ε∶ψ ,p χ≃φ = generation-appP Γ⊢δε∶φ in
  ψ ,p χ ,p Γ⊢δ∶ψ⊃χ ,p Γ⊢ε∶ψ ,p trans χ≃φ φ≃φ'
