module PHOML.Meta.Gen.Term where
open import Relation.Binary.PropositionalEquality
open import Data.Product renaming (_,_ to _,p_)
open import PHOML.Grammar
open import PHOML.Rules

generation-var : ∀ {V} {Γ : Context V} {x : Var V -Term} {M A} → Γ ⊢ M ∶ A → M ≡ var x →
  A ≡ typeof x Γ
generation-var {Γ = Γ} (varR _ _) x≡x = cong (λ v → typeof v Γ) (var-inj x≡x)
generation-var (⊥R _) ()
generation-var (⊃R _ _) ()
generation-var (appTR _ _) ()
generation-var (ΛTR _) ()

generation-ΛT : ∀ {V} {Γ : Context V} {A M B} →
  Γ ⊢ ΛT A M ∶ ty B → Σ[ C ∈ Type ] (Γ ,T A ⊢ M ∶ ty C × B ≡ A ⇛ C)
generation-ΛT (ΛTR {B = B} Γ,A⊢M∶B) = B ,p Γ,A⊢M∶B ,p refl

generation-appT : ∀ {V} {Γ : Context V} {M N : Term V} {B} →
  Γ ⊢ appT M N ∶ ty B → Σ[ A ∈ Type ] (Γ ⊢ M ∶ ty (A ⇛ B) × Γ ⊢ N ∶ ty A)
generation-appT (appTR {V} {Γ} {M} {N} {A} {B} Γ⊢M∶A⇛B Γ⊢N∶A) = A ,p Γ⊢M∶A⇛B ,p Γ⊢N∶A

generation-⊃₁ : ∀ {V} {Γ : Context V} {φ} {ψ} {A} → Γ ⊢ φ ⊃ ψ ∶ ty A → Γ ⊢ φ ∶ ty Ω
generation-⊃₁ (⊃R Γ⊢φ∶Ω _) = Γ⊢φ∶Ω

generation-⊃₂ : ∀ {V} {Γ : Context V} {φ} {ψ} {A} → Γ ⊢ φ ⊃ ψ ∶ ty A → Γ ⊢ ψ ∶ ty Ω
generation-⊃₂ (⊃R _ Γ⊢ψ∶Ω) = Γ⊢ψ∶Ω

generation-⊃₃ : ∀ {V} {Γ : Context V} {φ} {ψ} {A} → Γ ⊢ φ ⊃ ψ ∶ ty A → A ≡ Ω
generation-⊃₃ (⊃R _ _) = refl
