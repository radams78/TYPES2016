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

generation-plus : ∀ {V Γ} {P : Path V} {φ} → Γ ⊢ plus P ∶ φ →
  Σ[ ψ ∈ Term V ] Σ[ χ ∈ Term V ] Γ ⊢ P ∶ ψ ≡〈 Ω 〉 χ × φ ≃ ψ ⊃ χ
generation-plus (convPR Γ⊢P+∶φ' Γ⊢φ∶Ω φ'≃φ) = 
  let ψ ,p χ ,p Γ⊢P∶ψ≡χ ,p φ'≃ψ⊃χ = generation-plus Γ⊢P+∶φ' in 
  ψ ,p χ ,p Γ⊢P∶ψ≡χ ,p (trans (sym φ'≃φ) φ'≃ψ⊃χ)
generation-plus (plusR {φ = φ} {ψ = ψ} Γ⊢P∶φ≡ψ) = φ ,p ψ ,p Γ⊢P∶φ≡ψ ,p ref

generation-minus : ∀ {V Γ} {P : Path V} {φ} → Γ ⊢ minus P ∶ φ →
  Σ[ ψ ∈ Term V ] Σ[ χ ∈ Term V ] Γ ⊢ P ∶ ψ ≡〈 Ω 〉 χ × φ ≃ χ ⊃ ψ
generation-minus (convPR Γ⊢P+∶φ' Γ⊢φ∶Ω φ'≃φ) = 
  let ψ ,p χ ,p Γ⊢P∶ψ≡χ ,p φ'≃ψ⊃χ = generation-minus Γ⊢P+∶φ' in 
  ψ ,p χ ,p Γ⊢P∶ψ≡χ ,p (trans (sym φ'≃φ) φ'≃ψ⊃χ)
generation-minus (minusR {φ = φ} {ψ = ψ} Γ⊢P∶φ≡ψ) = φ ,p ψ ,p Γ⊢P∶φ≡ψ ,p ref

generation-reff₁ : ∀ {V} {Γ : Context V} {M N N' : Term V} {A} → Γ ⊢ reff M ∶ N ≡〈 A 〉 N' → Γ ⊢ M ∶ ty A
generation-reff₁ (refR Γ⊢M∶A) = Γ⊢M∶A
generation-reff₁ (convER Γ⊢refM∶N≡N' _ _ _ _) = generation-reff₁ Γ⊢refM∶N≡N'

generation-reff₂ : ∀ {V} {Γ : Context V} {M N N' : Term V} {A} → Γ ⊢ reff M ∶ N ≡〈 A 〉 N' → M ≃ N
generation-reff₂ (refR _) = ref
generation-reff₂ (convER Γ⊢refM∶N≡N' _ _ M≃M' _) = trans (generation-reff₂ Γ⊢refM∶N≡N') M≃M'

generation-reff₃ : ∀ {V} {Γ : Context V} {M N N' : Term V} {A} → Γ ⊢ reff M ∶ N ≡〈 A 〉 N' → M ≃ N'
generation-reff₃ (refR _) = ref
generation-reff₃ (convER Γ⊢refM∶N≡N' _ _ _ N≃N') = trans (generation-reff₃ Γ⊢refM∶N≡N') N≃N'

generation-univ₁ : ∀ {V} {Γ : Context V} {φ ψ δ ε M A N} → Γ ⊢ univ φ ψ δ ε ∶ M ≡〈 A 〉 N → φ ≃ M
generation-univ₁ (univR _ _) = ref
generation-univ₁ (convER Γ⊢univδε∶M≡N _ _ M≃M' _) = trans (generation-univ₁ Γ⊢univδε∶M≡N) M≃M'

generation-univ₂ : ∀ {V} {Γ : Context V} {φ ψ δ ε M A N} → Γ ⊢ univ φ ψ δ ε ∶ M ≡〈 A 〉 N → ψ ≃ N
generation-univ₂ (univR _ _) = ref
generation-univ₂ (convER Γ⊢univδε∶M≡N _ _ _ N≃N') = trans (generation-univ₂ Γ⊢univδε∶M≡N) N≃N'

generation-univ₃ : ∀ {V} {Γ : Context V} {φ ψ δ ε M A N} → Γ ⊢ univ φ ψ δ ε ∶ M ≡〈 A 〉 N → Γ ⊢ δ ∶ φ ⊃ ψ
generation-univ₃ (univR Γ⊢δ∶M⊃N _) = Γ⊢δ∶M⊃N
generation-univ₃ (convER Γ⊢univδε∶M≡N _ _ _ _) = generation-univ₃ Γ⊢univδε∶M≡N

generation-univ₄ : ∀ {V} {Γ : Context V} {φ ψ δ ε M A N} → Γ ⊢ univ φ ψ δ ε ∶ M ≡〈 A 〉 N → Γ ⊢ ε ∶ ψ ⊃ φ
generation-univ₄ (univR _ Γ⊢ε∶N⊃M) = Γ⊢ε∶N⊃M
generation-univ₄ (convER Γ⊢univδε∶M≡N _ _ _ _) = generation-univ₄ Γ⊢univδε∶M≡N