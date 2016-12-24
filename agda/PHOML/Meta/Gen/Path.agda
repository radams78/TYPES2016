module PHOML.Meta.Gen.Path where
open import PHOML.Grammar
open import PHOML.Red.Conv
open import PHOML.Rules

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
