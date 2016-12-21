module PHOML.Meta.Gen where
open import Data.Product renaming (_,_ to _,p_)
open import Prelims
open import PHOML.Grammar
open import PHOML.Red.Conv
open import PHOML.Rules
open import PHOML.Meta.ConVal

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

prop-validity : ∀ {V} {Γ : Context V} {δ : Proof V} {φ : Term V} → Γ ⊢ δ ∶ φ → Γ ⊢ φ ∶ ty Ω
eq-validity₁ : ∀ {V} {Γ : Context V} {P : Path V} {E M A N} → Γ ⊢ P ∶ E → E ≡ M ≡〈 A 〉 N → Γ ⊢ M ∶ ty A
eq-validity₂ : ∀ {V} {Γ : Context V} {P : Path V} {E M A N} → Γ ⊢ P ∶ E → E ≡ M ≡〈 A 〉 N → Γ ⊢ N ∶ ty A

prop-validity (varR _ validΓ) = context-validity-Prop validΓ
prop-validity (appPR Γ⊢δ∶φ⊃ψ _) = generation-⊃₂ (prop-validity Γ⊢δ∶φ⊃ψ)
prop-validity (ΛPR Γ⊢φ∶Ω Γ⊢ψ∶Ω _) = ⊃R Γ⊢φ∶Ω Γ⊢ψ∶Ω
prop-validity (convPR _ Γ⊢φ∶Ω _) = Γ⊢φ∶Ω
prop-validity (plusR Γ⊢P∶φ≡ψ) = ⊃R (eq-validity₁ Γ⊢P∶φ≡ψ refl) (eq-validity₂ Γ⊢P∶φ≡ψ refl)
prop-validity (minusR Γ⊢P∶φ≡ψ) = ⊃R (eq-validity₂ Γ⊢P∶φ≡ψ refl) (eq-validity₁ Γ⊢P∶φ≡ψ refl)

eq-validity₁ (varR {Γ = Γ} _ validΓ) E≡M≡N = subst (λ E → Γ ⊢ left E ∶ ty (type E)) E≡M≡N (context-validity-Eq₁ validΓ)
eq-validity₁ {Γ = Γ} (refR Γ⊢P∶M≡N) E≡M≡N = subst₂ (λ x y → Γ ⊢ x ∶ ty y) (eq-inj₁ E≡M≡N) (eq-inj₂ E≡M≡N) Γ⊢P∶M≡N
eq-validity₁ {Γ = Γ} (⊃*R Γ⊢P∶φ≡φ' Γ⊢Q∶ψ≡ψ') E≡φ⊃ψ≡φ'⊃ψ' = subst₂ (λ x y → Γ ⊢ x ∶ ty y) (eq-inj₁ E≡φ⊃ψ≡φ'⊃ψ') (eq-inj₂ E≡φ⊃ψ≡φ'⊃ψ') (⊃R (eq-validity₁ Γ⊢P∶φ≡φ' refl) (eq-validity₁ Γ⊢Q∶ψ≡ψ' refl))
eq-validity₁ {Γ = Γ} (univR Γ⊢δ∶φ⊃ψ Γ⊢ε∶ψ⊃φ) E≡φ≡ψ = subst₂ (λ x y → Γ ⊢ x ∶ ty y) (eq-inj₁ E≡φ≡ψ) (eq-inj₂ E≡φ≡ψ) (generation-⊃₂ (prop-validity Γ⊢ε∶ψ⊃φ))
eq-validity₁ {Γ = Γ} (lllR Γ⊢M∶A _ _) E≡M≡N = subst₂ (λ x y → Γ ⊢ x ∶ ty y) (eq-inj₁ E≡M≡N) (eq-inj₂ E≡M≡N) Γ⊢M∶A
eq-validity₁ {Γ = Γ} (appER Γ⊢N∶A Γ⊢N'∶A Γ⊢P∶M≡M' Γ⊢Q∶N≡N') E≡M≡N = subst₂ (λ x y → Γ ⊢ x ∶ ty y) (eq-inj₁ E≡M≡N) (eq-inj₂ E≡M≡N) (appTR (eq-validity₁ Γ⊢P∶M≡M' refl) Γ⊢N∶A)
eq-validity₁ {Γ = Γ} (convER Γ⊢P∶M≡N Γ⊢M'∶A Γ⊢N'∶A M≃M' N≃N') E≡M≡N = subst₂ (λ x y → Γ ⊢ x ∶ ty y) (eq-inj₁ E≡M≡N) (eq-inj₂ E≡M≡N) Γ⊢M'∶A

eq-validity₂ {Γ = Γ} (varR _ validΓ) E≡M≡N = subst (λ E → Γ ⊢ right E ∶ ty (type E)) E≡M≡N (context-validity-Eq₂ validΓ)
eq-validity₂ {Γ = Γ} (refR Γ⊢M∶A) E≡M≡N = subst₂ (λ x y → Γ ⊢ x ∶ ty y) (eq-inj₃ E≡M≡N) (eq-inj₂ E≡M≡N) Γ⊢M∶A
eq-validity₂ {Γ = Γ} (⊃*R Γ⊢P∶φ≡ψ Γ⊢Q∶φ'≡ψ') E≡M≡N = subst₂ (λ x y → Γ ⊢ x ∶ ty y) (eq-inj₃ E≡M≡N) (eq-inj₂ E≡M≡N) (⊃R (eq-validity₂ Γ⊢P∶φ≡ψ refl) (eq-validity₂ Γ⊢Q∶φ'≡ψ' refl))
eq-validity₂ {Γ = Γ} (univR Γ⊢δ∶φ⊃ψ Γ⊢ε∶ψ⊃φ) E≡M≡N = subst₂ (λ x y → Γ ⊢ x ∶ ty y) (eq-inj₃ E≡M≡N) (eq-inj₂ E≡M≡N) (generation-⊃₂ (prop-validity Γ⊢δ∶φ⊃ψ))
eq-validity₂ {Γ = Γ} (lllR _ Γ⊢N∶A⇛B _) E≡M≡N = subst₂ (λ x y → Γ ⊢ x ∶ ty y) (eq-inj₃ E≡M≡N) (eq-inj₂ E≡M≡N) Γ⊢N∶A⇛B
eq-validity₂ {Γ = Γ} (appER Γ⊢N∶A Γ⊢N'∶A Γ⊢P∶M≡M' Γ⊢Q∶N≡N') E≡M≡N = subst₂ (λ x y → Γ ⊢ x ∶ ty y) (eq-inj₃ E≡M≡N) (eq-inj₂ E≡M≡N) (appTR (eq-validity₂ Γ⊢P∶M≡M' refl) Γ⊢N'∶A)
eq-validity₂ {Γ = Γ} (convER _ _ Γ⊢N'∶A _ _) E≡M≡N = subst₂ (λ x y → Γ ⊢ x ∶ ty y) (eq-inj₃ E≡M≡N) (eq-inj₂ E≡M≡N) Γ⊢N'∶A

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

generation-app* : ∀ {V} {Γ : Context V} {P : Path V} {M N Q L B L'} →
  Γ ⊢ app* M N P Q ∶ L ≡〈 B 〉 L' →
  Σ[ A ∈ Type ] Σ[ F ∈ Term V ] Σ[ G ∈ Term V ] Γ ⊢ P ∶ F ≡〈 A ⇛ B 〉 G × Γ ⊢ Q ∶ M ≡〈 A 〉 N × appT F M ≃ L × appT G N ≃ L'
generation-app* (appER {M = F} {M' = G} {A = A} Γ⊢N∶A Γ⊢N'∶A Γ⊢P∶F≡G Γ⊢Q∶N≡N') = A ,p F ,p G ,p Γ⊢P∶F≡G ,p Γ⊢Q∶N≡N' ,p ref ,p ref
generation-app* (convER Γ⊢PQ∶L≡L' _ _ L≃L₁ L'≃L₁') = 
  let A ,p F ,p G ,p Γ⊢P∶F≡G ,p Γ⊢Q∶M≡N ,p FM≃L ,p GN≃L' = generation-app* Γ⊢PQ∶L≡L' in
  A ,p F ,p G ,p Γ⊢P∶F≡G ,p Γ⊢Q∶M≡N ,p trans FM≃L L≃L₁ ,p trans GN≃L' L'≃L₁'

generation-λλλ : ∀ {V} {Γ : Context V} {A P M B N} →
  Γ ⊢ λλλ A P ∶ M ≡〈 B 〉 N → Σ[ C ∈ Type ] addpath Γ A ⊢ P ∶ appT (M ⇑ ⇑ ⇑) (var x₂) ≡〈 C 〉 appT (N ⇑ ⇑ ⇑) (var x₁) × B ≡ A ⇛ C
generation-λλλ (lllR {B = C} _ _ Γ⊢P∶Mx≡Ny) = C ,p Γ⊢P∶Mx≡Ny ,p refl
generation-λλλ {Γ = Γ} {A = A} (convER {M = M} Γ⊢ΛP∶M≡N Γ⊢M'∶B Γ⊢N'∶B M≃M' N≃N') = 
  let C ,p Γ⊢P∶Mx≡Ny ,p B≡A⇛C = generation-λλλ Γ⊢ΛP∶M≡N in
  C ,p 
  let ΓAAE⊢M∶A⇛C : addpath Γ A ⊢ M ⇑ ⇑ ⇑ ∶ ty (A ⇛ C)
      ΓAAE⊢M∶A⇛C = weakening (weakening (weakening (change-type (eq-validity₁ Γ⊢ΛP∶M≡N refl) (cong ty B≡A⇛C)) (ctxTR (context-validity Γ⊢ΛP∶M≡N)) (upRep-typed (ty A))) {!!} {!!}) {!!} {!!} in 
  {!!} ,p 
  B≡A⇛C