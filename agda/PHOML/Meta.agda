module PHOML.Meta where
open import Data.Product renaming (_,_ to _,p_)
open import Prelims
open import PHOML.Grammar
open import PHOML.Red
open import PHOML.Rules
open import PHOML.PathSub
open import PHOML.Meta.ConVal public
open import PHOML.Meta.Gen public
open import PHOML.Meta.Sub public
open import PHOML.Meta.PathSub public
open import PHOML.Meta.TypeVal public

generation-ΛP : ∀ {V} {Γ : Context V} {φ δ ψ} →
  Γ ⊢ ΛP φ δ ∶ ψ → Σ[ χ ∈ Term V ] Γ ,P φ ⊢ δ ∶ χ ⇑ × ψ ≃ φ ⊃ χ
generation-ΛP (ΛPR _ _ Γ,φ⊢δ∶ψ) = _ ,p Γ,φ⊢δ∶ψ ,p ref
generation-ΛP (convPR Γ⊢Λδ∶ψ Γ⊢ψ'∶Ω ψ≃ψ') =
  let χ ,p Γ,φ⊢δ∶χ ,p χ≃φ⊃ψ = generation-ΛP Γ⊢Λδ∶ψ in 
  χ ,p Γ,φ⊢δ∶χ ,p trans (sym ψ≃ψ') χ≃φ⊃ψ

≃-⊃-injl : ∀ {V} {φ φ' ψ ψ' : Term V} → φ ⊃ ψ ≃ φ' ⊃ ψ' → φ ≃ φ'
≃-⊃-injl {V} {φ} {φ'} {ψ} {ψ'} φ⊃ψ≃φ'⊃ψ' = 
  let cr χ φ⊃ψ↠χ φ'⊃ψ'↠χ = PHOML-Church-Rosser φ⊃ψ≃φ'⊃ψ' in 
  let φ₀ ,p ψ₀ ,p χ≡φ₀⊃ψ₀ ,p φ↠φ₀ = imp-red-inj₁' φ⊃ψ↠χ refl in
  trans (sub-RT-RST φ↠φ₀) (sym (sub-RT-RST (imp-red-inj₁ (subst (λ x → φ' ⊃ ψ' ↠ x) χ≡φ₀⊃ψ₀ φ'⊃ψ'↠χ))))

≃-⊃-injr : ∀ {V} {φ φ' ψ ψ' : Term V} → φ ⊃ ψ ≃ φ' ⊃ ψ' → ψ ≃ ψ'
≃-⊃-injr {V} {φ} {φ'} {ψ} {ψ'} φ⊃ψ≃φ'⊃ψ' = 
  let cr χ φ⊃ψ↠χ φ'⊃ψ'↠χ = PHOML-Church-Rosser φ⊃ψ≃φ'⊃ψ' in 
  let φ₀ ,p ψ₀ ,p χ≡φ₀⊃ψ₀ ,p ψ↠ψ₀ = imp-red-inj₂' φ⊃ψ↠χ refl in
  trans (sub-RT-RST ψ↠ψ₀) (sym (sub-RT-RST (imp-red-inj₂ (subst (λ x → φ' ⊃ ψ' ↠ x) χ≡φ₀⊃ψ₀ φ'⊃ψ'↠χ))))

subject-reduction-⇒ : ∀ {V} {K} {E F : Expression V (varKind K)} {Γ} {A} →
  Γ ⊢ E ∶ A → E ⇒ F → Γ ⊢ F ∶ A
subject-reduction-⇒ {A = app (-ty B) []} Γ⊢ΛMN∶B βT = 
  let C ,p Γ⊢ΛM∶C⇛B ,p Γ⊢N∶C = generation-appT Γ⊢ΛMN∶B in
  let D ,p Γ,A⊢M∶D ,p C⇛B≡A⇛D = generation-ΛT Γ⊢ΛM∶C⇛B in
  change-type (substitution Γ,A⊢M∶D (context-validity Γ⊢ΛMN∶B) (botSub-typed (change-type Γ⊢N∶C (cong ty (⇛-injl C⇛B≡A⇛D))))) 
  (cong ty (≡-sym (⇛-injr C⇛B≡A⇛D)))
subject-reduction-⇒ {A = app (-ty A) []} Γ⊢MN∶A (appTl M⇒M') = 
  let B ,p Γ⊢M∶B⇛A ,p Γ⊢N∶B = generation-appT Γ⊢MN∶A in
  appTR (subject-reduction-⇒ Γ⊢M∶B⇛A M⇒M') Γ⊢N∶B
subject-reduction-⇒ {A = app (-ty A) []} Γ⊢φ⊃ψ∶Ω (impl φ⇒φ') = 
  let Γ⊢φ∶Ω = generation-⊃₁ Γ⊢φ⊃ψ∶Ω in
  let Γ⊢ψ∶Ω = generation-⊃₂ Γ⊢φ⊃ψ∶Ω in
  let A≡Ω = generation-⊃₃ Γ⊢φ⊃ψ∶Ω in
  change-type (⊃R (subject-reduction-⇒ Γ⊢φ∶Ω φ⇒φ') Γ⊢ψ∶Ω) (cong ty (≡-sym A≡Ω))
subject-reduction-⇒ {A = app (-ty A) []} Γ⊢φ⊃ψ∶Ω (impr ψ⇒ψ') = 
  let Γ⊢φ∶Ω = generation-⊃₁ Γ⊢φ⊃ψ∶Ω in
  let Γ⊢ψ∶Ω = generation-⊃₂ Γ⊢φ⊃ψ∶Ω in
  let A≡Ω = generation-⊃₃ Γ⊢φ⊃ψ∶Ω in
  change-type (⊃R Γ⊢φ∶Ω (subject-reduction-⇒ Γ⊢ψ∶Ω ψ⇒ψ')) (cong ty (≡-sym A≡Ω))
subject-reduction-⇒ {A = ψ} Γ⊢Λδε∶ψ (βP {ε = ε}) = 
  let φ' ,p ψ' ,p Γ⊢Λδ∶φ'⊃ψ' ,p Γ⊢ε∶φ' ,p ψ'≃ψ = generation-appP Γ⊢Λδε∶ψ in
  let χ ,p Γ,φ⊢δ∶χ ,p φ'⊃ψ'≃φ⊃χ = generation-ΛP Γ⊢Λδ∶φ'⊃ψ' in
  convPR (substitution Γ,φ⊢δ∶χ (context-validity Γ⊢Λδε∶ψ) (botSub-typed (convPR Γ⊢ε∶φ' (context-validityP (context-validity Γ,φ⊢δ∶χ)) 
    (≃-⊃-injl φ'⊃ψ'≃φ⊃χ)))) (prop-validity Γ⊢Λδε∶ψ) (let open EqReasoning (RSTCLOSE _⇒_) in 
    begin
      χ ⇑ ⟦ x₀:= ε ⟧
    ≡⟨ botSub-upRep χ ⟩
      χ
    ≈⟨⟨ ≃-⊃-injr φ'⊃ψ'≃φ⊃χ ⟩⟩
      ψ'
    ≈⟨ ψ'≃ψ ⟩
      ψ
    ∎)
subject-reduction-⇒ Γ⊢δε∶φ (appPl δ⇒δ') = 
  let ψ ,p φ' ,p Γ⊢δ∶ψ⊃φ' ,p Γ⊢ε∶ψ ,p φ'≃φ = generation-appP Γ⊢δε∶φ in 
  convPR (appPR (subject-reduction-⇒ Γ⊢δ∶ψ⊃φ' δ⇒δ') Γ⊢ε∶ψ) (prop-validity Γ⊢δε∶φ) φ'≃φ
subject-reduction-⇒ {Γ = Γ} Γ⊢reffM+∶φ (refdir {φ = M} {d = -plus}) = 
  let ψ ,p χ ,p Γ⊢reffM∶ψ≡χ ,p φ≃ψ⊃χ = generation-plus Γ⊢reffM+∶φ in
  let Γ⊢M∶Ω : Γ ⊢ M ∶ ty Ω
      Γ⊢M∶Ω = generation-reff₁ Γ⊢reffM∶ψ≡χ in
  convPR (ΛPR Γ⊢M∶Ω Γ⊢M∶Ω (varR x₀ (ctxPR Γ⊢M∶Ω))) (prop-validity Γ⊢reffM+∶φ) (trans (≃-imp (generation-reff₂ Γ⊢reffM∶ψ≡χ) (generation-reff₃ Γ⊢reffM∶ψ≡χ)) (sym φ≃ψ⊃χ))
subject-reduction-⇒ {Γ = Γ} Γ⊢reffM+∶φ (refdir {φ = M} {d = -minus}) = 
  let ψ ,p χ ,p Γ⊢reffM∶ψ≡χ ,p φ≃ψ⊃χ = generation-minus Γ⊢reffM+∶φ in
  let Γ⊢M∶Ω : Γ ⊢ M ∶ ty Ω
      Γ⊢M∶Ω = generation-reff₁ Γ⊢reffM∶ψ≡χ in
  convPR (ΛPR Γ⊢M∶Ω Γ⊢M∶Ω (varR x₀ (ctxPR Γ⊢M∶Ω))) (prop-validity Γ⊢reffM+∶φ) (trans (≃-imp (generation-reff₃ Γ⊢reffM∶ψ≡χ) (generation-reff₂ Γ⊢reffM∶ψ≡χ)) (sym φ≃ψ⊃χ))
subject-reduction-⇒ Γ⊢univδε+∶φ univplus = 
  let ψ ,p χ ,p Γ⊢univδε∶ψ≡χ ,p φ≃ψ⊃χ = generation-plus Γ⊢univδε+∶φ in 
  convPR (generation-univ₃ Γ⊢univδε∶ψ≡χ) (prop-validity Γ⊢univδε+∶φ) (trans (≃-imp (generation-univ₁ Γ⊢univδε∶ψ≡χ) (generation-univ₂ Γ⊢univδε∶ψ≡χ)) (sym φ≃ψ⊃χ))
subject-reduction-⇒ Γ⊢univδε-∶φ univminus = 
  let ψ ,p χ ,p Γ⊢univδε∶ψ≡χ ,p φ≃χ⊃ψ = generation-minus Γ⊢univδε-∶φ in 
  convPR (generation-univ₄ Γ⊢univδε∶ψ≡χ) (prop-validity Γ⊢univδε-∶φ) (trans (≃-imp (generation-univ₂ Γ⊢univδε∶ψ≡χ) (generation-univ₁ Γ⊢univδε∶ψ≡χ)) (sym φ≃χ⊃ψ))
subject-reduction-⇒ Γ⊢P+∶φ (dirR {d = -plus} P⇒Q) = 
  let ψ ,p χ ,p Γ⊢P∶ψ≡χ ,p φ≃ψ⊃χ = generation-plus Γ⊢P+∶φ in 
  convPR (plusR (subject-reduction-⇒ Γ⊢P∶ψ≡χ P⇒Q)) (prop-validity Γ⊢P+∶φ) (sym φ≃ψ⊃χ)
subject-reduction-⇒ Γ⊢P-∶φ (dirR {d = -minus} P⇒Q) =
  let ψ ,p χ ,p Γ⊢P∶ψ≡χ ,p φ≃χ⊃ψ = generation-minus Γ⊢P-∶φ in 
  convPR (minusR (subject-reduction-⇒ Γ⊢P∶ψ≡χ P⇒Q)) (prop-validity Γ⊢P-∶φ) (sym φ≃χ⊃ψ)
subject-reduction-⇒ {Γ = Γ} {A = app (-eq B) (L ∷ L' ∷ [])} Γ⊢ΛPQ∶L≡L' (βE {A = A} {M} {N} {P} {Q}) = 
  let C ,p F ,p G ,p Γ⊢ΛP∶F≡G ,p Γ⊢Q∶M≡N ,p FM≃L ,p GN≃L' = generation-app* Γ⊢ΛPQ∶L≡L' in
  let D ,p ΓAAE⊢P∶Fx≡Gy ,p C⇛B≡A⇛D = generation-λλλ Γ⊢ΛP∶F≡G in
  let C≡A : C ≡ A
      C≡A = ⇛-injl C⇛B≡A⇛D in
  let tyC≡tyA : ty C ≡ ty A
      tyC≡tyA = cong ty C≡A in
  convER (substitution (subst (λ x → addpath Γ A ⊢ P ∶ appT (F ⇑ ⇑ ⇑) (var x₂) ≡〈 x 〉 appT (G ⇑ ⇑ ⇑) (var x₁)) 
    (≡-sym (⇛-injr C⇛B≡A⇛D)) 
    ΓAAE⊢P∶Fx≡Gy) 
    (context-validity Γ⊢ΛPQ∶L≡L') 
    (botSub₃-typed (change-type (eq-validity₁ Γ⊢Q∶M≡N refl) tyC≡tyA) 
      (change-type (eq-validity₂ Γ⊢Q∶M≡N refl) tyC≡tyA) 
      (subst (λ x → Γ ⊢ Q ∶ M ≡〈 x 〉 N) C≡A Γ⊢Q∶M≡N))) 
    (eq-validity₁ Γ⊢ΛPQ∶L≡L' refl) 
    (eq-validity₂ Γ⊢ΛPQ∶L≡L' refl) 
    (subst₂ _≃_ (cong₂ appT (≡-sym botSub-upRep₃) refl) refl FM≃L) 
    (subst₂ _≃_ (cong₂ appT (≡-sym botSub-upRep₃) refl) refl GN≃L')
subject-reduction-⇒ {Γ = Γ} {A = app (-eq A) (M ∷ M' ∷ [])} Γ⊢refΛLP∶M≡M' (βPP {A = C} {M = L} {N = N} {N' = N'} {P = P}) =
  let B ,p F ,p G ,p Γ⊢refΛL∶F≡G ,p Γ⊢P∶N≡N' ,p FN≃M ,p GN'≃M' = generation-app* Γ⊢refΛLP∶M≡M' in
  let Γ⊢ΛL∶B⇛A : Γ ⊢ ΛT C L ∶ ty (B ⇛ A)
      Γ⊢ΛL∶B⇛A = generation-reff₁ Γ⊢refΛL∶F≡G in
  let ΛL≃F : ΛT C L ≃ F
      ΛL≃F = generation-reff₂ Γ⊢refΛL∶F≡G in
  let ΛL≃G : ΛT C L ≃ G
      ΛL≃G = generation-reff₃ Γ⊢refΛL∶F≡G in
  let D ,p ΓC⊢L∶D ,p B⇛A≡C⇛D = generation-ΛT Γ⊢ΛL∶B⇛A in
  let B≡C : B ≡ C
      B≡C = ⇛-injl B⇛A≡C⇛D in
  let Γ⊢P∶N≡〈C〉N' : Γ ⊢ P ∶ N ≡〈 C 〉 N'
      Γ⊢P∶N≡〈C〉N' = subst (λ x → Γ ⊢ P ∶ N ≡〈 x 〉 N') B≡C Γ⊢P∶N≡N' in
  let A≡D : A ≡ D
      A≡D = ⇛-injr B⇛A≡C⇛D in
  subst (λ x → Γ ⊢ L ⟦⟦ x₀::= P ∶ x₀:= N ≡ x₀:= N' ⟧⟧ ∶ M ≡〈 x 〉 M')
    (≡-sym A≡D) 
    (convER (path-substitution ΓC⊢L∶D (botPathSub-typed Γ⊢P∶N≡〈C〉N') 
    (botSub-typed (eq-validity₁ Γ⊢P∶N≡〈C〉N' refl)) (botSub-typed (eq-validity₂ Γ⊢P∶N≡〈C〉N' refl)) (context-validity Γ⊢refΛLP∶M≡M')) 
    (change-type (eq-validity₁ Γ⊢refΛLP∶M≡M' refl) (cong ty A≡D)) 
    (change-type (eq-validity₂ Γ⊢refΛLP∶M≡M' refl) (cong ty A≡D)) 
    (trans (trans (sym (inc βT)) (≃-appTl ΛL≃F)) FN≃M) 
    (trans (trans (sym (inc βT)) (≃-appTl ΛL≃G)) GN'≃M'))
subject-reduction-⇒ Γ⊢E∶A ref⊃* = {!!}
subject-reduction-⇒ Γ⊢E∶A ref⊃*univ = {!!}
subject-reduction-⇒ Γ⊢E∶A univ⊃*ref = {!!}
subject-reduction-⇒ Γ⊢E∶A univ⊃*univ = {!!}
subject-reduction-⇒ Γ⊢E∶A (imp*l E⇒F) = {!!}
subject-reduction-⇒ Γ⊢E∶A (imp*r E⇒F) = {!!}
subject-reduction-⇒ Γ⊢E∶A (app*l E⇒F) = {!!}
subject-reduction-⇒ Γ⊢E∶A (reffR E⇒F) = {!!}

postulate subject-reduction : ∀ {V} {K} {Γ}
                            {E F : Expression V (varKind K)} {A} → 
                            (Γ ⊢ E ∶ A) → (E ↠ F) → (Γ ⊢ F ∶ A)

app*R' : ∀ {V} {Γ : Context V} {P Q : Path V} {M M' N N' : Term V} {A B : Type} →
    Γ ⊢ P ∶ M ≡〈 A ⇛ B 〉 M' → Γ ⊢ Q ∶ N ≡〈 A 〉 N' →
  -------------------------------------------------
    Γ ⊢ app* N N' P Q ∶ appT M N ≡〈 B 〉 appT M' N'
app*R' Γ⊢P∶M≡M' Γ⊢Q∶N≡N' = appER (eq-validity₁ Γ⊢Q∶N≡N' refl) (eq-validity₂ Γ⊢Q∶N≡N' refl) Γ⊢P∶M≡M' Γ⊢Q∶N≡N'
