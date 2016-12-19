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
open import PHOML.Meta.TypeVal public

_∶_≡_∶_⟶_ : ∀ {U V} → PathSub U V → Sub U V → Sub U V → Context V → Context U → Set
τ ∶ ρ ≡ σ ∶ Γ ⟶ Δ = ∀ x → Γ ⊢ τ x ∶ ρ _ x ≡〈 typeof' x Δ 〉 σ _ x

liftPathSub-typed : ∀ {U V} {τ : PathSub U V} {ρ σ Γ Δ A} →
  τ ∶ ρ ≡ σ ∶ Γ ⟶ Δ → valid Γ → liftPathSub τ ∶ sub↖ ρ ≡ sub↗ σ ∶ addpath Γ A ⟶ Δ ,T A
liftPathSub-typed τ∶ρ≡σ validΓ x₀ = varR x₀ (valid-addpath validΓ)
liftPathSub-typed {τ = τ} {ρ} {σ} {Γ = Γ} {Δ} {A = A} τ∶ρ≡σ validΓ (↑ x) = subst₄ (λ x₃ y z w → addpath Γ A ⊢ x₃ ∶ y ≡〈 z 〉 w) 
  (rep-•R₃ (τ x)) (rep-•R₃ (ρ -Term x)) (≡-sym (yt-rep (typeof x Δ))) (rep-•R₃ (σ -Term x)) 
  (weakening (τ∶ρ≡σ x) (valid-addpath validΓ) (upRep₃-addpath-typed A))

path-substitution : ∀ {U} {V} {Γ : Context U} {Δ : Context V} 
  {ρ} {σ} {τ} {M} {A} →
  Γ ⊢ M ∶ A → τ ∶ ρ ≡ σ ∶ Δ ⟶ Γ →
  ρ ∶ Δ ⟶ Γ → σ ∶ Δ ⟶ Γ → 
  valid Δ → 
  Δ ⊢ M ⟦⟦ τ ∶ ρ ≡ σ ⟧⟧ ∶ M ⟦ ρ ⟧ ≡〈 yt A 〉 M ⟦ σ ⟧
path-substitution (varR x _) τ∶ρ≡σ _ _ _ = τ∶ρ≡σ x
path-substitution (appTR {A = A} Γ⊢M∶A⇛B Γ⊢N∶A) τ∶ρ≡σ ρ∶Δ⟶Γ σ∶Δ⟶Γ validΔ = 
  appER (substitution Γ⊢N∶A validΔ ρ∶Δ⟶Γ) (substitution Γ⊢N∶A validΔ σ∶Δ⟶Γ) (path-substitution Γ⊢M∶A⇛B τ∶ρ≡σ ρ∶Δ⟶Γ σ∶Δ⟶Γ validΔ) 
    (path-substitution Γ⊢N∶A τ∶ρ≡σ ρ∶Δ⟶Γ σ∶Δ⟶Γ validΔ)
path-substitution {Δ = Δ} {ρ} {σ} (ΛTR {A = A} {M = M} Γ,A⊢M∶B) τ∶ρ≡σ ρ∶Δ⟶Γ σ∶Δ⟶Γ validΔ = lllR (ΛTR (substitution Γ,A⊢M∶B (ctxTR validΔ) (liftSub-typed ρ∶Δ⟶Γ (ctxTR validΔ)))) 
  (ΛTR (substitution Γ,A⊢M∶B (ctxTR validΔ) (liftSub-typed σ∶Δ⟶Γ (ctxTR validΔ)))) 
  (convER (path-substitution Γ,A⊢M∶B (liftPathSub-typed τ∶ρ≡σ validΔ) (sub↖-typed ρ∶Δ⟶Γ validΔ) (sub↗-typed σ∶Δ⟶Γ validΔ) (valid-addpath validΔ)) 
  (appTR (ΛTR (weakening (weakening (weakening (substitution Γ,A⊢M∶B (ctxTR validΔ) 
                                               (liftSub-typed ρ∶Δ⟶Γ (ctxTR validΔ))) 
                                    (ctxTR (ctxTR validΔ))
                                    (liftRep-typed (upRep-typed (ty A)))) 
                         (ctxTR (ctxTR (ctxTR validΔ))) 
                         (liftRep-typed (upRep-typed (ty A)))) 
              (ctxTR (valid-addpath validΔ)) 
              (liftRep-typed (upRep-typed (var x₁ ≡〈 A 〉 var x₀))))) 
         (varR x₂ (valid-addpath validΔ))) 
  (appTR (ΛTR (weakening (weakening (weakening (substitution Γ,A⊢M∶B (ctxTR validΔ) 
                                               (liftSub-typed σ∶Δ⟶Γ (ctxTR validΔ))) 
                                    (ctxTR (ctxTR validΔ))
                                    (liftRep-typed (upRep-typed (ty A)))) 
                         (ctxTR (ctxTR (ctxTR validΔ))) 
                         (liftRep-typed (upRep-typed (ty A)))) 
              (ctxTR (valid-addpath validΔ)) 
              (liftRep-typed (upRep-typed (var x₁ ≡〈 A 〉 var x₀))))) 
         (varR x₁ (valid-addpath validΔ))) 
  (sym (inc (subst
               (λ x → appT (ΛT A (M ⟦ liftSub -Term ρ ⟧) ⇑ ⇑ ⇑) (var x₂) ⇒ x) 
            (≡-sym (sub↖-decomp {E = M})) βT))) 
  (sym (inc (subst
               (λ x → appT (ΛT A (M ⟦ liftSub -Term σ ⟧) ⇑ ⇑ ⇑) (var x₁) ⇒ x) 
            (≡-sym (sub↗-decomp {E = M})) βT))))
path-substitution (⊥R _) _ _ _ validΔ = refR (⊥R validΔ)
path-substitution (⊃R Γ⊢φ∶Ω Γ⊢ψ∶Ω) τ∶ρ≡σ ρ∶Δ⟶Γ σ∶Δ⟶Γ validΔ = ⊃*R 
  (path-substitution Γ⊢φ∶Ω τ∶ρ≡σ ρ∶Δ⟶Γ σ∶Δ⟶Γ validΔ) 
  (path-substitution Γ⊢ψ∶Ω τ∶ρ≡σ ρ∶Δ⟶Γ σ∶Δ⟶Γ validΔ)

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
subject-reduction-⇒ Γ⊢E∶A univplus = {!!}
subject-reduction-⇒ Γ⊢E∶A univminus = {!!}
subject-reduction-⇒ Γ⊢E∶A (dirR E⇒F) = {!!}
subject-reduction-⇒ Γ⊢E∶A βE = {!!}
subject-reduction-⇒ Γ⊢E∶A βPP = {!!}
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
