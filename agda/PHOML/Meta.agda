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
liftPathSub-typed {Γ = Γ} {A = A} τ∶ρ≡σ validΓ (↑ x) = subst₄ (λ x₃ y z w → addpath Γ A ⊢ x₃ ∶ y ≡〈 z 〉 w) {!!} {!!} {!!} {!!} 
  (weakening (τ∶ρ≡σ x) (valid-addpath validΓ) {!!})

path-substitution : ∀ {U} {V} {Γ : Context U} {Δ : Context V} 
  {ρ} {σ} {τ} {M} {A} →
  Γ ⊢ M ∶ A → τ ∶ ρ ≡ σ ∶ Δ ⟶ Γ →
  ρ ∶ Δ ⟶ Γ → σ ∶ Δ ⟶ Γ → 
  valid Δ → 
  Δ ⊢ M ⟦⟦ τ ∶ ρ ≡ σ ⟧⟧ ∶ M ⟦ ρ ⟧ ≡〈 yt A 〉 M ⟦ σ ⟧
path-substitution (varR x _) τ∶ρ≡σ _ _ _ = τ∶ρ≡σ x
path-substitution (appTR Γ⊢M∶A⇛B Γ⊢N∶A) τ∶ρ≡σ ρ∶Δ⟶Γ σ∶Δ⟶Γ validΔ = 
  appER (substitution Γ⊢N∶A validΔ ρ∶Δ⟶Γ) (substitution Γ⊢N∶A validΔ σ∶Δ⟶Γ) (path-substitution Γ⊢M∶A⇛B τ∶ρ≡σ ρ∶Δ⟶Γ σ∶Δ⟶Γ validΔ) 
    (path-substitution Γ⊢N∶A τ∶ρ≡σ ρ∶Δ⟶Γ σ∶Δ⟶Γ validΔ)
path-substitution (ΛTR Γ,A⊢M∶B) τ∶ρ≡σ ρ∶Δ⟶Γ σ∶Δ⟶Γ validΔ = lllR (ΛTR (substitution Γ,A⊢M∶B (ctxTR validΔ) (liftSub-typed ρ∶Δ⟶Γ (ctxTR validΔ)))) 
  (ΛTR (substitution Γ,A⊢M∶B (ctxTR validΔ) (liftSub-typed σ∶Δ⟶Γ (ctxTR validΔ)))) 
  (convER (path-substitution Γ,A⊢M∶B {!liftPathSub-typed!} {!!} {!!} {!!}) {!!} {!!} {!!} {!!})
path-substitution (⊥R validΓ) τ∶ρ≡σ ρ∶Δ⟶Γ σ∶Δ⟶Γ validΔ = {!!}
path-substitution (⊃R Γ⊢M∶A Γ⊢M∶A₁) τ∶ρ≡σ ρ∶Δ⟶Γ σ∶Δ⟶Γ validΔ = {!!}
{- path-substitution (varR x validΓ) τ∶ρ≡σ _ _ _ = τ∶ρ≡σ x
path-substitution (⊥R validΓ) _ _ _ validΔ = refR (⊥R validΔ)
path-substitution (⊃R Γ⊢φ∶Ω Γ⊢ψ∶Ω) τ∶ρ≡σ ρ∶Γ⇒Δ σ∶Γ⇒Δ validΔ = ⊃*R (path-substitution Γ⊢φ∶Ω τ∶ρ≡σ ρ∶Γ⇒Δ σ∶Γ⇒Δ validΔ) (path-substitution Γ⊢ψ∶Ω τ∶ρ≡σ ρ∶Γ⇒Δ σ∶Γ⇒Δ validΔ)
path-substitution (appR {A = A} Γ⊢M∶A⇛B Γ⊢N∶A) τ∶σ≡σ' ρ∶Γ⇒Δ σ∶Γ⇒Δ validΔ = 
  app*R (substitution Γ⊢N∶A validΔ ρ∶Γ⇒Δ) (substitution Γ⊢N∶A validΔ σ∶Γ⇒Δ)
  (path-substitution Γ⊢M∶A⇛B τ∶σ≡σ' ρ∶Γ⇒Δ σ∶Γ⇒Δ validΔ) (path-substitution Γ⊢N∶A τ∶σ≡σ' ρ∶Γ⇒Δ σ∶Γ⇒Δ validΔ)
path-substitution {U} {V} {Γ} {Δ} {ρ} {σ} {τ} (ΛTR .{U} .{Γ} {A} {M} {B} Γ,A⊢M∶B) τ∶σ≡σ' ρ∶Γ⇒Δ σ∶Γ⇒Δ validΔ = 
  let ΔAAE = Δ ,T A ,T A ,E var x₁ ≡〈 A 〉 var x₀ in
  let validΔAA  : valid (Δ ,T A ,T A)
      validΔAA = ctxTR (ctxTR validΔ) in
  let validΔAAE : valid ΔAAE
      validΔAAE = ctxER (varR x₁ validΔAA) (varR x₀ validΔAA) in
  let Mσ-typed : ∀ {σ} {x} → σ ∶ Γ ⇒ Δ → typeof x ΔAAE ≡ ty A → ΔAAE ⊢ appT ((ΛT A M) ⟦ σ ⟧ ⇑ ⇑ ⇑) (var x) ∶ ty B
      Mσ-typed = λ {σ} {x} σ∶Γ⇒Δ x∶A∈ΔAAE → appR (weakening-addpath (substitution (ΛTR Γ,A⊢M∶B) validΔ σ∶Γ⇒Δ)) (change-type (varR x (valid-addpath validΔ)) x∶A∈ΔAAE) in
  let step1 : Δ ,T A ,T A ,E var x₁ ≡〈 A 〉 var x₀ ⊢ 
              M ⟦⟦ liftPathSub τ ∶ sub↖ ρ ≡ sub↗ σ ⟧⟧ ∶ 
              appT ((ΛT A M) ⟦ ρ ⟧ ⇑ ⇑ ⇑) (var x₂) ≡〈 B 〉 appT ((ΛT A M) ⟦ σ ⟧ ⇑ ⇑ ⇑) (var x₁)
      step1 = convER 
              (path-substitution Γ,A⊢M∶B 
                (liftPathSub-typed τ∶σ≡σ' validΔ) 
                (sub↖-typed ρ∶Γ⇒Δ) (sub↗-typed σ∶Γ⇒Δ) validΔAAE) 
                (Mσ-typed ρ∶Γ⇒Δ refl) (Mσ-typed σ∶Γ⇒Δ refl) 
                (sym (inc (subst (λ x → appT ((ΛT A M ⟦ ρ ⟧) ⇑ ⇑ ⇑) (var x₂) ⇒ x) (let open ≡-Reasoning in 
              begin
                M ⟦ liftSub _ ρ ⟧ 〈 liftRep _ upRep 〉 〈 liftRep _ upRep 〉 〈 liftRep _ upRep 〉 ⟦ x₀:= var x₂ ⟧
              ≡⟨ sub↖-decomp M ⟩
                M ⟦ sub↖ ρ ⟧
              ∎) βT))) (sym (inc (subst (λ x → appT ((ΛT A M ⟦ σ ⟧) ⇑ ⇑ ⇑) (var x₁) ⇒ x) (sub↗-decomp M) {!!}))) -}
{- convER 
               (path-substitution Γ,A⊢M∶B 
                 (liftPathSub-typed τ∶σ≡σ' validΔ) (sub↖-typed ρ∶Γ⇒Δ) (sub↗-typed σ∶Γ⇒Δ) 
                 validΔAAE)
                 (Mσ-typed ρ∶Γ⇒Δ refl)
                 (Mσ-typed σ∶Γ⇒Δ refl)
                 (RSTClose.sym (redex-conv (subst (R -appTerm ((ΛT A M ⟦ ρ ⟧) ⇑ ⇑ ⇑ ∷ var x₂ ∷ [])) (sub↖-decomp M) (βR βT)))) (RSTClose.sym (redex-conv (subst (R -appTerm ((ΛT A M ⟦ σ ⟧) ⇑ ⇑ ⇑ ∷ var x₁ ∷ [])) (sub↗-decomp M) (βR βT)))) -}
--  in lllR step1

generation-ΛP : ∀ {V} {Γ : Context V} {φ δ ψ} →
  Γ ⊢ ΛP φ δ ∶ ψ → Σ[ χ ∈ Term V ] Γ ,P φ ⊢ δ ∶ χ ⇑ × ψ ≃ φ ⊃ χ
generation-ΛP (ΛPR _ _ Γ,φ⊢δ∶ψ) = _ ,p Γ,φ⊢δ∶ψ ,p ref
generation-ΛP (convPR Γ⊢Λδ∶ψ Γ⊢ψ'∶Ω ψ≃ψ') =
  let χ ,p Γ,φ⊢δ∶χ ,p χ≃φ⊃ψ = generation-ΛP Γ⊢Λδ∶ψ in 
  χ ,p Γ,φ⊢δ∶χ ,p trans (sym ψ≃ψ') χ≃φ⊃ψ

context-validityP : ∀ {V} {Γ : Context V} {φ} → valid (Γ ,P φ) → Γ ⊢ φ ∶ ty Ω
context-validityP (ctxPR Γ⊢φ∶Ω) = Γ⊢φ∶Ω

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
subject-reduction-⇒ Γ⊢Λδε∶ψ (βP {ε = ε}) = 
  let φ' ,p ψ' ,p Γ⊢Λδ∶φ'⊃ψ' ,p Γ⊢ε∶φ' ,p ψ'≃ψ = generation-appP Γ⊢Λδε∶ψ in
  let χ ,p Γ,φ⊢δ∶χ ,p φ⊃χ≃φ'⊃ψ' = generation-ΛP Γ⊢Λδ∶φ'⊃ψ' in
  change-type (substitution Γ,φ⊢δ∶χ (context-validity Γ⊢Λδε∶ψ) (botSub-typed (convPR Γ⊢ε∶φ' {!!} {!!}))) {!!}
subject-reduction-⇒ Γ⊢E∶A (appPl E⇒F) = {!!}
subject-reduction-⇒ Γ⊢E∶A refdir = {!!}
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
