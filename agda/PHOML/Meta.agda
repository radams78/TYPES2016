module PHOML.Meta where
open import Data.Product renaming (_,_ to _,p_)
open import Prelims
open import PHOML.Grammar
open import PHOML.Red
open import PHOML.Rules
open import PHOML.PathSub
open import PHOML.Meta.ConVal public
open import PHOML.Meta.Gen public

prop-validity : ∀ {V} {Γ : Context V} {δ : Proof V} {φ : Term V} → Γ ⊢ δ ∶ φ → Γ ⊢ φ ∶ ty Ω
eq-validity₁ : ∀ {V} {Γ : Context V} {P : Path V} {E M A N} → Γ ⊢ P ∶ E → E ≡ M ≡〈 A 〉 N → Γ ⊢ M ∶ ty A
eq-validity₂ : ∀ {V} {Γ : Context V} {P : Path V} {E M A N} → Γ ⊢ P ∶ E → E ≡ M ≡〈 A 〉 N → Γ ⊢ N ∶ ty A

prop-validity (varR _ validΓ) = context-validity-Prop validΓ
prop-validity (appPR Γ⊢δ∶φ⊃ψ _) = generation-⊃₂ (prop-validity Γ⊢δ∶φ⊃ψ)
prop-validity (ΛPR Γ⊢φ∶Ω Γ⊢ψ∶Ω _) = ⊃R Γ⊢φ∶Ω Γ⊢ψ∶Ω
prop-validity (convR _ Γ⊢φ∶Ω _) = Γ⊢φ∶Ω
prop-validity (plusR Γ⊢P∶φ≡ψ) = ⊃R (eq-validity₁ Γ⊢P∶φ≡ψ refl) (eq-validity₂ Γ⊢P∶φ≡ψ refl)
prop-validity (minusR Γ⊢P∶φ≡ψ) = ⊃R (eq-validity₂ Γ⊢P∶φ≡ψ refl) (eq-validity₁ Γ⊢P∶φ≡ψ refl)

eq-validity₁ (varR {Γ = Γ} _ validΓ) E≡M≡N = subst (λ E → Γ ⊢ left E ∶ ty (type E)) E≡M≡N (context-validity-Eq₁ validΓ)
eq-validity₁ {Γ = Γ} (refR Γ⊢P∶M≡N) E≡M≡N = subst₂ (λ x y → Γ ⊢ x ∶ ty y) (eq-inj₁ E≡M≡N) (eq-inj₂ E≡M≡N) Γ⊢P∶M≡N
eq-validity₁ {Γ = Γ} (⊃*R Γ⊢P∶φ≡φ' Γ⊢Q∶ψ≡ψ') E≡φ⊃ψ≡φ'⊃ψ' = subst₂ (λ x y → Γ ⊢ x ∶ ty y) (eq-inj₁ E≡φ⊃ψ≡φ'⊃ψ') (eq-inj₂ E≡φ⊃ψ≡φ'⊃ψ') (⊃R (eq-validity₁ Γ⊢P∶φ≡φ' refl) (eq-validity₁ Γ⊢Q∶ψ≡ψ' refl))
eq-validity₁ {Γ = Γ} (univR Γ⊢δ∶φ⊃ψ Γ⊢ε∶ψ⊃φ) E≡φ≡ψ = subst₂ (λ x y → Γ ⊢ x ∶ ty y) (eq-inj₁ E≡φ≡ψ) (eq-inj₂ E≡φ≡ψ) (generation-⊃₂ (prop-validity Γ⊢ε∶ψ⊃φ))
eq-validity₁ {Γ = Γ} (lllR Γ⊢M∶A _ _) E≡M≡N = subst₂ (λ x y → Γ ⊢ x ∶ ty y) (eq-inj₁ E≡M≡N) (eq-inj₂ E≡M≡N) Γ⊢M∶A
eq-validity₁ {Γ = Γ} (app*R Γ⊢N∶A Γ⊢N'∶A Γ⊢P∶M≡M' Γ⊢Q∶N≡N') E≡M≡N = subst₂ (λ x y → Γ ⊢ x ∶ ty y) (eq-inj₁ E≡M≡N) (eq-inj₂ E≡M≡N) (appR (eq-validity₁ Γ⊢P∶M≡M' refl) Γ⊢N∶A)
eq-validity₁ {Γ = Γ} (convER Γ⊢P∶M≡N Γ⊢M'∶A Γ⊢N'∶A M≃M' N≃N') E≡M≡N = subst₂ (λ x y → Γ ⊢ x ∶ ty y) (eq-inj₁ E≡M≡N) (eq-inj₂ E≡M≡N) Γ⊢M'∶A

eq-validity₂ {Γ = Γ} (varR _ validΓ) E≡M≡N = subst (λ E → Γ ⊢ right E ∶ ty (type E)) E≡M≡N (context-validity-Eq₂ validΓ)
eq-validity₂ {Γ = Γ} (refR Γ⊢M∶A) E≡M≡N = subst₂ (λ x y → Γ ⊢ x ∶ ty y) (eq-inj₃ E≡M≡N) (eq-inj₂ E≡M≡N) Γ⊢M∶A
eq-validity₂ {Γ = Γ} (⊃*R Γ⊢P∶φ≡ψ Γ⊢Q∶φ'≡ψ') E≡M≡N = subst₂ (λ x y → Γ ⊢ x ∶ ty y) (eq-inj₃ E≡M≡N) (eq-inj₂ E≡M≡N) (⊃R (eq-validity₂ Γ⊢P∶φ≡ψ refl) (eq-validity₂ Γ⊢Q∶φ'≡ψ' refl))
eq-validity₂ {Γ = Γ} (univR Γ⊢δ∶φ⊃ψ Γ⊢ε∶ψ⊃φ) E≡M≡N = subst₂ (λ x y → Γ ⊢ x ∶ ty y) (eq-inj₃ E≡M≡N) (eq-inj₂ E≡M≡N) (generation-⊃₂ (prop-validity Γ⊢δ∶φ⊃ψ))
eq-validity₂ {Γ = Γ} (lllR _ Γ⊢N∶A⇛B _) E≡M≡N = subst₂ (λ x y → Γ ⊢ x ∶ ty y) (eq-inj₃ E≡M≡N) (eq-inj₂ E≡M≡N) Γ⊢N∶A⇛B
eq-validity₂ {Γ = Γ} (app*R Γ⊢N∶A Γ⊢N'∶A Γ⊢P∶M≡M' Γ⊢Q∶N≡N') E≡M≡N = subst₂ (λ x y → Γ ⊢ x ∶ ty y) (eq-inj₃ E≡M≡N) (eq-inj₂ E≡M≡N) (appR (eq-validity₂ Γ⊢P∶M≡M' refl) Γ⊢N'∶A)
eq-validity₂ {Γ = Γ} (convER _ _ Γ⊢N'∶A _ _) E≡M≡N = subst₂ (λ x y → Γ ⊢ x ∶ ty y) (eq-inj₃ E≡M≡N) (eq-inj₂ E≡M≡N) Γ⊢N'∶A

_∶_⟶_ : ∀ {U V} → Sub U V → Context V → Context U → Set
_∶_⟶_ {U} {V} σ Γ Δ = ∀ {K} (x : Var U K) → Γ ⊢ σ _ x ∶ typeof x Δ ⟦ σ ⟧

_∶_≡_∶_⟶_ : ∀ {U V} → PathSub U V → Sub U V → Sub U V → Context V → Context U → Set
τ ∶ ρ ≡ σ ∶ Γ ⟶ Δ = ∀ x → Γ ⊢ τ x ∶ ρ _ x ≡〈 typeof' x Δ 〉 σ _ x

postulate substitution : ∀ {U} {V} {σ : Sub U V} {K}
                       {Γ : Context U} {M : Expression U (varKind K)} {A} {Δ} →
                       Γ ⊢ M ∶ A → valid Δ → σ ∶ Δ ⟶ Γ → Δ ⊢ M ⟦ σ ⟧ ∶ A ⟦ σ ⟧

postulate ⊃-gen₁ : ∀ {V} {Γ : Context V} {φ} {ψ} → Γ ⊢ φ ⊃ ψ ∶ ty Ω → Γ ⊢ φ ∶ ty Ω

postulate Type-Reduction : ∀ {V} {Γ : Context V} {K} {M : Expression V (varKind K)} {A} {B} →
                         Γ ⊢ M ∶ A → A ↠ B → Γ ⊢ M ∶ B

postulate path-substitution : ∀ {U} {V} {Γ : Context U} {Δ : Context V} 
                            {ρ} {σ} {τ} {M} {A} →
                            (Γ ⊢ M ∶ A) → (τ ∶ ρ ≡ σ ∶ Δ ⟶ Γ) →
                            (ρ ∶ Δ ⟶ Γ) → (σ ∶ Δ ⟶ Γ) → 
                            valid Δ → 
                            Δ ⊢ M ⟦⟦ τ ∶ ρ ≡ σ ⟧⟧ ∶ M ⟦ ρ ⟧ ≡〈 yt A 〉 M ⟦ σ ⟧
{- path-substitution (varR x validΓ) τ∶ρ≡σ _ _ _ = τ∶ρ≡σ x
path-substitution (⊥R validΓ) _ _ _ validΔ = refR (⊥R validΔ)
path-substitution (⊃R Γ⊢φ∶Ω Γ⊢ψ∶Ω) τ∶ρ≡σ ρ∶Γ⇒Δ σ∶Γ⇒Δ validΔ = ⊃*R (path-substitution Γ⊢φ∶Ω τ∶ρ≡σ ρ∶Γ⇒Δ σ∶Γ⇒Δ validΔ) (path-substitution Γ⊢ψ∶Ω τ∶ρ≡σ ρ∶Γ⇒Δ σ∶Γ⇒Δ validΔ)
path-substitution (appR {A = A} Γ⊢M∶A⇛B Γ⊢N∶A) τ∶σ≡σ' ρ∶Γ⇒Δ σ∶Γ⇒Δ validΔ = 
  app*R (substitution Γ⊢N∶A validΔ ρ∶Γ⇒Δ) (substitution Γ⊢N∶A validΔ σ∶Γ⇒Δ)
  (path-substitution Γ⊢M∶A⇛B τ∶σ≡σ' ρ∶Γ⇒Δ σ∶Γ⇒Δ validΔ) (path-substitution Γ⊢N∶A τ∶σ≡σ' ρ∶Γ⇒Δ σ∶Γ⇒Δ validΔ)
path-substitution {U} {V} {Γ} {Δ} {ρ} {σ} {τ} (ΛR .{U} .{Γ} {A} {M} {B} Γ,A⊢M∶B) τ∶σ≡σ' ρ∶Γ⇒Δ σ∶Γ⇒Δ validΔ = 
  let ΔAAE = Δ ,T A ,T A ,E var x₁ ≡〈 A 〉 var x₀ in
  let validΔAA  : valid (Δ ,T A ,T A)
      validΔAA = ctxTR (ctxTR validΔ) in
  let validΔAAE : valid ΔAAE
      validΔAAE = ctxER (varR x₁ validΔAA) (varR x₀ validΔAA) in
  let Mσ-typed : ∀ {σ} {x} → σ ∶ Γ ⇒ Δ → typeof x ΔAAE ≡ ty A → ΔAAE ⊢ appT ((ΛT A M) ⟦ σ ⟧ ⇑ ⇑ ⇑) (var x) ∶ ty B
      Mσ-typed = λ {σ} {x} σ∶Γ⇒Δ x∶A∈ΔAAE → appR (weakening-addpath (substitution (ΛR Γ,A⊢M∶B) validΔ σ∶Γ⇒Δ)) (change-type (varR x (valid-addpath validΔ)) x∶A∈ΔAAE) in
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

generation-ΛT : ∀ {V} {Γ : Context V} {A M B} →
  Γ ⊢ ΛT A M ∶ ty B → Σ[ C ∈ Type ] Γ ,T A ⊢ M ∶ ty C × B ≡ A ⇛ C
generation-ΛT (ΛR {B = B} Γ,A⊢M∶B) = B ,p Γ,A⊢M∶B ,p refl

botSub-typed : ∀ {V} {M : Term V} {Γ A} →
  Γ ⊢ M ∶ ty A → x₀:= M ∶ Γ ⟶ Γ ,T A
botSub-typed {V} {M} {Γ} {A} Γ⊢M∶A x₀ = change-type Γ⊢M∶A (≡-sym (botSub-upRep (ty A) {M}))
botSub-typed {Γ = Γ} Γ⊢M∶A (↑ x) = change-type (varR x (context-validity Γ⊢M∶A)) (≡-sym (botSub-upRep (typeof x Γ)))

⇛-injl : ∀ {A A' B B' : Type} → A ⇛ B ≡ A' ⇛ B' → A ≡ A'
⇛-injl refl = refl

⇛-injr : ∀ {A A' B B' : Type} → A ⇛ B ≡ A' ⇛ B' → B ≡ B'
⇛-injr refl = refl

subject-reduction-⇒ : ∀ {V} {K} {E F : Expression V (varKind K)} {Γ} {A} →
  Γ ⊢ E ∶ A → E ⇒ F → Γ ⊢ F ∶ A
subject-reduction-⇒ {A = app (-ty B) []} Γ⊢ΛMN∶B βT = 
  let C ,p Γ⊢ΛM∶C⇛B ,p Γ⊢N∶C = generation-appT Γ⊢ΛMN∶B in
  let D ,p Γ,A⊢M∶D ,p C⇛B≡A⇛D = generation-ΛT Γ⊢ΛM∶C⇛B in
  change-type (substitution Γ,A⊢M∶D (context-validity Γ⊢ΛMN∶B) (botSub-typed (change-type Γ⊢N∶C (cong ty (⇛-injl C⇛B≡A⇛D))))) 
  (cong ty (≡-sym {!⇛-injr C⇛B≡A⇛D!}))
subject-reduction-⇒ Γ⊢E∶A (appTl E⇒F) = {!!}
subject-reduction-⇒ Γ⊢E∶A (impl E⇒F) = {!!}
subject-reduction-⇒ Γ⊢E∶A (impr E⇒F) = {!!}
subject-reduction-⇒ Γ⊢E∶A βP = {!!}
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

postulate equation-validity₁ : ∀ {V} {Γ : Context V} {P : Path V} {M} {A} {N} →
                             Γ ⊢ P ∶ M ≡〈 A 〉 N → Γ ⊢ M ∶ ty A

postulate equation-validity₂ : ∀ {V} {Γ : Context V} {P : Path V} {M} {A} {N} →
                             Γ ⊢ P ∶ M ≡〈 A 〉 N → Γ ⊢ N ∶ ty A

app*R' : ∀ {V} {Γ : Context V} {P Q : Path V} {M M' N N' : Term V} {A B : Type} →
    Γ ⊢ P ∶ M ≡〈 A ⇛ B 〉 M' → Γ ⊢ Q ∶ N ≡〈 A 〉 N' →
  -------------------------------------------------
    Γ ⊢ app* N N' P Q ∶ appT M N ≡〈 B 〉 appT M' N'
app*R' Γ⊢P∶M≡M' Γ⊢Q∶N≡N' = app*R (equation-validity₁ Γ⊢Q∶N≡N') (equation-validity₂ Γ⊢Q∶N≡N') Γ⊢P∶M≡M' Γ⊢Q∶N≡N'
