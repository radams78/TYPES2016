module PHOPL.Meta where
open import Data.Empty renaming (⊥ to Empty)
open import Data.Fin
open import Data.Product renaming (_,_ to _,p_)
open import Prelims
open import Prelims.Closure
open import PHOPL.Grammar
open import PHOPL.Red
open import PHOPL.Rules
open import PHOPL.PathSub
open import PHOPL.Meta.ConVal

⊃-gen₂ : ∀ {V} {Γ : Context V} {φ} {ψ} {A} → Γ ⊢ φ ⊃ ψ ∶ A → Γ ⊢ ψ ∶ ty Ω
⊃-gen₂ (⊃R _ Γ⊢ψ∶Ω) = Γ⊢ψ∶Ω

eq-validity₁ : ∀ {V} {Γ : Context V} {P : Path V} {E M A N} → Γ ⊢ P ∶ E → E ≡ M ≡〈 A 〉 N → Γ ⊢ M ∶ ty A
eq-validity₁ (varR {Γ = Γ} _ validΓ) E≡M≡N = subst (λ E → Γ ⊢ left E ∶ ty (type E)) E≡M≡N (context-validity-Eq₁ validΓ)
eq-validity₁ {Γ = Γ} (refR Γ⊢P∶M≡N) E≡M≡N = subst₂ (λ x y → Γ ⊢ x ∶ y) {!eq-inj₁!} {!!} {!!}
eq-validity₁ (⊃*R Γ⊢P∶M≡N Γ⊢P∶M≡N₁) E≡M≡N = {!!}
eq-validity₁ (univR Γ⊢P∶M≡N Γ⊢P∶M≡N₁) E≡M≡N = {!!}
eq-validity₁ (lllR Γ⊢P∶M≡N) E≡M≡N = {!!}
eq-validity₁ (app*R Γ⊢P∶M≡N Γ⊢P∶M≡N₁ Γ⊢P∶M≡N₂ Γ⊢P∶M≡N₃) E≡M≡N = {!!}
eq-validity₁ (convER Γ⊢P∶M≡N Γ⊢P∶M≡N₁ Γ⊢P∶M≡N₂ M≃M' N≃N') E≡M≡N = {!!}

postulate Prop-Validity : ∀ {V} {Γ : Context V} {δ : Proof V} {φ : Term V} → 
                        Γ ⊢ δ ∶ φ → Γ ⊢ φ ∶ ty Ω
{- Prop-Validity (varR _ validΓ) = context-validity-Prop validΓ
Prop-Validity (appPR Γ⊢δ∶φ⊃ψ _) = ⊃-gen₂ (Prop-Validity Γ⊢δ∶φ⊃ψ)
Prop-Validity (ΛPR Γ⊢φ∶Ω Γ⊢ψ∶Ω _) = ⊃R Γ⊢φ∶Ω Γ⊢ψ∶Ω
Prop-Validity (convR _ Γ⊢φ∶Ω _) = Γ⊢φ∶Ω
Prop-Validity (plusR Γ⊢δ∶φ) = {!!}
Prop-Validity (minusR Γ⊢δ∶φ) = {!!} -}

postulate change-codR : ∀ {U} {V} {ρ : Rep U V} {Γ : Context U} {Δ Δ' : Context V} →
                      ρ ∶ Γ ⇒R Δ → Δ ≡ Δ' → ρ ∶ Γ ⇒R Δ'

postulate Generation-ΛP : ∀ {V} {Γ : Context V} {φ} {δ} {ε} {ψ} →
                          Γ ⊢ appP (ΛP φ δ) ε ∶ ψ →
                          Σ[ χ ∈ Term V ] 
                          (ψ ≃ φ ⊃ χ × Γ ,P φ ⊢ δ ∶ χ ⇑)

Generation-appT : ∀ {V} {Γ : Context V} {M N : Term V} {B} →
  Γ ⊢ appT M N ∶ ty B → Σ[ A ∈ Type ] Γ ⊢ M ∶ ty (A ⇛ B) × Γ ⊢ N ∶ ty A
Generation-appT (appR {V} {Γ} {M} {N} {A} {B} Γ⊢M∶A⇛B Γ⊢N∶A) = A ,p Γ⊢M∶A⇛B ,p Γ⊢N∶A

postulate _∶_⇒_ : ∀ {U} {V} → Sub U V → Context U → Context V → Set

postulate substitution : ∀ {U} {V} {σ : Sub U V} {K}
                       {Γ : Context U} {M : Expression U (varKind K)} {A} {Δ} →
                       Γ ⊢ M ∶ A → valid Δ → σ ∶ Γ ⇒ Δ → Δ ⊢ M ⟦ σ ⟧ ∶ A ⟦ σ ⟧

postulate •-typed : ∀ {U} {V} {W} {σ : Sub V W} {ρ : Sub U V} {Γ} {Δ} {Θ} →
                         σ ∶ Δ ⇒ Θ → ρ ∶ Γ ⇒ Δ → σ • ρ ∶ Γ ⇒ Θ

postulate •RS-typed : ∀ {U} {V} {W} {ρ : Rep V W} {σ : Sub U V} {Γ} {Δ} {Θ} →
                      ρ ∶ Δ ⇒R Θ → σ ∶ Γ ⇒ Δ → ρ •RS σ ∶ Γ ⇒ Θ

postulate liftSub-typed : ∀ {U} {V} {K} {σ : Sub U V} {Γ} {Δ} {A} →
                     σ ∶ Γ ⇒ Δ → liftSub K σ ∶ Γ , A ⇒ Δ , A ⟦ σ ⟧

postulate botsub-typed : ∀ {V} {K} {Γ} {E : Expression V (varKind K)} {A} → Γ ⊢ E ∶ A → x₀:= E ∶ Γ , A ⇒ Γ

lemma : ∀ {U} {V} {W} {K} (M : Expression U K) Q N' N (ρ : Rep V W) (σ : Sub U V) → M ⇑ ⇑ ⇑ ⟦ x₀:= Q • liftSub -Path (x₀:= N' • liftSub -Term (x₀:= N • liftSub -Term (ρ •RS σ))) ⟧ ≡ M ⟦ σ ⟧ 〈 ρ 〉 --TODO Rename
lemma {U} {V} {W} M Q N' N ρ σ = let open ≡-Reasoning in 
          begin
            M ⇑ ⇑ ⇑ ⟦ x₀:= Q • liftSub -Path (x₀:= N' • liftSub -Term (x₀:= N • liftSub -Term (ρ •RS σ))) ⟧
          ≡⟨ sub-• (M ⇑ ⇑ ⇑) ⟩
            M ⇑ ⇑ ⇑ ⟦ liftSub -Path (x₀:= N' • liftSub -Term (x₀:= N • liftSub -Term (ρ •RS σ))) ⟧ ⟦ x₀:= Q ⟧
          ≡⟨ sub-congl (liftSub-upRep (M ⇑ ⇑)) ⟩
            M ⇑ ⇑ ⟦ x₀:= N' • liftSub -Term (x₀:= N • liftSub -Term (ρ •RS σ)) ⟧ ⇑ ⟦ x₀:= Q ⟧
          ≡⟨ botSub-upRep _ ⟩
            M ⇑ ⇑ ⟦ x₀:= N' • liftSub -Term (x₀:= N • liftSub -Term (ρ •RS σ)) ⟧
          ≡⟨ sub-• (M ⇑ ⇑) ⟩
            M ⇑ ⇑ ⟦ liftSub -Term (x₀:= N • liftSub -Term (ρ •RS σ)) ⟧ ⟦ x₀:= N' ⟧
          ≡⟨ sub-congl (liftSub-upRep (M ⇑)) ⟩
            M ⇑ ⟦ x₀:= N • liftSub -Term (ρ •RS σ) ⟧ ⇑ ⟦ x₀:= N' ⟧
          ≡⟨ botSub-upRep _ ⟩
            M ⇑ ⟦ x₀:= N • liftSub -Term (ρ •RS σ) ⟧
          ≡⟨ sub-• (M ⇑) ⟩
            M ⇑ ⟦ liftSub -Term (ρ •RS σ) ⟧ ⟦ x₀:= N ⟧
          ≡⟨ sub-congl (liftSub-upRep M) ⟩
            M ⟦ ρ •RS σ ⟧ ⇑ ⟦ x₀:= N ⟧
          ≡⟨ botSub-upRep _ ⟩
            M ⟦ ρ •RS σ ⟧
          ≡⟨ sub-•RS M ⟩
            M ⟦ σ ⟧ 〈 ρ 〉
          ∎

postulate change-cod' : ∀ {U} {V} {σ : Sub U V} {Γ} {Δ} {Δ'} → σ ∶ Γ ⇒ Δ → Δ ≡ Δ' → σ ∶ Γ ⇒ Δ'

postulate extendSub-typed : ∀ {U} {V} {σ : Sub U V} {M : Term V} {Γ} {Δ} {A} →
                          σ ∶ Γ ⇒ Δ → Δ ⊢ M ∶ ty A → extendSub σ M ∶ Γ ,T A ⇒ Δ
                                                                              
postulate extendSub-upRep : ∀ {U} {V} {σ : Sub U V} {K} {M : Expression V (varKind K)} {C L} {E : Subexp U C L} →
                          E ⇑ ⟦ extendSub σ M ⟧ ≡ E ⟦ σ ⟧

postulate ⊃-gen₁ : ∀ {V} {Γ : Context V} {φ} {ψ} → Γ ⊢ φ ⊃ ψ ∶ ty Ω → Γ ⊢ φ ∶ ty Ω

postulate Type-Reduction : ∀ {V} {Γ : Context V} {K} {M : Expression V (varKind K)} {A} {B} →
                         Γ ⊢ M ∶ A → A ↠ B → Γ ⊢ M ∶ B

postulate change-cod : ∀ {U} {V} {σ : Sub U V} {Γ} {Δ} {Δ'} → σ ∶ Γ ⇒ Δ → Δ ≡ Δ' → σ ∶ Γ ⇒ Δ'
postulate sub↖-typed : ∀ {U} {V} {σ : Sub U V} {Γ} {Δ} {A} → σ ∶ Γ ⇒ Δ → sub↖ σ ∶ Γ ,T A ⇒ Δ ,T A ,T A ,E var x₁ ≡〈 A 〉 var x₀

postulate sub↗-typed : ∀ {U} {V} {σ : Sub U V} {Γ} {Δ} {A} → σ ∶ Γ ⇒ Δ → sub↗ σ ∶ Γ ,T A ⇒ Δ ,T A ,T A ,E var x₁ ≡〈 A 〉 var x₀

_∶_≡_∶_⇒_ : ∀ {U} {V} → PathSub U V → Sub U V → Sub U V → Context U → Context V → Set
τ ∶ σ ≡ σ' ∶ Γ ⇒ Δ = ∀ x → Δ ⊢ τ x ∶ σ -Term x ≡〈 typeof' x Γ 〉 σ' -Term x

change-cod-PS : ∀ {U} {V} {τ : PathSub U V} {ρ} {σ} {Γ} {Δ} {Δ'} →
                τ ∶ ρ ≡ σ ∶ Γ ⇒ Δ → Δ ≡ Δ' → τ ∶ ρ ≡ σ ∶ Γ ⇒ Δ'
change-cod-PS {τ = τ} {ρ} {σ} {Γ} τ∶ρ≡σ Δ≡Δ' = subst (λ x → τ ∶ ρ ≡ σ ∶ Γ ⇒ x) Δ≡Δ' τ∶ρ≡σ

postulate typeof'-up : ∀ {V} {Γ : Context V} {A} {x} → typeof' (↑ x) (Γ ,T A) ≡ typeof' x Γ

postulate rep-comp₃ : ∀ {U V₁ V₂ V₃ C K} (E : Subexp U C K) {ρ₃ : Rep V₂ V₃} {ρ₂ : Rep V₁ V₂} {ρ₁ : Rep U V₁} →
                    E 〈 ρ₃ •R ρ₂ •R ρ₁ 〉 ≡ E 〈 ρ₁ 〉 〈 ρ₂ 〉 〈 ρ₃ 〉

postulate weakening-addpath : ∀ {V} {Γ : Context V} {K} {E : Expression V (varKind K)} {T : Expression V (parent K)} {A} → Γ ⊢ E ∶ T → addpath Γ A ⊢ E ⇑ ⇑ ⇑ ∶ T ⇑ ⇑ ⇑
{- weakening-addpath {Γ = Γ} {E = E} {T} {A = A} Γ⊢T∶E = subst₂ (λ t e → addpath Γ A ⊢ t ∶ e) (rep-comp₃ E) (rep-comp₃ T) (weakening Γ⊢T∶E (valid-addpath (context-validity Γ⊢T∶E)) 
  (•R-typed {Θ = addpath Γ A} (•R-typed {Θ = addpath Γ A} {!upRep-typed !} (upRep-typed _)) (upRep-typed _))) -}

liftPathSub-typed : ∀ {U} {V} {τ : PathSub U V} {ρ} {σ} {Γ} {A} {Δ} → 
  τ ∶ ρ ≡ σ ∶ Γ ⇒ Δ → valid Δ → liftPathSub τ ∶ sub↖ ρ ≡ sub↗ σ ∶ Γ ,T A ⇒ Δ ,T  A ,T  A ,E var x₁ ≡〈 A 〉 var x₀
liftPathSub-typed _ validΔ x₀ = varR x₀ (valid-addpath validΔ)
liftPathSub-typed {U} {Γ = Γ} {A} {Δ = Δ} τ∶ρ≡σ validΔ (↑ x) = change-type (weakening-addpath (τ∶ρ≡σ x)) 
  (cong₃ _≡〈_〉_ refl (≡-sym (typeof'-up {U} {Γ = Γ} {A} {x = x})) refl)

postulate sub↖-decomp : ∀ {U} {V} {C} {K} (M : Subexp (U , -Term) C K) {ρ : Sub U V} → 
                     M ⟦ liftSub _ ρ ⟧ 〈 liftRep _ upRep 〉 〈 liftRep _ upRep 〉 〈 liftRep _ upRep 〉 ⟦ x₀:= var x₂ ⟧ ≡ M ⟦ sub↖ ρ ⟧

postulate sub↗-decomp : ∀ {U} {V} {C} {K} (M : Subexp (U , -Term) C K) {ρ : Sub U V} → 
                     M ⟦ liftSub _ ρ ⟧ 〈 liftRep _ upRep 〉 〈 liftRep _ upRep 〉 〈 liftRep _ upRep 〉 ⟦ x₀:= var x₁ ⟧ ≡ M ⟦ sub↗ ρ ⟧

postulate path-substitution : ∀ {U} {V} {Γ : Context U} {Δ : Context V} 
                            {ρ} {σ} {τ} {M} {A} →
                            (Γ ⊢ M ∶ A) → (τ ∶ ρ ≡ σ ∶ Γ ⇒ Δ) →
                            (ρ ∶ Γ ⇒ Δ) → (σ ∶ Γ ⇒ Δ) → 
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

postulate idPathSub : ∀ V → PathSub V V

postulate compRP-typed : ∀ {U} {V} {W} {ρ : Rep V W} {τ : PathSub U V} {σ σ' : Sub U V}
                           {Γ} {Δ} {Θ} →
                           ρ ∶ Δ ⇒R Θ → τ ∶ σ ≡ σ' ∶ Γ ⇒ Δ →
                           ρ •RP τ ∶ ρ •RS σ ≡ ρ •RS σ' ∶ Γ ⇒ Θ

postulate extendPS-typed : ∀ {U} {V} {τ : PathSub U V} {ρ} {σ} {Γ} {Δ} {P} {M} {N} {A} →
                           τ ∶ ρ ≡ σ ∶ Γ ⇒ Δ → Δ ⊢ P ∶ M ≡〈 A 〉 N →
                           extendPS τ P ∶ extendSub ρ M ≡ extendSub σ N ∶ Γ ,T A ⇒ Δ

toPath : ∀ {U V} → Sub U V → PathSub U V
toPath σ x = reff (σ _ x)

postulate extendPS-decomp : ∀ {U V} {M : Term (U , -Term)} {σ : Sub U V} {P N N'} →
                          M ⟦⟦ extendPS (toPath σ) P ∶ extendSub σ N ≡ extendSub σ N' ⟧⟧ ≡ (M ⟦ liftSub _ σ ⟧) ⟦⟦ x₀::= P ∶ x₀:= N ≡ x₀:= N' ⟧⟧

postulate pathsub-extendPS : ∀ {U} {V} M {τ} {P : Path V} {N : Term V} {σ : Sub U V} {N' : Term V} {σ'} →
                           M ⟦⟦ extendPS τ P ∶ extendSub σ N ≡ extendSub σ' N' ⟧⟧
                           ≡ M ⟦⟦ liftPathSub τ ∶ sub↖ σ ≡ sub↗ σ' ⟧⟧ ⟦ x₂:= N ,x₁:= N' ,x₀:= P ⟧

postulate sub↖-compRP : ∀ {U} {V} {W} {σ : Sub U V} {ρ : Rep V W} →
                      sub↖ (ρ •RS σ) ∼ liftRep -Path (liftRep -Term (liftRep -Term ρ)) •RS sub↖ σ

postulate sub↗-compRP : ∀ {U} {V} {W} {σ : Sub U V} {ρ : Rep V W} →
                      sub↗ (ρ •RS σ) ∼ liftRep -Path (liftRep -Term (liftRep -Term ρ)) •RS sub↗ σ

postulate Subject-Reduction-R : ∀ {V} {K} {E F : Expression V (varKind K)} {Γ} {A} →
                              Γ ⊢ E ∶ A → E ⇒ F → Γ ⊢ F ∶ A

{-Subject-Reduction-R : ∀ {V} {K} {C} 
  {c : Constructor C} {E : ListAbs V C} {F : Expression V (varKind K)} {Γ} {A} →
  Γ ⊢ (app c E) ∶ A → R c E F → Γ ⊢ F ∶ A
Subject-Reduction-R Γ⊢ΛPφδε∶A βR =
  let (χ ,p A≃φ⊃χ ,p Γ,φ⊢δ∶χ) = Generation-ΛP Γ⊢ΛPφδε∶A in {!!}
Subject-Reduction-R Γ⊢cE∶A βE = {!!}
Subject-Reduction-R Γ⊢cE∶A plus-ref = {!!}
Subject-Reduction-R Γ⊢cE∶A minus-ref = {!!}
Subject-Reduction-R Γ⊢cE∶A plus-univ = {!!}
Subject-Reduction-R Γ⊢cE∶A minus-univ = {!!}
Subject-Reduction-R Γ⊢cE∶A ref⊃*univ = {!!}
Subject-Reduction-R Γ⊢cE∶A univ⊃*ref = {!!}
Subject-Reduction-R Γ⊢cE∶A univ⊃*univ = {!!}
Subject-Reduction-R Γ⊢cE∶A ref⊃*ref = {!!}
Subject-Reduction-R Γ⊢cE∶A refref = {!!}
Subject-Reduction-R Γ⊢cE∶A lllred = {!!}
Subject-Reduction-R Γ⊢cE∶A reflamvar = {!!}
Subject-Reduction-R Γ⊢cE∶A reflam⊃* = {!!}
Subject-Reduction-R Γ⊢cE∶A reflamuniv = {!!}
Subject-Reduction-R Γ⊢cE∶A reflamλλλ = {!!} -}

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