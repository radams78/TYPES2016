module PHOML.Meta.Sub where
open import Prelims.EqReasoning
open import PHOML.Grammar
open import PHOML.Red.Conv
open import PHOML.Rules
open import PHOML.Meta.ConVal

_∶_⟶_ : ∀ {U V} → Sub U V → Context V → Context U → Set
_∶_⟶_ {U} {V} σ Γ Δ = ∀ {K} (x : Var U K) → Γ ⊢ σ _ x ∶ typeof x Δ ⟦ σ ⟧

botSub-typed : ∀ {V K} {M : VExpression V K} {Γ A} →
  Γ ⊢ M ∶ A → x₀:= M ∶ Γ ⟶ Γ , A
botSub-typed {V} {K} {M} {Γ} {A} Γ⊢M∶A x₀ = change-type Γ⊢M∶A (≡-sym (botSub-upRep A {M}))
botSub-typed {Γ = Γ} Γ⊢M∶A (↑ x) = change-type (varR x (context-validity Γ⊢M∶A)) (≡-sym (botSub-upRep (typeof x Γ)))

liftSub-typed : ∀ {U V} {σ : Sub U V} {Δ Γ K A} →
  σ ∶ Δ ⟶ Γ → valid (_,_ {V} {K} Δ (A ⟦ σ ⟧)) → liftSub K σ ∶ Δ , A ⟦ σ ⟧ ⟶ Γ , A
liftSub-typed {A = A} σ∶Δ⟶Γ validΔA x₀ = change-type (varR x₀ validΔA) (≡-sym (liftSub-upRep A))
liftSub-typed {σ = σ} {Γ = Γ} {A = A} σ∶Δ⟶Γ validΔA (↑ x) = change-type (weakening (σ∶Δ⟶Γ x) validΔA (upRep-typed (A ⟦ σ ⟧))) (≡-sym (liftSub-upRep (typeof x Γ)))

substitution : ∀ {U} {V} {σ : Sub U V} {K}
  {Γ : Context U} {M : Expression U (varKind K)} {A} {Δ} →
  Γ ⊢ M ∶ A → valid Δ → σ ∶ Δ ⟶ Γ → Δ ⊢ M ⟦ σ ⟧ ∶ A ⟦ σ ⟧
substitution (varR x _) _ σ∶Δ⟶Γ = σ∶Δ⟶Γ x
substitution (appR Γ⊢M∶A⇛B Γ⊢N∶A) validΔ σ∶Δ⟶Γ = appR (substitution Γ⊢M∶A⇛B validΔ σ∶Δ⟶Γ) (substitution Γ⊢N∶A validΔ σ∶Δ⟶Γ)
substitution (ΛR Γ,A⊢M∶B) validΔ σ∶Δ⟶Γ = ΛR (substitution Γ,A⊢M∶B (ctxTR validΔ) (liftSub-typed σ∶Δ⟶Γ (ctxTR validΔ)))
substitution (⊥R validΓ) validΔ σ∶Δ⟶Γ = ⊥R validΔ
substitution (⊃R Γ⊢φ∶Ω Γ⊢ψ∶Ω) validΔ σ∶Δ⟶Γ = 
  ⊃R (substitution Γ⊢φ∶Ω validΔ σ∶Δ⟶Γ) (substitution Γ⊢ψ∶Ω validΔ σ∶Δ⟶Γ)
substitution (appPR Γ⊢δ∶φ⊃ψ Γ⊢ε∶φ) validΔ σ∶Δ⟶Γ =
  appPR (substitution Γ⊢δ∶φ⊃ψ validΔ σ∶Δ⟶Γ) (substitution Γ⊢ε∶φ validΔ σ∶Δ⟶Γ)
substitution {σ = σ} {Δ = Δ} (ΛPR {φ = φ} {ψ = ψ} Γ⊢φ∶Ω Γ⊢ψ∶Ω Γ,φ⊢δ∶ε) validΔ σ∶Δ⟶Γ = 
  let Δ⊢φ∶Ω : Δ ⊢ φ ⟦ σ ⟧ ∶ ty Ω
      Δ⊢φ∶Ω = substitution Γ⊢φ∶Ω validΔ σ∶Δ⟶Γ in
  let validΔφ : valid (Δ ,P φ ⟦ σ ⟧)
      validΔφ = ctxPR Δ⊢φ∶Ω in
  ΛPR Δ⊢φ∶Ω (substitution Γ⊢ψ∶Ω validΔ σ∶Δ⟶Γ)
  (change-type (substitution Γ,φ⊢δ∶ε validΔφ
    (liftSub-typed σ∶Δ⟶Γ validΔφ)) (liftSub-upRep ψ))
substitution (convR Γ⊢δ∶φ Γ⊢ψ∶Ω φ≃ψ) validΔ σ∶Δ⟶Γ = 
  convR (substitution Γ⊢δ∶φ validΔ σ∶Δ⟶Γ) (substitution Γ⊢ψ∶Ω validΔ σ∶Δ⟶Γ) 
  (≃-resp-sub φ≃ψ)
substitution (refR Γ⊢M∶A) validΔ σ∶Δ⟶Γ = refR (substitution Γ⊢M∶A validΔ σ∶Δ⟶Γ)
substitution (⊃*R Γ⊢P∶φ≡φ' Γ⊢Q∶ψ≡ψ') validΔ σ∶Δ⟶Γ = 
  ⊃*R (substitution Γ⊢P∶φ≡φ' validΔ σ∶Δ⟶Γ) (substitution Γ⊢Q∶ψ≡ψ' validΔ σ∶Δ⟶Γ)
substitution (univR Γ⊢δ∶φ⊃ψ Γ⊢ε∶ψ⊃φ) validΔ σ∶Δ⟶Γ = 
  univR (substitution Γ⊢δ∶φ⊃ψ validΔ σ∶Δ⟶Γ) (substitution Γ⊢ε∶ψ⊃φ validΔ σ∶Δ⟶Γ)
substitution (plusR Γ⊢P∶φ≡φ') validΔ σ∶Δ⟶Γ = plusR (substitution Γ⊢P∶φ≡φ' validΔ σ∶Δ⟶Γ)
substitution (minusR Γ⊢P∶φ≡ψ) validΔ σ∶Δ⟶Γ = minusR (substitution Γ⊢P∶φ≡ψ validΔ σ∶Δ⟶Γ)
substitution (lllR {B = B} {M = M} {N = N} Γ⊢M∶A⇛B Γ⊢N∶A⇛B ΓAAE⊢P∶Mx≡Ny) validΔ σ∶Δ⟶Γ = 
  lllR (substitution Γ⊢M∶A⇛B validΔ σ∶Δ⟶Γ) 
    (substitution Γ⊢N∶A⇛B validΔ σ∶Δ⟶Γ) 
    (change-type (substitution ΓAAE⊢P∶Mx≡Ny 
      (valid-addpath validΔ) (liftSub-typed (liftSub-typed (liftSub-typed σ∶Δ⟶Γ (ctxTR validΔ)) (ctxTR (ctxTR validΔ))) (valid-addpath validΔ))) 
  (cong₂ (λ x y → appT x (var x₂) ≡〈 B 〉 appT y (var x₁)) 
    (liftSub-upRep₃ M) (liftSub-upRep₃ N)))
substitution (app*R Γ⊢N∶A Γ⊢N'∶A Γ⊢P∶M≡M' Γ⊢Q∶N≡N') validΔ σ∶Δ⟶Γ = 
  app*R (substitution Γ⊢N∶A validΔ σ∶Δ⟶Γ) (substitution Γ⊢N'∶A validΔ σ∶Δ⟶Γ) 
    (substitution Γ⊢P∶M≡M' validΔ σ∶Δ⟶Γ) (substitution Γ⊢Q∶N≡N' validΔ σ∶Δ⟶Γ)
substitution (convER Γ⊢P∶M≡N Γ⊢M'∶A Γ⊢N'∶A M≃M' N≃N') validΔ σ∶Δ⟶Γ = 
  convER (substitution Γ⊢P∶M≡N validΔ σ∶Δ⟶Γ) (substitution Γ⊢M'∶A validΔ σ∶Δ⟶Γ) (substitution Γ⊢N'∶A validΔ σ∶Δ⟶Γ) (≃-resp-sub M≃M') (≃-resp-sub N≃N')

