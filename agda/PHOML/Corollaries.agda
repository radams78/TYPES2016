module PHOML.Corollaries where
open import Data.Product renaming (_,_ to _,p_)
open import Prelims
open import PHOML.Grammar
open import PHOML.Red
open import PHOML.Canon
open import PHOML.Neutral
open import PHOML.Rules
open import PHOML.Meta
open import PHOML.Compute
open import PHOML.ComputeSub
open import PHOML.MainTheorem

private id-up-lemma : ∀ {V C K L} (E : Subexp V C K) → E ⟦ idSub V ⟧ ⇑ ≡ E ⇑ ⟦ idSub (V , L) ⟧
id-up-lemma {V} {C} {K} {L} E = let open ≡-Reasoning in 
  begin
    E ⟦ idSub V ⟧ ⇑
  ≡⟨ rep-congl (sub-idSub {E = E}) ⟩
    E ⇑
  ≡⟨⟨ sub-idSub ⟩⟩
    E ⇑ ⟦ idSub (V , L) ⟧
  ∎

remove-term : Alphabet → Alphabet
remove-term ∅ = ∅
remove-term (V , -Proof) = remove-term V , -Proof
remove-term (V , -Term) = remove-term V
remove-term (V , -Path) = remove-term V , -Path

default : ∀ {V} → Context V → Sub V (remove-term V)
default 〈〉 _ ()
default {_ , -Proof} (Γ , _) = extendSub (upRep •RS default Γ) (var x₀)
default {_ , -Term} (Γ , app (-ty A) []) = extendSub (default Γ) (c A)
default {_ , -Path} (Γ , _) = extendSub (upRep •RS default Γ) (var x₀)

extendSub-upRep : ∀ {U V C K L} (E : Subexp U C K) {σ : Sub U V} {F : VExpression V L} → E ⇑ ⟦ extendSub σ F ⟧ ≡ E ⟦ σ ⟧
extendSub-upRep {U} {V} {C} {K} {L} E {σ} {F} = let open ≡-Reasoning in 
  begin
    E ⇑ ⟦ extendSub σ F ⟧
  ≡⟨ extendSub-decomp (E ⇑) ⟩
    E ⇑ ⟦ liftSub L σ ⟧ ⟦ x₀:= F ⟧
  ≡⟨ sub-congl (liftSub-upRep E) ⟩
    E ⟦ σ ⟧ ⇑ ⟦ x₀:= F ⟧
  ≡⟨ botSub-upRep (E ⟦ σ ⟧) ⟩
    E ⟦ σ ⟧
  ∎
  
extendSub-upRep-•RS : ∀ {U V W C K L} (E : Subexp U C K) {σ : Sub U V} {ρ : Rep V W} {F : VExpression W L} →
  E ⇑ ⟦ extendSub (ρ •RS σ) F ⟧ ≡ E ⟦ σ ⟧ 〈 ρ 〉
extendSub-upRep-•RS {U} {V} {W} {C} {K} {L} E {σ} {ρ} {F} = let open ≡-Reasoning in 
  begin
    E ⇑ ⟦ extendSub (ρ •RS σ) F ⟧
  ≡⟨ extendSub-upRep E ⟩
    E ⟦ ρ •RS σ ⟧
  ≡⟨ sub-•RS E ⟩
    E ⟦ σ ⟧ 〈 ρ 〉
  ∎

⊧default : ∀ {V} {Γ : Context V} → valid Γ → ⊧S default Γ ∶ Γ
⊧default {Γ = 〈〉} _ ()
⊧default {V , -Proof} {Γ , φ} (ctxPR Γ⊢φ∶Ω) x₀ = ⊧neutralP' {remove-term V , -Proof} {var x₀} {(φ ⇑) ⟦ default (Γ , φ) ⟧} 
  (subst (λ x → ⊧T x ∶ Ω) 
  (≡-sym (extendSub-upRep-•RS φ))
  (⊧TΩrep {φ = φ ⟦ default Γ ⟧} {ρ = upRep} (soundness Γ⊢φ∶Ω (⊧default (context-validity Γ⊢φ∶Ω)))))
⊧default {V , -Term} {_ , app (-ty _) []} _ x₀ = ⊧c
⊧default {V , -Path} {Γ , app (-eq A) (M ∷ N ∷ [])} (ctxER Γ⊢M∶A Γ⊢N∶A) x₀ = ⊧neutralE {P = var x₀} 
  (subst (λ x → ⊧T x ∶ A) 
    (≡-sym (extendSub-upRep-•RS M {default Γ} )) (⊧Trep (M ⟦ default Γ ⟧) (soundness Γ⊢M∶A (⊧default (context-validity Γ⊢M∶A))))) 
  (subst (λ x → ⊧T x ∶ A) 
    (≡-sym (extendSub-upRep-•RS N {default Γ} )) (⊧Trep (N ⟦ default Γ ⟧) (soundness Γ⊢N∶A (⊧default (context-validity Γ⊢N∶A)))))
⊧default {V , -Proof} {Γ , φ} x₁ (↑ x₂) = {!!}
⊧default {V , -Term} {Γ , x} x₁ (↑ x₂) = {!!}
⊧default {V , -Path} {Γ , x} x₁ (↑ x₂) = {!!}