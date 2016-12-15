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

data NoTermAlpha : Set where
  ∅ : NoTermAlpha
  _,Proof : NoTermAlpha → NoTermAlpha
  _,Path  : NoTermAlpha → NoTermAlpha

decodeNTA : NoTermAlpha → Alphabet
decodeNTA ∅ = ∅
decodeNTA (V ,Proof) = decodeNTA V , -Proof
decodeNTA (V ,Path) = decodeNTA V , -Path

⊧idSub : ∀ V Γ → valid Γ → ⊧S idSub (decodeNTA V) ∶ Γ
⊧idSub ∅ .〈〉 empR ()
⊧idSub (V ,Proof) (Γ , φ) (ctxPR Γ⊢φ∶Ω) x₀ = ⊧neutralP' {δ = var x₀}
  (subst (λ x → ⊧T x ∶ Ω) (let open ≡-Reasoning in 
    begin
      φ ⟦ idSub (decodeNTA V) ⟧ ⇑
    ≡⟨ rep-congl (sub-idSub {E = φ}) ⟩
      φ ⇑
    ≡⟨⟨ sub-idSub ⟩⟩
      φ ⇑ ⟦ idSub (decodeNTA V , -Proof) ⟧
    ∎)
  (⊧Trep _ (soundness Γ⊢φ∶Ω (⊧idSub V Γ (context-validity Γ⊢φ∶Ω)))))
⊧idSub (V ,Proof) (Γ , φ) (ctxPR Γ⊢φ∶Ω) (↑ x) = 
  subst (λ y → ⊧ var (↑ x) ∶ y) 
  (≡-sym sub-idSub) 
  (⊧rep {decodeNTA V} {decodeNTA V , -Proof} {_} {var x} {typeof x Γ}
     {upRep} 
  (subst (λ y → ⊧ var x ∶ y) sub-idSub (⊧idSub V Γ (context-validity Γ⊢φ∶Ω) x)))
⊧idSub (V ,Path) (Γ , app (-eq A) (M ∷ N ∷ [])) (ctxER Γ⊢M∶A Γ⊢N∶A) x₀ = 
  ⊧neutralE {P = var x₀} 
  (subst (λ x → ⊧T x ∶ A) (≡-sym sub-idSub) (⊧Trep M {ρ = upRep}  
  (subst (λ x → ⊧T x ∶ A) sub-idSub (soundness Γ⊢M∶A (⊧idSub V Γ (context-validity Γ⊢M∶A)))))) 
  (subst (λ x → ⊧T x ∶ A) (≡-sym sub-idSub) (⊧Trep N {ρ = upRep}  
  (subst (λ x → ⊧T x ∶ A) sub-idSub (soundness Γ⊢N∶A (⊧idSub V Γ (context-validity Γ⊢M∶A))))))
⊧idSub (V ,Path) (Γ , _) (ctxER Γ⊢M∶A _) (↑ x) = 
  subst (λ y → ⊧ var (↑ x) ∶ y) (≡-sym sub-idSub) 
  (⊧rep {decodeNTA V} {decodeNTA V , -Path} {_} {E = var x} {typeof x Γ} {ρ = upRep} 
  (subst (λ y → ⊧ var x ∶ y) sub-idSub (⊧idSub V Γ (context-validity Γ⊢M∶A) x)))
