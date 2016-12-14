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

⊧idSub : ∀ V Γ → valid Γ → ⊧S idSub V ∶ Γ
⊧idSub .∅ 〈〉 _ ()
⊧idSub (V , -Proof) (Γ , φ) (ctxPR Γ⊢φ∶Ω) { -Proof} x₀ = let θ ,p φ↠θ = ⊧canon (soundness Γ⊢φ∶Ω (⊧idSub V Γ (context-validity Γ⊢φ∶Ω))) in 
  ⊧neutralP {V , -Proof} {var x₀} {(φ ⇑) ⟦ idSub _ ⟧} {θ} 
  (subst₂ _↠_ 
    (let open ≡-Reasoning in 
    begin
      φ ⟦ idSub V ⟧ ⇑
    ≡⟨ rep-congl (sub-idSub {E = φ}) ⟩
      φ ⇑
    ≡⟨⟨ sub-idSub ⟩⟩
      φ ⇑ ⟦ idSub _ ⟧
    ∎) (canon-closed θ) (↠-resp-rep {ρ = upRep} φ↠θ))
⊧idSub (V , .-Term) (Γ , _) (ctxTR validΓ) { -Proof} (↑ x) = 
  subst (λ y → ⊧P var (↑ x) ∶ y) {!!} (⊧Prep {ρ = upRep} (⊧idSub V Γ validΓ x))
⊧idSub (V , .-Proof) (Γ , A) (ctxPR x) { -Proof} (↑ x₁) = {!!}
⊧idSub (V , .-Path) (Γ , _) (ctxER x x₁) { -Proof} (↑ x₂) = {!!}
⊧idSub V Γ validΓ { -Term} x = {!!}
⊧idSub V Γ validΓ { -Path} x = {!!}
