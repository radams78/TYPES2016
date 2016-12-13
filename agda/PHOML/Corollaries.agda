module PHOML.Corollaries where
open import PHOML.Grammar
open import PHOML.Rules
open import PHOML.Meta
open import PHOML.Compute
open import PHOML.ComputeSub
open import PHOML.MainTheorem

⊧idSub : ∀ V Γ → valid Γ → ⊧S idSub V ∶ Γ
⊧idSub .∅ 〈〉 _ ()
⊧idSub (V , -Proof) (Γ , φ) (ctxPR Γ⊢φ∶Ω) { -Proof} x₀ = let θ ,p φ↠θ = ⊧canon (soundness Γ⊢φ∶Ω (⊧idSub V Γ {!context-validity Γ⊢φ∶Ω!})) in {!!}
⊧idSub _ (Γ , x) validΓ { -Proof} (↑ x₁) = {!!}
⊧idSub V Γ validΓ { -Term} x = {!!}
⊧idSub V Γ validΓ { -Path} x = {!!}
