--Computable proofs of canonical propositions
module PHOML.Compute.PC where
open import Data.Product renaming (_,_ to _,p_)
open import Prelims.EqReasoning
open import PHOML.Grammar
open import PHOML.Canon.Prop
open import PHOML.Neutral
open import PHOML.Red.RTRed

⊧PC_∶_ : ∀ {V} → Proof V → CanonProp → Set
⊧PC_∶_ {V} δ bot = Σ[ ε ∈ NeutralP V ] δ ↠ decode-NeutralP ε
⊧PC_∶_ {V} δ (imp φ ψ) = ∀ W (ρ : Rep V W) (ε : Proof W) (⊧ε∶φ : ⊧PC ε ∶ φ) → ⊧PC appP (δ 〈 ρ 〉) ε ∶ ψ

⊧PCrep : ∀ {U V} {δ : Proof U} {ρ : Rep U V} {θ} → ⊧PC δ ∶ θ → ⊧PC δ 〈 ρ 〉 ∶ θ
⊧PCrep {δ = δ} {ρ = ρ} {θ = bot} (ν ,p δ↠ν) = nrepP ρ ν ,p subst (λ x → δ 〈 ρ 〉 ↠ x) (≡-sym (decode-nrepP {ρ = ρ} {ν})) (↠-resp-rep δ↠ν)
⊧PCrep {δ = δ} {ρ = ρ} {θ = imp θ θ'} ⊧δ∶θ⊃θ' W σ ε ⊧ε∶θ = subst (λ x → ⊧PC appP x ε ∶ θ') (rep-comp δ) (⊧δ∶θ⊃θ' W (σ •R ρ) ε ⊧ε∶θ)
