--Computable proofs of canonical propositions
module PHOML.Compute.PC where
open import Data.Product renaming (_,_ to _,p_)
open import Prelims
open import PHOML.Grammar
open import PHOML.Canon.Prop
open import PHOML.Neutral
open import PHOML.Red

⊧PC_∶_ : ∀ {V} → Proof V → CanonProp → Set
⊧PC_∶_ {V} δ bot = Σ[ ε ∈ NeutralP V ] δ ↠ decode-NeutralP ε
⊧PC_∶_ {V} δ (imp φ ψ) = ∀ W (ρ : Rep V W) (ε : Proof W) (⊧ε∶φ : ⊧PC ε ∶ φ) → ⊧PC appP (δ 〈 ρ 〉) ε ∶ ψ

⊧PCrep : ∀ {U V} {δ : Proof U} {ρ : Rep U V} {θ} → ⊧PC δ ∶ θ → ⊧PC δ 〈 ρ 〉 ∶ θ
⊧PCrep {δ = δ} {ρ = ρ} {θ = bot} (ν ,p δ↠ν) = nrepP ρ ν ,p subst (λ x → δ 〈 ρ 〉 ↠ x) (≡-sym (decode-nrepP {ρ = ρ} {ν})) (↠-resp-rep δ↠ν)
⊧PCrep {δ = δ} {ρ = ρ} {θ = imp θ θ'} ⊧δ∶θ⊃θ' W σ ε ⊧ε∶θ = subst (λ x → ⊧PC appP x ε ∶ θ') (rep-•R δ) (⊧δ∶θ⊃θ' W (σ •R ρ) ε ⊧ε∶θ)

⊧neutralPC : ∀ {V} (δ : NeutralP V) {θ : CanonProp} → ⊧PC decode-NeutralP δ ∶ θ
⊧neutralPC δ {θ = bot} = δ ,p ref
⊧neutralPC δ {θ = imp θ θ'} W ρ ε ⊧ε∶φ = subst (λ x → ⊧PC x ∶ θ') {appP (decode-NeutralP (nrepP ρ δ)) ε} (cong (λ x → appP x ε) (decode-nrepP {ρ = ρ} {δ})) (⊧neutralPC (app (nrepP ρ δ) ε))

expansionPC : ∀ {V} {δ ε : Proof V} {θ} → ⊧PC ε ∶ θ → δ ⇒ ε → ⊧PC δ ∶ θ
expansionPC {θ = bot} (χ ,p ε↠χ) δ⇒ε = χ ,p (trans (inc δ⇒ε) ε↠χ)
expansionPC {θ = imp θ θ'} ⊧ε∶θ⊃θ' δ⇒ε W ρ χ ⊧χ∶θ = expansionPC (⊧ε∶θ⊃θ' W ρ χ ⊧χ∶θ) (appPl (⇒-resp-rep δ⇒ε))
