module PHOML.Compute.Prop where
open import Relation.Binary.PropositionalEquality
open import Data.Product renaming (_,_ to _,p_)
open import PHOML.Grammar
open import PHOML.Canon.Prop
open import PHOML.Red.RTRed
open import PHOML.Compute.PC

⊧P_∶_ : ∀ {V} → Proof V → Term V → Set
⊧P δ ∶ φ = Σ[ ψ ∈ CanonProp ] φ ↠ decode ψ × ⊧PC δ ∶ ψ

⊧P-change-prop : ∀ {V} {δ : Proof V} {φ ψ} → ⊧P δ ∶ φ → φ ≡ ψ → ⊧P δ ∶ ψ
⊧P-change-prop ⊧δ∶φ refl = ⊧δ∶φ

⊧Prep : ∀ {U V} {δ : Proof U} {φ} {ρ : Rep U V} → ⊧P δ ∶ φ → ⊧P δ 〈 ρ 〉 ∶ φ 〈 ρ 〉
⊧Prep (θ ,p φ↠θ ,p ⊧δ∶θ) = θ ,p rep-red-canon θ φ↠θ ,p ⊧PCrep ⊧δ∶θ

