module PHOML.Compute.Prop where
open import Data.Product renaming (_,_ to _,p_)
open import Prelims
open import PHOML.Grammar
open import PHOML.Neutral
open import PHOML.Canon
open import PHOML.Red
open import PHOML.Compute.PC

⊧P_∶_ : ∀ {V} → Proof V → Term V → Set
⊧P δ ∶ φ = Σ[ ψ ∈ CanonProp ] φ ↠ decode ψ × ⊧PC δ ∶ ψ

⊧P-change-prop : ∀ {V} {δ : Proof V} {φ ψ} → ⊧P δ ∶ φ → φ ≡ ψ → ⊧P δ ∶ ψ
⊧P-change-prop ⊧δ∶φ refl = ⊧δ∶φ

⊧Prep : ∀ {U V} {δ : Proof U} {φ} {ρ : Rep U V} → ⊧P δ ∶ φ → ⊧P δ 〈 ρ 〉 ∶ φ 〈 ρ 〉
⊧Prep (θ ,p φ↠θ ,p ⊧δ∶θ) = θ ,p rep-red-canon θ φ↠θ ,p ⊧PCrep ⊧δ∶θ

Lemma35d : ∀ {V} {P : Path V} {pp θ d} → ⊧PC APPP (dir d P) (snocmap var pp) ∶ θ → Σ[ Q ∈ CanonΩ V ] P ↠ decode-CanonΩ Q
Lemma35d {pp = pp} {θ = bot} (δ ,p P+pp↠δ) = Lemma35c pp δ P+pp↠δ
Lemma35d {V} {P} {pp} {imp θ θ'} {d} ⊧P+pp∶θ⊃θ' =
  let Q ,p P↠Q = Lemma35d {V , -Proof} {P ⇑} {snocmap ↑ pp snoc x₀} {θ'} 
        (subst (λ x → ⊧PC x ∶ θ') 
        (cong (λ x → appP x (var x₀)) 
        (let open ≡-Reasoning in 
        begin
          APPP (dir d P) (snocmap var pp) ⇑
        ≡⟨ APPP-rep {εε = snocmap var pp} ⟩
          APPP (dir d (P ⇑)) (snocmap (λ E → E ⇑) (snocmap var pp))
        ≡⟨⟨ cong (APPP (dir d (P ⇑))) (snocmap-comp pp) ⟩⟩
          APPP (dir d (P ⇑)) (snocmap (λ x → var (↑ x)) pp)
        ≡⟨ cong (APPP (dir d (P ⇑))) (snocmap-comp pp) ⟩
          APPP (dir d (P ⇑)) (snocmap var (snocmap ↑ pp))
        ∎)) 
        (⊧P+pp∶θ⊃θ' (V , -Proof) upRep (var x₀) (⊧neutralPC (var x₀)))) in
  let Q' ,p P↠Q' ,p Q'≡Q = ↠-reflect-rep {E = P} {ρ = upRep} P↠Q refl in
  let Q₀ ,p Q₀≡Q' = reflect-canonΩ {P = Q'} {Q = Q} {ρ = upRep} Q'≡Q in
  Q₀ ,p subst (λ x → P ↠ x) Q₀≡Q' P↠Q'

Lemma35e : ∀ {V} {P : Path V} {φ d} → ⊧P dir d P ∶ φ → Σ[ Q ∈ CanonΩ V ] P ↠ decode-CanonΩ Q
Lemma35e (_ ,p _ ,p ⊧P+∶θ) = Lemma35d {pp = []} ⊧P+∶θ

conversionP : ∀ {V} {δ : Proof V} {φ ψ} → ⊧P δ ∶ φ → φ ≃ ψ → ⊧P δ ∶ ψ
conversionP (θ ,p φ↠θ ,p ⊧δ∶θ) φ≃ψ = θ ,p red-canon {θ = θ} φ↠θ φ≃ψ ,p ⊧δ∶θ

expansionP : ∀ {V} {δ ε : Proof V} {φ} → ⊧P ε ∶ φ → δ ⇒ ε → ⊧P δ ∶ φ
expansionP (θ ,p φ↠θ ,p ⊧ε∶θ) δ⇒ε = θ ,p φ↠θ ,p expansionPC ⊧ε∶θ δ⇒ε

