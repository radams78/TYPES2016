module PHOML.Lemma35 where
open import Data.Product renaming (_,_ to _,p_)
open import Prelims
open import PHOML.Grammar
open import PHOML.Red
open import PHOML.Neutral
open import PHOML.Canon
open import PHOML.Compute

⊧P-out : ∀ {V} {δ : Proof V} {φ : Term V} {θ : CanonProp} →
  ⊧P δ ∶ φ → φ ↠ decode θ → ⊧PC δ ∶ θ
⊧P-out {δ = δ} (θ' ,p φ↠θ' ,p ⊧δ∶θ') φ↠θ = subst (λ x → ⊧PC δ ∶ x) (canon-unique φ↠θ' φ↠θ) ⊧δ∶θ'

⊧⊃* : ∀ {V} {P : Path V} {φ φ' Q ψ ψ'} →
  ⊧E P ∶ φ ≡〈 Ω 〉 φ' → ⊧E Q ∶ ψ ≡〈 Ω 〉 ψ' → ⊧E P ⊃* Q ∶ φ ⊃ ψ ≡〈 Ω 〉 φ' ⊃ ψ'
⊧⊃* (⊧P+∶φ⊃φ' ,p ⊧P-∶φ'⊃φ) (⊧Q+∶ψ⊃ψ' ,p ⊧Q-∶ψ'⊃ψ) with Lemma35e ⊧P+∶φ⊃φ'
⊧⊃* (⊧P+∶φ⊃φ' ,p ⊧P-∶φ'⊃φ) (⊧Q+∶ψ⊃ψ' ,p ⊧Q-∶ψ'⊃ψ) | Pcanon ,p P↠Pcanon with Lemma35e ⊧Q+∶ψ⊃ψ'
⊧⊃* {Q = Q} (⊧P+∶φ⊃φ' ,p ⊧P-∶φ'⊃φ) (⊧Q+∶ψ⊃ψ' ,p ⊧Q-∶ψ'⊃ψ) | neutral Pcanon ,p P↠Pcanon | Qcanon ,p Q↠Qcanon = 
  ↞E (⊧neutralE {P = imp*l Pcanon Q} (⊧imp (⊧E-valid₁ (⊧P+∶φ⊃φ' ,p ⊧P-∶φ'⊃φ)) (⊧E-valid₁ (⊧Q+∶ψ⊃ψ' ,p ⊧Q-∶ψ'⊃ψ))) 
  (⊧imp (⊧E-valid₂ (⊧P+∶φ⊃φ' ,p ⊧P-∶φ'⊃φ)) (⊧E-valid₂ (⊧Q+∶ψ⊃ψ' ,p ⊧Q-∶ψ'⊃ψ)))) (↠-imp*l P↠Pcanon)
⊧⊃* {P = P} (⊧P+∶φ⊃φ' ,p ⊧P-∶φ'⊃φ) (⊧Q+∶ψ⊃ψ' ,p ⊧Q-∶ψ'⊃ψ) | Pcanon ,p P↠Pcanon | neutral Qcanon ,p Q↠Qcanon = 
  ↞E (⊧neutralE {P = imp*r P Qcanon} (⊧imp (⊧E-valid₁ (⊧P+∶φ⊃φ' ,p ⊧P-∶φ'⊃φ)) (⊧E-valid₁ (⊧Q+∶ψ⊃ψ' ,p ⊧Q-∶ψ'⊃ψ))) 
  (⊧imp (⊧E-valid₂ (⊧P+∶φ⊃φ' ,p ⊧P-∶φ'⊃φ)) (⊧E-valid₂ (⊧Q+∶ψ⊃ψ' ,p ⊧Q-∶ψ'⊃ψ)))) (↠-imp*r Q↠Qcanon)
⊧⊃* {V} {φ = φ} {φ'} {ψ = ψ} {ψ'} (⊧P+∶φ⊃φ' ,p ⊧P-∶φ'⊃φ) (⊧Q+∶ψ⊃ψ' ,p ⊧Q-∶ψ'⊃ψ) | reffC M ,p P↠refM | reffC N ,p Q↠refN = 
  let θ ,p φ↠θ = ⊧canon (⊧E-valid₁ (⊧P+∶φ⊃φ' ,p ⊧P-∶φ'⊃φ)) in
  let θ' ,p φ'↠θ' = ⊧canon (⊧E-valid₂ (⊧P+∶φ⊃φ' ,p ⊧P-∶φ'⊃φ)) in
  let η ,p ψ↠η = ⊧canon (⊧E-valid₁ (⊧Q+∶ψ⊃ψ' ,p ⊧Q-∶ψ'⊃ψ)) in
  let η' ,p ψ'↠η' = ⊧canon (⊧E-valid₂ (⊧Q+∶ψ⊃ψ' ,p ⊧Q-∶ψ'⊃ψ)) in
  let ⊧idM∶θ⊃θ' : ⊧PC id M ∶ imp θ θ'
      ⊧idM∶θ⊃θ' = ⊧P-out (↠P ⊧P+∶φ⊃φ' (trans (↠-dir P↠refM) (inc refdir))) (↠-imp φ↠θ φ'↠θ') in
  let ⊧idM∶θ'⊃θ : ⊧PC id M ∶ imp θ' θ
      ⊧idM∶θ'⊃θ = ⊧P-out (↠P ⊧P-∶φ'⊃φ (trans (↠-dir P↠refM) (inc refdir))) (↠-imp φ'↠θ' φ↠θ) in
  let ⊧idN∶η⊃η' : ⊧PC id N ∶ imp η η'
      ⊧idN∶η⊃η' = ⊧P-out (↠P ⊧Q+∶ψ⊃ψ' (trans (↠-dir Q↠refN) (inc refdir))) (↠-imp ψ↠η ψ'↠η') in
  let ⊧idN∶η'⊃η : ⊧PC id N ∶ imp η' η
      ⊧idN∶η'⊃η = ⊧P-out (↠P ⊧Q-∶ψ'⊃ψ (trans (↠-dir Q↠refN) (inc refdir))) (↠-imp ψ'↠η' ψ↠η) in
  let ⊧ErefM⊃N : ⊧E reff (M ⊃ N) ∶ φ ⊃ ψ ≡〈 Ω 〉 φ' ⊃ ψ'
      ⊧ErefM⊃N = ((imp (imp θ η) (imp θ' η') ) ,p ((↠-imp (↠-imp φ↠θ ψ↠η) (↠-imp φ'↠θ' ψ'↠η')) ,p 
        (λ W ρ ε ⊧ε∶θ⊃η W₁ ρ₁ ε₁ ⊧ε₁∶θ' → 
        let ⊧ε₁∶θ : ⊧PC ε₁ ∶ θ
            ⊧ε₁∶θ = reductionPC (⊧idM∶θ'⊃θ W₁ (ρ₁ •R ρ) ε₁ ⊧ε₁∶θ') βP in
        let ⊧εε₁∶η : ⊧PC appP (ε 〈 ρ₁ 〉) ε₁ ∶ η
            ⊧εε₁∶η = ⊧ε∶θ⊃η W₁ ρ₁ ε₁ ⊧ε₁∶θ in
        let ⊧εε₁∶η' : ⊧PC appP (ε 〈 ρ₁ 〉) ε₁ ∶ η'
            ⊧εε₁∶η' = reductionPC (⊧idN∶η⊃η' W₁ (ρ₁ •R ρ) (appP (ε 〈 ρ₁ 〉) ε₁) ⊧εε₁∶η) βP in
        ↞PC {δ = appP (appP (plus (reff (M ⊃ N)) 〈 ρ 〉) ε 〈 ρ₁ 〉) ε₁}
          {ε = appP (ε 〈 ρ₁ 〉) ε₁} ⊧εε₁∶η' (trans (inc (appPl (appPl refdir))) (inc (appPl βP)))))) ,p 
        (imp (imp θ' η') (imp θ η)) ,p ((↠-imp (↠-imp φ'↠θ' ψ'↠η') (↠-imp φ↠θ ψ↠η)) ,p 
        (λ W ρ ε ⊧ε∶θ'⊃η' W₁ ρ₁ ε₁ ⊧ε₁∶θ →
        let ⊧ε₁∶θ' : ⊧PC ε₁ ∶ θ'
            ⊧ε₁∶θ' = reductionPC (⊧idM∶θ⊃θ' W₁ (ρ₁ •R ρ) ε₁ ⊧ε₁∶θ) βP in
        let ⊧εε₁∶η' : ⊧PC appP (ε 〈 ρ₁ 〉) ε₁ ∶ η'
            ⊧εε₁∶η' = ⊧ε∶θ'⊃η' W₁ ρ₁ ε₁ ⊧ε₁∶θ' in
        let ⊧εε₁∶η : ⊧PC appP (ε 〈 ρ₁ 〉) ε₁ ∶ η
            ⊧εε₁∶η = reductionPC (⊧idN∶η'⊃η W₁ (ρ₁ •R ρ) (appP (ε 〈 ρ₁ 〉) ε₁) ⊧εε₁∶η') βP in
          ↞PC {δ = appP (appP (minus (reff (M ⊃ N)) 〈 ρ 〉) ε 〈 ρ₁ 〉) ε₁}
          {ε = appP (ε 〈 ρ₁ 〉) ε₁} ⊧εε₁∶η (trans (inc (appPl (appPl refdir))) (inc (appPl βP))))) in
  ↞E ⊧ErefM⊃N (trans (↠-imp* P↠refM Q↠refN) (inc ref⊃*))
⊧⊃* (⊧P+∶φ⊃φ' ,p ⊧P-∶φ'⊃φ) (⊧Q+∶ψ⊃ψ' ,p ⊧Q-∶ψ'⊃ψ) | reffC M ,p P↠Pcanon | univC x x₁ x₂ x₃ ,p Q↠Qcanon = {!!}
⊧⊃* (⊧P+∶φ⊃φ' ,p ⊧P-∶φ'⊃φ) (⊧Q+∶ψ⊃ψ' ,p ⊧Q-∶ψ'⊃ψ) | univC x x₁ x₂ x₃ ,p P↠Pcanon | Qcanon ,p Q↠Qcanon = {!!}
