module PHOML.Lemma35 where
open import Data.Product renaming (_,_ to _,p_)
open import Prelims
open import PHOML.Grammar
open import PHOML.Red
open import PHOML.Neutral
open import PHOML.Canon
open import PHOML.Compute

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
⊧⊃* {V} {P} {φ} {φ'} {Q} {ψ} {ψ'} (⊧P+∶φ⊃φ' ,p ⊧P-∶φ'⊃φ) (⊧Q+∶ψ⊃ψ' ,p ⊧Q-∶ψ'⊃ψ) | reffC M ,p P↠refM | reffC N ,p Q↠refN = 
  let ⊧φ : ⊧T φ ∶ Ω
      ⊧φ = ⊧E-valid₁ (⊧P+∶φ⊃φ' ,p ⊧P-∶φ'⊃φ) in
  let ⊧φ' : ⊧T φ' ∶ Ω
      ⊧φ' = ⊧E-valid₂ (⊧P+∶φ⊃φ' ,p ⊧P-∶φ'⊃φ) in
  let ⊧ψ : ⊧T ψ ∶ Ω
      ⊧ψ = ⊧E-valid₁ (⊧Q+∶ψ⊃ψ' ,p ⊧Q-∶ψ'⊃ψ) in
  let ⊧ψ' : ⊧T ψ' ∶ Ω
      ⊧ψ' = ⊧E-valid₂ (⊧Q+∶ψ⊃ψ' ,p ⊧Q-∶ψ'⊃ψ) in
  (⊧P⊃I (⊧imp ⊧φ ⊧ψ) (⊧imp ⊧φ' ⊧ψ') (λ W ρ ε ⊧ε∶φ⊃ψ → 
  ⊧P⊃I (⊧TΩrep ⊧φ') (⊧TΩrep ⊧ψ') (λ W₁ ρ₁ ε₁ ⊧ε₁∶φ' → 
  let ⊧P-ε₁∶φ : ⊧P appP (minus P 〈 ρ₁ •R ρ 〉) ε₁ ∶ φ 〈 ρ₁ •R ρ 〉
      ⊧P-ε₁∶φ = ⊧P⊃E (⊧Prep ⊧P-∶φ'⊃φ) (⊧P-change-prop ⊧ε₁∶φ' (≡-sym (rep-comp φ'))) in
  let ⊧ε₁∶φ : ⊧P ε₁ ∶ φ 〈 ρ₁ •R ρ 〉
      ⊧ε₁∶φ = ↠P ⊧P-ε₁∶φ (Pdirlm P↠refM) in
  let ⊧εε₁∶ψ : ⊧P appP (ε 〈 ρ₁ 〉) ε₁ ∶ ψ 〈 ρ₁ •R ρ 〉
      ⊧εε₁∶ψ = ⊧P⊃E (⊧P-change-prop (⊧Prep ⊧ε∶φ⊃ψ) (≡-sym (rep-comp (φ ⊃ ψ)))) ⊧ε₁∶φ in
  let ⊧Q+εε₁∶ψ' : ⊧P appP (plus Q 〈 ρ₁ •R ρ 〉) (appP (ε 〈 ρ₁ 〉) ε₁) ∶ ψ' 〈 ρ₁ •R ρ 〉
      ⊧Q+εε₁∶ψ' = ⊧P⊃E (⊧Prep ⊧Q+∶ψ⊃ψ') ⊧εε₁∶ψ in
  let ⊧εε₁∶ψ' : ⊧P appP (ε 〈 ρ₁ 〉) ε₁ ∶ ψ' 〈 ρ₁ •R ρ 〉
      ⊧εε₁∶ψ' = ↠P ⊧Q+εε₁∶ψ' (Pdirlm Q↠refN) in
  ↞P (⊧P-change-prop ⊧εε₁∶ψ' (rep-comp ψ')) (↠-appP (subst (λ x → appP x (ε 〈 ρ₁ 〉) ↠ ε 〈 ρ₁ 〉) (rep-comp (plus (P ⊃* Q))) (Pdirlm (trans (↠-imp* P↠refM Q↠refN) (inc ref⊃*)))))))) ,p
  (⊧P⊃I (⊧imp ⊧φ' ⊧ψ') (⊧imp ⊧φ ⊧ψ) (λ W ρ ε ⊧ε∶φ'⊃ψ' → 
  ⊧P⊃I (⊧TΩrep ⊧φ) (⊧TΩrep ⊧ψ) (λ W₁ ρ₁ ε₁ ⊧ε₁∶φ → 
  let ⊧P+ε₁∶φ' : ⊧P appP (plus P 〈 ρ₁ •R ρ 〉) ε₁ ∶ φ' 〈 ρ₁ •R ρ 〉
      ⊧P+ε₁∶φ' = ⊧P⊃E (⊧Prep ⊧P+∶φ⊃φ') (⊧P-change-prop ⊧ε₁∶φ (≡-sym (rep-comp φ))) in
  let ⊧ε₁∶φ' : ⊧P ε₁ ∶ φ' 〈 ρ₁ •R ρ 〉
      ⊧ε₁∶φ' = ↠P ⊧P+ε₁∶φ' (Pdirlm P↠refM) in
  let ⊧εε₁∶ψ' : ⊧P appP (ε 〈 ρ₁ 〉) ε₁ ∶ ψ' 〈 ρ₁ •R ρ 〉
      ⊧εε₁∶ψ' = ⊧P⊃E (⊧P-change-prop (⊧Prep ⊧ε∶φ'⊃ψ') (≡-sym (rep-comp (φ' ⊃ ψ')))) ⊧ε₁∶φ' in
  let ⊧Q-εε₁∶ψ : ⊧P appP (minus Q 〈 ρ₁ •R ρ 〉) (appP (ε 〈 ρ₁ 〉) ε₁) ∶ ψ 〈 ρ₁ •R ρ 〉
      ⊧Q-εε₁∶ψ = ⊧P⊃E (⊧Prep ⊧Q-∶ψ'⊃ψ) ⊧εε₁∶ψ' in
  let ⊧εε₁∶ψ : ⊧P appP (ε 〈 ρ₁ 〉) ε₁ ∶ ψ 〈 ρ₁ •R ρ 〉
      ⊧εε₁∶ψ = ↠P ⊧Q-εε₁∶ψ (Pdirlm Q↠refN) in
   ↞P (⊧P-change-prop ⊧εε₁∶ψ (rep-comp ψ)) (↠-appP (subst (λ x → appP x (ε 〈 ρ₁ 〉) ↠ ε 〈 ρ₁ 〉) (rep-comp (minus (P ⊃* Q))) (Pdirlm (trans (↠-imp* P↠refM Q↠refN) (inc ref⊃*))))))))
⊧⊃* {V} {P} {φ} {φ'} {Q} {ψ} {ψ'} (⊧P+∶φ⊃φ' ,p ⊧P-∶φ'⊃φ) (⊧Q+∶ψ⊃ψ' ,p ⊧Q-∶ψ'⊃ψ) | reffC M ,p P↠refM | univC _ _ δ ε ,p Q↠univδε = 
  let ⊧φ : ⊧T φ ∶ Ω
      ⊧φ = ⊧E-valid₁ (⊧P+∶φ⊃φ' ,p ⊧P-∶φ'⊃φ) in
  let ⊧φ' : ⊧T φ' ∶ Ω
      ⊧φ' = ⊧E-valid₂ (⊧P+∶φ⊃φ' ,p ⊧P-∶φ'⊃φ) in
  let ⊧ψ : ⊧T ψ ∶ Ω
      ⊧ψ = ⊧E-valid₁ (⊧Q+∶ψ⊃ψ' ,p ⊧Q-∶ψ'⊃ψ) in
  let ⊧ψ' : ⊧T ψ' ∶ Ω
      ⊧ψ' = ⊧E-valid₂ (⊧Q+∶ψ⊃ψ' ,p ⊧Q-∶ψ'⊃ψ) in
  let ⊧δ∶ψ⊃ψ' : ⊧P δ ∶ ψ ⊃ ψ'
      ⊧δ∶ψ⊃ψ' = ↠P ⊧Q+∶ψ⊃ψ' (trans (↠-dir Q↠univδε) (inc univplus)) in
  let ⊧ε∶ψ'⊃ψ : ⊧P ε ∶ ψ' ⊃ ψ
      ⊧ε∶ψ'⊃ψ = ↠P ⊧Q-∶ψ'⊃ψ (trans (↠-dir Q↠univδε) (inc univminus)) in
  (⊧P⊃I (⊧imp ⊧φ ⊧ψ) (⊧imp ⊧φ' ⊧ψ') (λ W ρ α ⊧α∶φ⊃ψ → 
  ⊧P⊃I (⊧TΩrep ⊧φ') (⊧TΩrep ⊧ψ') (λ W₁ ρ₁ β ⊧β∶φ' → 
  let ⊧β∶φ : ⊧P β ∶ φ 〈 ρ 〉 〈 ρ₁ 〉
      ⊧β∶φ = ↠P (⊧P⊃E (⊧Prep (⊧Prep ⊧P-∶φ'⊃φ)) ⊧β∶φ') (subst (λ x → x ↠ β) (cong (λ x → appP x β) (cong minus (rep-comp P))) (Pdirlm P↠refM)) in
  let ⊧αβ∶ψ : ⊧P appP (α 〈 ρ₁ 〉) β ∶ ψ 〈 ρ 〉 〈 ρ₁ 〉
      ⊧αβ∶ψ = ⊧P⊃E (⊧Prep ⊧α∶φ⊃ψ) ⊧β∶φ in
  let ⊧δαβ∶ψ' : ⊧P appP (δ 〈 ρ 〉 〈 ρ₁ 〉) (appP (α 〈 ρ₁ 〉) β) ∶ ψ' 〈 ρ 〉 〈 ρ₁ 〉
      ⊧δαβ∶ψ' = ⊧P⊃E (⊧Prep (⊧Prep ⊧δ∶ψ⊃ψ')) ⊧αβ∶ψ in
  ↞P (subst (λ x → ⊧P x ∶ ((ψ' 〈 ρ 〉) 〈 ρ₁ 〉)) 
    (cong₂ appP (let open ≡-Reasoning in 
    begin
      δ 〈 ρ 〉 〈 ρ₁ 〉
    ≡⟨⟨ botSub-upRep (δ 〈 ρ 〉 〈 ρ₁ 〉) ⟩⟩
      δ 〈 ρ 〉 〈 ρ₁ 〉 ⇑ ⟦ x₀:= β ⟧
    ≡⟨⟨ sub-congl (rep-congl (botSub-upRep (δ 〈 ρ 〉 〈 ρ₁ 〉))) ⟩⟩
      δ 〈 ρ 〉 〈 ρ₁ 〉 ⇑ ⟦ x₀:= α 〈 ρ₁ 〉 ⟧ ⇑ ⟦ x₀:= β ⟧
    ≡⟨⟨ sub-congl (liftSub-upRep (δ 〈 ρ 〉 〈 ρ₁ 〉 ⇑)) ⟩⟩
      δ 〈 ρ 〉 〈 ρ₁ 〉 ⇑ ⇑ ⟦ liftSub _ (x₀:= α 〈 ρ₁ 〉) ⟧ ⟦ x₀:= β ⟧
    ∎) 
    (cong₂ appP (≡-sym (botSub-upRep (α 〈 ρ₁ 〉))) refl)) 
    ⊧δαβ∶ψ') 
  (trans (↠-appP (↠-appP (↠-dir (↠-imp* (↠-resp-rep (↠-resp-rep P↠refM)) (↠-resp-rep (↠-resp-rep Q↠univδε)))))) 
  (trans (inc (appPl (appPl (dirR ref⊃*univ)))) (trans (inc (appPl (appPl univplus))) (trans (inc (appPl βP)) (inc βP)))))))) ,p
  ⊧P⊃I (⊧imp ⊧φ' ⊧ψ') (⊧imp ⊧φ ⊧ψ) (λ W ρ α ⊧α∶φ'⊃ψ' → 
  ⊧P⊃I (⊧TΩrep ⊧φ) (⊧TΩrep ⊧ψ) (λ W₁ ρ₁ β ⊧β∶φ → 
  let ⊧β∶φ' : ⊧P β ∶ φ' 〈 ρ 〉 〈 ρ₁ 〉
      ⊧β∶φ' = ↠P (⊧P⊃E (⊧Prep (⊧Prep ⊧P+∶φ⊃φ')) ⊧β∶φ) (subst (λ x → x ↠ β) (cong (λ x → appP x β) (cong plus (rep-comp P))) (Pdirlm P↠refM)) in
  let ⊧αβ∶ψ' : ⊧P appP (α 〈 ρ₁ 〉) β ∶ ψ' 〈 ρ 〉 〈 ρ₁ 〉
      ⊧αβ∶ψ' = ⊧P⊃E (⊧Prep ⊧α∶φ'⊃ψ') ⊧β∶φ' in
  let ⊧εαβ∶ψ : ⊧P appP (ε 〈 ρ 〉 〈 ρ₁ 〉) (appP (α 〈 ρ₁ 〉) β) ∶ ψ 〈 ρ 〉 〈 ρ₁ 〉
      ⊧εαβ∶ψ = ⊧P⊃E (⊧Prep (⊧Prep ⊧ε∶ψ'⊃ψ)) ⊧αβ∶ψ' in
    ↞P (subst (λ x → ⊧P x ∶ ((ψ 〈 ρ 〉) 〈 ρ₁ 〉)) 
    (cong₂ appP (let open ≡-Reasoning in 
    begin
      ε 〈 ρ 〉 〈 ρ₁ 〉
    ≡⟨⟨ botSub-upRep (ε 〈 ρ 〉 〈 ρ₁ 〉) ⟩⟩
      ε 〈 ρ 〉 〈 ρ₁ 〉 ⇑ ⟦ x₀:= β ⟧
    ≡⟨⟨ sub-congl (rep-congl (botSub-upRep (ε 〈 ρ 〉 〈 ρ₁ 〉))) ⟩⟩
      ε 〈 ρ 〉 〈 ρ₁ 〉 ⇑ ⟦ x₀:= α 〈 ρ₁ 〉 ⟧ ⇑ ⟦ x₀:= β ⟧
    ≡⟨⟨ sub-congl (liftSub-upRep (ε 〈 ρ 〉 〈 ρ₁ 〉 ⇑)) ⟩⟩
      ε 〈 ρ 〉 〈 ρ₁ 〉 ⇑ ⇑ ⟦ liftSub _ (x₀:= α 〈 ρ₁ 〉) ⟧ ⟦ x₀:= β ⟧
    ∎) 
    (cong₂ appP (≡-sym (botSub-upRep (α 〈 ρ₁ 〉))) refl)) 
    ⊧εαβ∶ψ) 
  (trans (↠-appP (↠-appP (↠-dir (↠-imp* (↠-resp-rep (↠-resp-rep P↠refM)) (↠-resp-rep (↠-resp-rep Q↠univδε)))))) 
  (trans (inc (appPl (appPl (dirR ref⊃*univ)))) (trans (inc (appPl (appPl univminus))) (trans (inc (appPl βP)) (inc βP)))))))
⊧⊃* {V} {P} {φ} {φ'} {Q} {ψ} {ψ'} (⊧P+∶φ⊃φ' ,p ⊧P-∶φ'⊃φ) (⊧Q+∶ψ⊃ψ' ,p ⊧Q-∶ψ'⊃ψ) | univC M M' δ ε ,p P↠univ | reffC N ,p Q↠ref =
  let ⊧φ : ⊧T φ ∶ Ω
      ⊧φ = ⊧E-valid₁ (⊧P+∶φ⊃φ' ,p ⊧P-∶φ'⊃φ) in
  let ⊧φ' : ⊧T φ' ∶ Ω
      ⊧φ' = ⊧E-valid₂ (⊧P+∶φ⊃φ' ,p ⊧P-∶φ'⊃φ) in
  let ⊧ψ : ⊧T ψ ∶ Ω
      ⊧ψ = ⊧E-valid₁ (⊧Q+∶ψ⊃ψ' ,p ⊧Q-∶ψ'⊃ψ) in
  let ⊧ψ' : ⊧T ψ' ∶ Ω
      ⊧ψ' = ⊧E-valid₂ (⊧Q+∶ψ⊃ψ' ,p ⊧Q-∶ψ'⊃ψ) in
  let ⊧δ∶φ⊃φ' : ⊧P δ ∶ φ ⊃ φ'
      ⊧δ∶φ⊃φ' = ↠P ⊧P+∶φ⊃φ' (trans (↠-dir P↠univ) (inc univplus)) in
  let ⊧ε∶φ'⊃φ : ⊧P ε ∶ φ' ⊃ φ
      ⊧ε∶φ'⊃φ = ↠P ⊧P-∶φ'⊃φ (trans (↠-dir P↠univ) (inc univminus)) in
  (⊧P⊃I (⊧imp ⊧φ ⊧ψ) (⊧imp ⊧φ' ⊧ψ') (λ W ρ α ⊧α∶φ⊃ψ → 
  ⊧P⊃I (⊧TΩrep ⊧φ') (⊧TΩrep ⊧ψ') (λ W₁ ρ₁ β ⊧β∶φ' → 
    let ⊧εβ∶φ : ⊧P appP (ε 〈 ρ 〉 〈 ρ₁ 〉) β ∶ φ 〈 ρ 〉 〈 ρ₁ 〉
        ⊧εβ∶φ = ⊧P⊃E (⊧Prep (⊧Prep ⊧ε∶φ'⊃φ)) ⊧β∶φ' in
    let ⊧αεβ∶ψ : ⊧P appP (α 〈 ρ₁ 〉) (appP (ε 〈 ρ 〉 〈 ρ₁ 〉) β) ∶ ψ 〈 ρ 〉 〈 ρ₁ 〉
        ⊧αεβ∶ψ = ⊧P⊃E (⊧Prep ⊧α∶φ⊃ψ) ⊧εβ∶φ in
    let ⊧αεβ∶ψ' : ⊧P appP (α 〈 ρ₁ 〉) (appP (ε 〈 ρ 〉 〈 ρ₁ 〉) β) ∶ ψ' 〈 ρ 〉 〈 ρ₁ 〉
        ⊧αεβ∶ψ' = ↠P (⊧P⊃E (⊧Prep (⊧Prep ⊧Q+∶ψ⊃ψ')) ⊧αεβ∶ψ) (trans (↠-appP (↠-dir (↠-resp-rep (↠-resp-rep Q↠ref)))) (trans (inc (appPl refdir)) (inc βP))) in
  ↞P ⊧αεβ∶ψ' (trans (↠-appP (↠-appP (↠-dir (↠-resp-rep (↠-resp-rep (↠-imp* P↠univ Q↠ref)))))) (trans (inc (appPl (appPl (dirR univ⊃*ref)))) 
    (trans (inc (appPl (appPl univplus))) (trans (inc (appPl βP)) (inc (subst (λ x → appP ((ΛP (M' 〈 ρ 〉 〈 ρ₁ 〉 ⇑) (appP (var x₁) (appP (ε 〈 ρ 〉 〈 ρ₁ 〉 ⇑ ⇑) (var x₀)))) ⟦ x₀:= α 〈 ρ₁ 〉 ⟧) β ⇒ x) (cong₂ appP (botSub-upRep (α 〈 ρ₁ 〉)) (cong₂ appP (≡-sym (let open ≡-Reasoning in 
    begin
      ε 〈 ρ 〉 〈 ρ₁ 〉
    ≡⟨⟨ botSub-upRep (ε 〈 ρ 〉 〈 ρ₁ 〉) ⟩⟩
      ε 〈 ρ 〉 〈 ρ₁ 〉 ⇑ ⟦ x₀:= β ⟧
    ≡⟨⟨ sub-congl (rep-congl (botSub-upRep (ε 〈 ρ 〉 〈 ρ₁ 〉))) ⟩⟩
      ε 〈 ρ 〉 〈 ρ₁ 〉 ⇑ ⟦ x₀:= α 〈 ρ₁ 〉 ⟧ ⇑ ⟦ x₀:= β ⟧
    ≡⟨⟨ sub-congl (liftSub-upRep (ε 〈 ρ 〉 〈 ρ₁ 〉 ⇑)) ⟩⟩
      ε 〈 ρ 〉 〈 ρ₁ 〉 ⇑ ⇑ ⟦ liftSub _ (x₀:= α 〈 ρ₁ 〉) ⟧ ⟦ x₀:= β ⟧
    ∎)) refl)) βP))))))))) ,p
  ⊧P⊃I (⊧imp ⊧φ' ⊧ψ') (⊧imp ⊧φ ⊧ψ) (λ W ρ α ⊧α∶φ'⊃ψ' → 
  ⊧P⊃I (⊧TΩrep ⊧φ) (⊧TΩrep ⊧ψ) (λ W₁ ρ₁ β ⊧β∶φ → 
    let ⊧δβ∶φ' : ⊧P appP (δ 〈 ρ 〉 〈 ρ₁ 〉) β ∶ φ' 〈 ρ 〉 〈 ρ₁ 〉
        ⊧δβ∶φ' = ⊧P⊃E (⊧Prep (⊧Prep ⊧δ∶φ⊃φ')) ⊧β∶φ in
    let ⊧αδβ∶ψ' : ⊧P appP (α 〈 ρ₁ 〉) (appP (δ 〈 ρ 〉 〈 ρ₁ 〉) β) ∶ ψ' 〈 ρ 〉 〈 ρ₁ 〉
        ⊧αδβ∶ψ' = ⊧P⊃E (⊧Prep ⊧α∶φ'⊃ψ') ⊧δβ∶φ' in
    let ⊧αδβ∶ψ : ⊧P appP (α 〈 ρ₁ 〉) (appP (δ 〈 ρ 〉 〈 ρ₁ 〉) β) ∶ ψ 〈 ρ 〉 〈 ρ₁ 〉
        ⊧αδβ∶ψ = ↠P (⊧P⊃E (⊧Prep (⊧Prep ⊧Q-∶ψ'⊃ψ)) ⊧αδβ∶ψ') (trans (↠-appP (↠-dir (↠-resp-rep (↠-resp-rep Q↠ref)))) (trans (inc (appPl refdir)) (inc βP))) in
  ↞P ⊧αδβ∶ψ (trans (↠-appP (↠-appP (↠-dir (↠-resp-rep (↠-resp-rep (↠-imp* P↠univ Q↠ref)))))) 
    (trans (inc (appPl (appPl (dirR univ⊃*ref)))) (trans (inc (appPl (appPl univminus))) (trans (inc (appPl βP)) (inc 
      (subst (λ x → appP ((ΛP (M 〈 ρ 〉 〈 ρ₁ 〉 ⇑) (appP (var x₁) (appP (δ 〈 ρ 〉 〈 ρ₁ 〉 ⇑ ⇑) (var x₀)))) ⟦ x₀:= α 〈 ρ₁ 〉 ⟧) β ⇒ x) (cong₂ appP (botSub-upRep (α 〈 ρ₁ 〉)) (cong₂ appP (≡-sym (let open ≡-Reasoning in 
    begin
      δ 〈 ρ 〉 〈 ρ₁ 〉
    ≡⟨⟨ botSub-upRep (δ 〈 ρ 〉 〈 ρ₁ 〉) ⟩⟩
      δ 〈 ρ 〉 〈 ρ₁ 〉 ⇑ ⟦ x₀:= β ⟧
    ≡⟨⟨ sub-congl (rep-congl (botSub-upRep (δ 〈 ρ 〉 〈 ρ₁ 〉))) ⟩⟩
      δ 〈 ρ 〉 〈 ρ₁ 〉 ⇑ ⟦ x₀:= α 〈 ρ₁ 〉 ⟧ ⇑ ⟦ x₀:= β ⟧
    ≡⟨⟨ sub-congl (liftSub-upRep (δ 〈 ρ 〉 〈 ρ₁ 〉 ⇑)) ⟩⟩
      δ 〈 ρ 〉 〈 ρ₁ 〉 ⇑ ⇑ ⟦ liftSub _ (x₀:= α 〈 ρ₁ 〉) ⟧ ⟦ x₀:= β ⟧
    ∎)) refl)) βP))))))))
⊧⊃* {V} {P} {φ} {φ'} {Q} {ψ} {ψ'} (⊧P+∶φ⊃φ' ,p ⊧P-∶φ'⊃φ) (⊧Q+∶ψ⊃ψ' ,p ⊧Q-∶ψ'⊃ψ) | univC M M' δ ε ,p P↠univ | univC N N' δ' ε' ,p Q↠univ =
  let ⊧φ : ⊧T φ ∶ Ω
      ⊧φ = ⊧E-valid₁ (⊧P+∶φ⊃φ' ,p ⊧P-∶φ'⊃φ) in
  let ⊧φ' : ⊧T φ' ∶ Ω
      ⊧φ' = ⊧E-valid₂ (⊧P+∶φ⊃φ' ,p ⊧P-∶φ'⊃φ) in
  let ⊧ψ : ⊧T ψ ∶ Ω
      ⊧ψ = ⊧E-valid₁ (⊧Q+∶ψ⊃ψ' ,p ⊧Q-∶ψ'⊃ψ) in
  let ⊧ψ' : ⊧T ψ' ∶ Ω
      ⊧ψ' = ⊧E-valid₂ (⊧Q+∶ψ⊃ψ' ,p ⊧Q-∶ψ'⊃ψ) in
  let ⊧δ∶φ⊃φ' : ⊧P δ ∶ φ ⊃ φ'
      ⊧δ∶φ⊃φ' = ↠P ⊧P+∶φ⊃φ' (trans (↠-dir P↠univ) (inc univplus)) in
  let ⊧ε∶φ'⊃φ : ⊧P ε ∶ φ' ⊃ φ
      ⊧ε∶φ'⊃φ = ↠P ⊧P-∶φ'⊃φ (trans (↠-dir P↠univ) (inc univminus)) in
  let ⊧δ'∶ψ⊃ψ' : ⊧P δ' ∶ ψ ⊃ ψ'
      ⊧δ'∶ψ⊃ψ' = ↠P ⊧Q+∶ψ⊃ψ' (trans (↠-dir Q↠univ) (inc univplus)) in
  let ⊧ε'∶ψ'⊃ψ : ⊧P ε' ∶ ψ' ⊃ ψ
      ⊧ε'∶ψ'⊃ψ = ↠P ⊧Q-∶ψ'⊃ψ (trans (↠-dir Q↠univ) (inc univminus)) in
  (⊧P⊃I (⊧imp ⊧φ ⊧ψ) (⊧imp ⊧φ' ⊧ψ') (λ W ρ α ⊧α∶φ⊃ψ → 
  ⊧P⊃I (⊧TΩrep ⊧φ') (⊧TΩrep ⊧ψ') (λ W₁ ρ₁ β ⊧β∶φ' → 
  let ⊧εβ∶φ : ⊧P appP (ε 〈 ρ 〉 〈 ρ₁ 〉) β ∶ φ 〈 ρ 〉 〈 ρ₁ 〉
      ⊧εβ∶φ = ⊧P⊃E (⊧Prep (⊧Prep ⊧ε∶φ'⊃φ)) ⊧β∶φ' in
  let ⊧αεβ∶ψ : ⊧P appP (α 〈 ρ₁ 〉) (appP (ε 〈 ρ 〉 〈 ρ₁ 〉) β) ∶ ψ 〈 ρ 〉 〈 ρ₁ 〉
      ⊧αεβ∶ψ = ⊧P⊃E (⊧Prep ⊧α∶φ⊃ψ) ⊧εβ∶φ in
  let ⊧δαεβ∶ψ' : ⊧P appP (δ 〈 ρ 〉 〈 ρ₁ 〉) (
    {!!}))) ,p 
  ⊧P⊃I (⊧imp ⊧φ' ⊧ψ') (⊧imp ⊧φ ⊧ψ) (λ W ρ α ⊧α∶φ'⊃ψ' → 
  ⊧P⊃I (⊧TΩrep ⊧φ) (⊧TΩrep ⊧ψ) (λ W₁ ρ₁ β ⊧β∶φ →
  let ⊧δβ∶φ' : ⊧P appP (δ 〈 ρ 〉 〈 ρ₁ 〉) β ∶ φ' 〈 ρ 〉 〈 ρ₁ 〉
      ⊧δβ∶φ' = ⊧P⊃E (⊧Prep (⊧Prep ⊧δ∶φ⊃φ')) ⊧β∶φ in
  {!!}))
--TODO Lots of duplication!