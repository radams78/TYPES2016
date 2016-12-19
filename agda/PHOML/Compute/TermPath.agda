module PHOML.Compute.TermPath where
open import Data.Product renaming (_,_ to _,p_)
open import Prelims
open import PHOML.Grammar
open import PHOML.PathSub
open import PHOML.Red
open import PHOML.Canon
open import PHOML.Compute.Prop

⊧T_∶_ : ∀ {V} → Term V → Type → Set
⊧E_∶_≡〈_〉_ : ∀ {V} → Path V → Term V → Type → Term V → Set

⊧T M ∶ A = ⊧E M ⟦⟦ refSub ∶ idSub _ ≡ idSub _ ⟧⟧ ∶ M ≡〈 A 〉 M
⊧E P ∶ φ ≡〈 Ω 〉 ψ = ⊧P plus P ∶ φ ⊃ ψ × ⊧P minus P ∶ ψ ⊃ φ
⊧E_∶_≡〈_〉_ {U} P M (A ⇛ B) M' = ∀ V (ρ : Rep U V) N N' Q → ⊧T N ∶ A → ⊧T N' ∶ A → ⊧E Q ∶ N ≡〈 A 〉 N' →
  ⊧E app* N N' (P 〈 ρ 〉) Q ∶ appT (M 〈 ρ 〉) N ≡〈 B 〉 appT (M' 〈 ρ 〉) N'

⊧Erep : ∀ {U V} {P : Path U} {M A N} {ρ : Rep U V} → ⊧E P ∶ M ≡〈 A 〉 N → ⊧E P 〈 ρ 〉 ∶ M 〈 ρ 〉 ≡〈 A 〉 N 〈 ρ 〉
⊧Erep {A = Ω} (⊧P+∶M⊃N ,p ⊧P-∶N⊃M) = ⊧Prep ⊧P+∶M⊃N ,p ⊧Prep ⊧P-∶N⊃M
⊧Erep {P = P} {M} {A = A ⇛ B} {M'} {ρ = ρ} ⊧P∶M≡M' W ρ₁ N N' Q ⊧N∶A ⊧N'∶A ⊧Q∶N≡N' = 
  subst₃ (λ x y z → ⊧E x ∶ y ≡〈 B 〉 z) (cong (λ x → app* N N' x Q) (rep-•R P)) (cong (λ x → appT x N) (rep-•R M)) (cong (λ x → appT x N') (rep-•R M')) (⊧P∶M≡M' W (ρ₁ •R ρ) N N' Q ⊧N∶A ⊧N'∶A ⊧Q∶N≡N')

⊧Trep : ∀ {U V} (M : Term U) {A} {ρ : Rep U V} → ⊧T M ∶ A → ⊧T M 〈 ρ 〉 ∶ A
⊧Trep {U} {V} M {A} {ρ} ⊧M∶A = subst (λ x → ⊧E x ∶ M 〈 ρ 〉 ≡〈 A 〉 (M 〈 ρ 〉)) 
  (let open ≡-Reasoning in 
    begin
      M ⟦⟦ refSub ∶ idSub U ≡ idSub U ⟧⟧ 〈 ρ 〉
    ≡⟨⟨ pathSub-•RP M ⟩⟩
      M ⟦⟦ refSub •PR ρ ∶ idSub V •SR ρ ≡ idSub V •SR ρ ⟧⟧
    ≡⟨⟨ pathSub-•PR M ⟩⟩
      M 〈 ρ 〉 ⟦⟦ refSub ∶ idSub V ≡ idSub V ⟧⟧
    ∎) 
  (⊧Erep ⊧M∶A)
--TODO Flip inputs to pathsub-•PR

⊧E⇛E : ∀ {V} {P : Path V} {M A B M' Q N N'} → ⊧E P ∶ M ≡〈 A ⇛ B 〉 M' → ⊧T N ∶ A → ⊧T N' ∶ A → ⊧E Q ∶ N ≡〈 A 〉 N' → ⊧E app* N N' P Q ∶ appT M N ≡〈 B 〉 appT M' N'
⊧E⇛E {V} {P} {M} {A} {B} {M'} {Q} {N} {N'} ⊧P∶M≡M' ⊧N∶A ⊧N'∶A ⊧Q∶N≡N' = subst₃ (λ x y z → ⊧E app* N N' x Q ∶ appT y N ≡〈 B 〉 appT z N') rep-idRep rep-idRep
                                                               rep-idRep (⊧P∶M≡M' V (idRep V) N N' Q ⊧N∶A ⊧N'∶A ⊧Q∶N≡N')
--A canonical object of type A
c : ∀ {V} → Type → Term V
c Ω = ⊥
c (A ⇛ B) = ΛT A (c B)

conversionE : ∀ {V} {P : Path V} {M M' N N' A} → ⊧E P ∶ M ≡〈 A 〉 N → M ≃ M' → N ≃ N' →
                      ⊧E P ∶ M' ≡〈 A 〉 N'
conversionE {A = Ω} (⊧P+∶φ⊃ψ ,p ⊧P-∶ψ⊃φ) φ≃φ' ψ≃ψ' =
  conversionP ⊧P+∶φ⊃ψ (≃-imp φ≃φ' ψ≃ψ') ,p conversionP ⊧P-∶ψ⊃φ (≃-imp ψ≃ψ' φ≃φ')
conversionE {A = A ⇛ B} ⊧P∶M≡N M≃M' N≃N' W ρ L L' Q ⊧L∶A ⊧L'∶A ⊧Q∶L≡L' = 
  conversionE {A = B} (⊧P∶M≡N W ρ L L' Q ⊧L∶A ⊧L'∶A ⊧Q∶L≡L') (≃-appTl (≃-resp-rep M≃M')) (≃-appTl (≃-resp-rep N≃N'))

expansionT : ∀ {V} {M N : Term V} {A} → ⊧T N ∶ A → M ⇒ N → ⊧T M ∶ A
expansionE : ∀ {V} {P Q : Path V} {M A N} → ⊧E Q ∶ M ≡〈 A 〉 N → P ⇒ Q → ⊧E P ∶ M ≡〈 A 〉 N

expansionT ⊧N∶A M⇒N = conversionE (expansionE ⊧N∶A (⇒-resp-ps M⇒N)) (sym (inc M⇒N)) (sym (inc M⇒N))

expansionE {A = Ω} (⊧Q+∶φ⊃ψ ,p ⊧Q-∶ψ⊃φ) P⇒Q = 
  expansionP ⊧Q+∶φ⊃ψ (dirR P⇒Q) ,p expansionP ⊧Q-∶ψ⊃φ (dirR P⇒Q)
expansionE {A = A ⇛ B} ⊧Q∶M≡M' P⇒Q W ρ N N' R ⊧N∶A ⊧N'∶A ⊧R∶N≡N' = expansionE (⊧Q∶M≡M' W ρ N N' R ⊧N∶A ⊧N'∶A ⊧R∶N≡N') (app*l (⇒-resp-rep P⇒Q))

c-closedE : ∀ {U U' V W} A {ρ₁ ρ₂ ρ₁' ρ₂'} {τ' : PathSub U' W} {τ : PathSub U V} {σ : Sub V W} →
                    c A ⟦⟦ τ ∶ ρ₁ ≡ ρ₂ ⟧⟧ ⟦ σ ⟧ ≡ c A ⟦⟦ τ' ∶ ρ₁' ≡ ρ₂' ⟧⟧
c-closedE Ω = refl
c-closedE (A ⇛ B) = cong (λλλ A) (c-closedE B)

c-closedR : ∀ {U V} A {ρ : Rep U V} → c A 〈 ρ 〉 ≡ c A
c-closedR Ω = refl
c-closedR (A ⇛ B) = cong (ΛT A) (c-closedR B)

c-closed : ∀ {U V} A {σ : Sub U V} → c A ⟦ σ ⟧ ≡ c A
c-closed Ω = refl
c-closed (A ⇛ B) = cong (ΛT A) (c-closed B)

⊧c : ∀ {V A} → ⊧T c {V} A ∶ A
⊧c {A = Ω} = (imp bot bot ,p ref ,p (λ {W ρ ε (ε' ,p ε↠ε') → ε' ,p trans (inc (appPl refdir)) (trans (inc βP) ε↠ε')})) ,p imp bot bot ,p ref ,p 
  λ {W ρ ε (ε' ,p ε↠ε') → ε' ,p trans (inc (appPl refdir)) (trans (inc βP) ε↠ε')}
⊧c {V} {A = A ⇛ B} W ρ N N' Q ⊧N∶A ⊧N'∶A ⊧Q∶N≡N' = expansionE 
  (conversionE 
    (subst₃ (λ x y z → ⊧E x ∶ y ≡〈 B 〉 z) 
      (let open ≡-Reasoning in 
      begin
        c B ⟦⟦ refSub ∶ idSub W ≡ idSub W ⟧⟧
      ≡⟨⟨ c-closedE B ⟩⟩
        c B ⟦⟦ liftPathSub refSub ∶ sub↖ (idSub V) ≡ sub↗ (idSub V) ⟧⟧ ⟦ (x₂:= N ,x₁:= N' ,x₀:= Q) •SR liftsRep pathDom ρ ⟧
      ≡⟨ sub-•SR (c B ⟦⟦ liftPathSub refSub ∶ sub↖ (idSub V) ≡ sub↗ (idSub V) ⟧⟧) ⟩
        c B ⟦⟦ liftPathSub refSub ∶ sub↖ (idSub V) ≡ sub↗ (idSub V) ⟧⟧ 〈 liftsRep pathDom ρ 〉 ⟦ x₂:= N ,x₁:= N' ,x₀:= Q ⟧
      ∎) (≡-sym (≡-trans (sub-congl (c-closedR B)) (c-closed B))) (≡-sym (≡-trans (sub-congl (c-closedR B)) (c-closed B))) (⊧c {A = B}))
    (sym (inc βT)) (sym (inc βT))) 
  βE

⊧E-wn : ∀ {V} {P : Path V} {M A N} → ⊧E P ∶ M ≡〈 A 〉 N → Σ[ Q ∈ CanonE V ] P ↠ decode-CanonE Q
⊧E-wn {A = Ω} (⊧P+∶M⊃N ,p _) with Lemma35e ⊧P+∶M⊃N
⊧E-wn {P = P} {A = Ω} (⊧P+∶M⊃N ,p _) | (P' ,p P↠P') = CanonΩ2CanonE P' ,p subst (λ x → P ↠ x) (decode-CanonΩE {P = P'}) P↠P'
⊧E-wn {V} {A = A ⇛ B} ⊧P∶M≡N = let 
  P'cA ,p PcA↠P'cA = ⊧E-wn (⊧P∶M≡N V (idRep V) (c A) (c A) (c A ⟦⟦ refSub ∶ idSub V ≡ idSub V ⟧⟧) ⊧c ⊧c ⊧c) in 
  app*-wnl {R = P'cA} PcA↠P'cA (cong₄ app* refl refl rep-idRep refl)
