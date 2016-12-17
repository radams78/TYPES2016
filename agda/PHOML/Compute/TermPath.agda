module PHOML.Compute.TermPath where
open import Data.Product renaming (_,_ to _,p_)
open import Prelims.EqReasoning
open import PHOML.Grammar
open import PHOML.PathSub
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
  subst₃ (λ x y z → ⊧E x ∶ y ≡〈 B 〉 z) (cong (λ x → app* N N' x Q) (rep-comp P)) (cong (λ x → appT x N) (rep-comp M)) (cong (λ x → appT x N') (rep-comp M')) (⊧P∶M≡M' W (ρ₁ •R ρ) N N' Q ⊧N∶A ⊧N'∶A ⊧Q∶N≡N')

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

