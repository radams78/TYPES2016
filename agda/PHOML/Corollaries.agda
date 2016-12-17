module PHOML.Corollaries where
open import Data.Empty renaming (⊥ to Empty)
open import Data.Product renaming (_,_ to _,p_)
open import Data.Sum
open import Prelims
open import PHOML.Grammar
open import PHOML.PathSub
open import PHOML.Red
open import PHOML.Canon
open import PHOML.Neutral
open import PHOML.Rules
open import PHOML.Meta
open import PHOML.Compute
open import PHOML.ComputeSub
open import PHOML.MainTheorem

data NoTermAlpha : Set where
  ∅ : NoTermAlpha
  _,Proof : NoTermAlpha → NoTermAlpha
  _,Path  : NoTermAlpha → NoTermAlpha

decodeNTA : NoTermAlpha → Alphabet
decodeNTA ∅ = ∅
decodeNTA (V ,Proof) = decodeNTA V , -Proof
decodeNTA (V ,Path) = decodeNTA V , -Path

⊧idSub : ∀ V Γ → valid Γ → ⊧S idSub (decodeNTA V) ∶ Γ
⊧idSub ∅ .〈〉 empR ()
⊧idSub (V ,Proof) (Γ , φ) (ctxPR Γ⊢φ∶Ω) x₀ = ⊧neutralP' {δ = var x₀}
  (subst (λ x → ⊧T x ∶ Ω) (let open ≡-Reasoning in 
    begin
      φ ⟦ idSub (decodeNTA V) ⟧ ⇑
    ≡⟨ rep-congl (sub-idSub {E = φ}) ⟩
      φ ⇑
    ≡⟨⟨ sub-idSub ⟩⟩
      φ ⇑ ⟦ idSub (decodeNTA V , -Proof) ⟧
    ∎)
  (⊧Trep _ (soundness Γ⊢φ∶Ω (⊧idSub V Γ (context-validity Γ⊢φ∶Ω)))))
⊧idSub (V ,Proof) (Γ , φ) (ctxPR Γ⊢φ∶Ω) (↑ x) = 
  subst (λ y → ⊧ var (↑ x) ∶ y) 
  (≡-sym sub-idSub) 
  (⊧rep {decodeNTA V} {decodeNTA V , -Proof} {_} {var x} {typeof x Γ}
     {upRep} 
  (subst (λ y → ⊧ var x ∶ y) sub-idSub (⊧idSub V Γ (context-validity Γ⊢φ∶Ω) x)))
⊧idSub (V ,Path) (Γ , app (-eq A) (M ∷ N ∷ [])) (ctxER Γ⊢M∶A Γ⊢N∶A) x₀ = 
  ⊧neutralE {P = var x₀} 
  (subst (λ x → ⊧T x ∶ A) (≡-sym sub-idSub) (⊧Trep M {ρ = upRep}  
  (subst (λ x → ⊧T x ∶ A) sub-idSub (soundness Γ⊢M∶A (⊧idSub V Γ (context-validity Γ⊢M∶A)))))) 
  (subst (λ x → ⊧T x ∶ A) (≡-sym sub-idSub) (⊧Trep N {ρ = upRep}  
  (subst (λ x → ⊧T x ∶ A) sub-idSub (soundness Γ⊢N∶A (⊧idSub V Γ (context-validity Γ⊢M∶A))))))
⊧idSub (V ,Path) (Γ , _) (ctxER Γ⊢M∶A _) (↑ x) = 
  subst (λ y → ⊧ var (↑ x) ∶ y) (≡-sym sub-idSub) 
  (⊧rep {decodeNTA V} {decodeNTA V , -Path} {_} {E = var x} {typeof x Γ} {ρ = upRep} 
  (subst (λ y → ⊧ var x ∶ y) sub-idSub (⊧idSub V Γ (context-validity Γ⊢M∶A) x)))

soundness' : ∀ {V} {Γ : Context (decodeNTA V)} {K} {E : VExpression (decodeNTA V) K} {T} → Γ ⊢ E ∶ T → ⊧ E ∶ T
soundness' {V} {Γ} {K} {E} {T} Γ⊢E∶T = subst₂ (λ x y → ⊧ x ∶ y) {E ⟦ idSub (decodeNTA V) ⟧} {E} {T ⟦ idSub (decodeNTA V) ⟧} {T} sub-idSub sub-idSub 
  (soundness Γ⊢E∶T (⊧idSub V Γ (context-validity Γ⊢E∶T)))

canonicityP : ∀ {V} {Γ : Context (decodeNTA V)} {δ : Proof (decodeNTA V)} {φ} → Γ ⊢ δ ∶ φ → Σ[ ε ∈ CanonP (decodeNTA V) ] δ ↠ decode-CanonP ε
canonicityP {V} Γ⊢δ∶φ = ⊧P-wn (soundness' {V} Γ⊢δ∶φ)

⊧E-wn : ∀ {V} {P : Path V} {M A N} → ⊧E P ∶ M ≡〈 A 〉 N → Σ[ Q ∈ CanonE V ] P ↠ decode-CanonE Q
⊧E-wn {A = Ω} (⊧P+∶M⊃N ,p _) with Lemma35e ⊧P+∶M⊃N
⊧E-wn {P = P} {A = Ω} (⊧P+∶M⊃N ,p _) | (P' ,p P↠P') = CanonΩ2CanonE P' ,p subst (λ x → P ↠ x) (decode-CanonΩE {P = P'}) P↠P'
⊧E-wn {V} {A = A ⇛ B} ⊧P∶M≡N = let 
  P'cA ,p PcA↠P'cA = ⊧E-wn (⊧P∶M≡N V (idRep V) (c A) (c A) (c A ⟦⟦ refSub ∶ idSub V ≡ idSub V ⟧⟧) ⊧c ⊧c ⊧c) in 
  app*-wnl {R = P'cA} PcA↠P'cA (cong₄ app* refl refl rep-idRep refl)

canonicityE : ∀ {V} {Γ : Context (decodeNTA V)} {P M A N} → Γ ⊢ P ∶ M ≡〈 A 〉 N →
  Σ[ Q ∈ CanonE _ ] P ↠ decode-CanonE Q
canonicityE Γ⊢P∶M≡N = {!!}

consistency : ∀ {δ : Proof ∅} → 〈〉 ⊢ δ ∶ ⊥ → Empty
consistency {δ} ⊢δ∶⊥ with soundness' {∅} ⊢δ∶⊥
consistency ⊢δ∶⊥ | bot ,p _ ,p ε ,p _ = NeutralP-not-closed ε
consistency ⊢δ∶⊥ | imp ε ε₁ ,p ⊥↠φ⊃ψ ,p x = bot-not-red-imp ⊥↠φ⊃ψ
