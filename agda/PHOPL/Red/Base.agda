module PHOPL.Red.Base where
open import Prelims.Closure
open import Data.Product renaming (_,_ to _,p_)
open import PHOPL.Grammar
open import PHOPL.PathSub

{--Redex for a path ref ⊃* univ:
ru-redex-half : ∀ {V} → Term V → Term V → Proof V → Proof V
ru-redex-half {V} φ ψ δ = ΛP (φ ⊃ ψ) (ΛP (φ ⇑) (appP (δ ⇑ ⇑) (appP (var x₁) (var x₀))))

ru-redex : ∀ {V} → Term V → Term V → Term V → Proof V → Proof V → Path V
ru-redex φ ψ χ δ ε = univ (φ ⊃ ψ) (φ ⊃ χ) (ru-redex-half φ ψ δ) (ru-redex-half φ χ ε)

--Redex for a path univ ⊃* ref:
ur-redex-half : ∀ {V} → Term V → Term V → Term V → Proof V → Proof V
ur-redex-half φ ψ χ δ = ΛP (φ ⊃ ψ) (ΛP (χ ⇑) (appP (var x₁) (appP (δ ⇑ ⇑) (var x₀))))

ur-redex : ∀ {V} → Term V → Term V → Term V → Proof V → Proof V → Path V
ur-redex φ ψ χ δ ε = univ (φ ⊃ χ) (ψ ⊃ χ) (ur-redex-half φ χ ψ ε) (ur-redex-half ψ χ φ δ)

--Redex for a path univ ⊃* univ;
uu-redex-half : ∀ {V} → Term V → Term V → Term V → Proof V → Proof V → Proof V
uu-redex-half φ φ' ψ δ ε = ΛP (φ ⊃ φ') (ΛP (ψ ⇑) (appP (δ ⇑ ⇑) (appP (var x₁) (appP (ε ⇑ ⇑) (var x₀)))))

uu-redex : ∀ {V} → Term V → Term V → Term V → Term V → Proof V → Proof V → Proof V → Proof V → Path V
uu-redex φ φ' ψ ψ' δ δ' ε ε' = univ (φ ⊃ φ') (ψ ⊃ ψ') (uu-redex-half φ φ' ψ δ' ε) (uu-redex-half ψ ψ' φ ε' δ)

data not-ref-univ {V} : Path V → Set where
  nruvar : ∀ e → not-ref-univ (var e)
  nru⊃*  : ∀ {P} {Q} → not-ref-univ (P ⊃* Q)
  nruλλλ : ∀ {A P} → not-ref-univ (λλλ A P)
  nruapp* : ∀ {M N P Q} → not-ref-univ (app* M N P Q)

data not-ref-λλλ {V} : Path V → Set where
  nrλvar : ∀ e → not-ref-λλλ (var e)
  nrλ⊃*  : ∀ {P Q} → not-ref-λλλ (P ⊃* Q)
  nrλuniv : ∀ {φ ψ δ ε} → not-ref-λλλ (univ φ ψ δ ε)
  nrλapp* : ∀ {M N P Q} → not-ref-λλλ (app* M N P Q)

data not-ref {V} : Path V → Set where
  nrλvar : ∀ e → not-ref (var e)
  nrλ⊃*  : ∀ {P Q} → not-ref (P ⊃* Q)
  nrλuniv : ∀ {φ ψ δ ε} → not-ref (univ φ ψ δ ε)
  nrλλλλ : ∀ {A P} → not-ref (λλλ A P)
  nrλapp* : ∀ {M N P Q} → not-ref (app* M N P Q)

--TODO Do the same for nfappT and nfappP -}

data β : Reduction where
  βT : ∀ {V} {A} {M} {N} → β {V} -appTerm (ΛT A M ∷ N ∷ []) (M ⟦ x₀:= N ⟧)
  
