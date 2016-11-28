module PHOPL.Red.Base where
open import Prelims.Closure
open import Data.Product renaming (_,_ to _,p_)
open import PHOPL.Grammar
open import PHOPL.PathSub

--Redex for a path ref ⊃* univ:
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

--TODO Do the same for nfappT and nfappP

data β : Reduction where
  βT : ∀ {V} {A} {M} {N} → β {V} -appTerm (ΛT A M ∷ N ∷ []) (M ⟦ x₀:= N ⟧)
  
data R₀ : Reduction
data nf : ∀ {V} {K} → Expression V K → Set

data R₀ where
  βR : ∀ {V} {φ} {δ} {ε} → nf (ΛP φ δ) → nf ε → R₀ {V} -appProof (ΛP φ δ ∷ ε ∷ []) (δ ⟦ x₀:= ε ⟧)
  dir-ref : ∀ {V} {φ} {d} → nf (reff φ) → R₀ {V} (-dir d) (reff φ ∷ []) (ΛP φ (var x₀))
  plus-univ : ∀ {V} {φ} {ψ} {δ} {ε} → nf (univ φ ψ δ ε) → R₀ {V} (-dir -plus) (univ φ ψ δ ε ∷ []) δ 
  minus-univ : ∀ {V} {φ} {ψ} {δ} {ε} → nf (univ φ ψ δ ε) → R₀ {V} (-dir -minus) (univ φ ψ δ ε ∷ []) ε
  ref⊃*univ : ∀ {V} {φ} {ψ} {χ} {δ} {ε} → nf (reff φ) → nf (univ ψ χ δ ε) → R₀ {V} -imp* (reff φ ∷ univ ψ χ δ ε ∷ []) (ru-redex φ ψ χ δ ε)
  univ⊃*ref : ∀ {V} {φ} {ψ} {χ} {δ} {ε} → nf (univ φ ψ δ ε) → nf (reff χ) → R₀ {V} -imp* (univ φ ψ δ ε ∷ reff χ ∷ []) (ur-redex φ ψ χ δ ε)
  univ⊃*univ : ∀ {V} {φ} {φ'} {ψ} {ψ'} {δ} {δ'} {ε} {ε'} → nf (univ φ ψ δ ε) → nf (univ φ' ψ' δ' ε') →
    R₀ {V} -imp* (univ φ ψ δ ε ∷ univ φ' ψ' δ' ε' ∷ []) (uu-redex φ φ' ψ ψ' δ δ' ε ε')
  ref⊃*ref : ∀ {V} {φ} {ψ} → nf (reff φ) → nf (reff ψ) → R₀ {V} -imp* (reff φ ∷ reff ψ ∷ []) (reff (φ ⊃ ψ))
  refref : ∀ {V} {M} {N} → nf (reff M) → nf (reff N) → R₀ {V} -app* (N ∷ N ∷ reff M ∷ reff N ∷ []) (reff (appT M N))
  βE : ∀ {V} {M} {N} {A} {P} {Q} → nf M → nf N → nf (λλλ A P) → nf Q → R₀ {V} -app* (M ∷ N ∷ λλλ A P ∷ Q ∷ []) 
    (P ⟦ x₂:= M ,x₁:= N ,x₀:= Q ⟧)
  reflam : ∀ {V} {N} {N'} {A} {M} {P} → nf N → nf N' → nf (reff (ΛT A M)) → nf P → not-ref P → R₀ {V} -app* (N ∷ N' ∷ reff (ΛT A M) ∷ P ∷ []) (M ⟦⟦ x₀::= P ∶ x₀:= N ∼ x₀:= N' ⟧⟧)

data nf where
  nfvar  : ∀ {V} {K} (x : Var V K) → nf (var x)
  nf⊥    : ∀ {V} → nf {V} ⊥
  nf⊃    : ∀ {V} {φ ψ : Term V} → nf φ → nf ψ → nf (φ ⊃ ψ)
  nfΛT   : ∀ {V} A {M : Term (V , -Term)} → nf M → nf (ΛT A M)
  nfappTvar : ∀ {V} (x : Var V -Term) {M} → nf M → nf (appT (var x) M)
  nfappT⊥   : ∀ {V} {M : Term V} → nf M → nf (appT ⊥ M)
  nfappT⊃   : ∀ {V} {M N P : Term V} → nf M → nf N → nf P → nf (appT (M ⊃ N) P)
  nfappTappT : ∀ {V} {M N P : Term V} → nf (appT M N) → nf P → nf (appT (appT M N) P)
  nfΛP   : ∀ {V} {φ : Term V} {δ} → nf φ → nf δ → nf (ΛP φ δ)
  nfappPvar : ∀ {V} (p : Var V -Proof) {δ} → nf δ → nf (appP (var p) δ)
  nfappPappP : ∀ {V} {δ ε ε' : Proof V} → nf (appP δ ε) → nf ε' → nf (appP (appP δ ε) ε')
  nfappPdir : ∀ {V d} {P : Path V} {δ} → nf (dir d P) → nf δ → nf (appP (dir d P) δ)
  nfdirvar : ∀ {V d} (P : Path V) → nf P → not-ref-univ P → nf (dir d P)
  nfreff : ∀ {V} {M : Term V} → nf M → nf (reff M)
  nf⊃*l  : ∀ {V} {P Q : Path V} → nf P → nf Q → not-ref-univ P → nf (P ⊃* Q)
  nf⊃*r  : ∀ {V} {P Q : Path V} → nf P → nf Q → not-ref-univ Q → nf (P ⊃* Q)
  nfuniv : ∀ {V} {φ ψ : Term V} {δ ε} → nf φ → nf ψ → nf δ → nf ε → nf (univ φ ψ δ ε)
  nfλλλ  : ∀ {V A} {P : Path (V , -Term , -Term , -Path)} → nf P → nf (λλλ A P)
  nfapp* : ∀ {V} {M N : Term V} {P Q} → nf M → nf N → nf P → nf Q → not-ref-λλλ P → nf (app* M N P Q)

data R : Reduction where
  βR : ∀ {V AA K} {c : Con (SK AA K)} {EE : ListAbs V AA} {F} → β c EE F → R c EE F
  R₀R : ∀ {V AA K} {c : Con (SK AA K)} {EE : ListAbs V AA} {F} → R₀ c EE F → R c EE F

open import Reduction PHOPL R public 

data NfDec {V} (M : Term V) : Set where
  nfNfDec : nf M → NfDec M
  redNfDec : ∀ {N} → M ⇒ N → NfDec M

nf-decidable : ∀ {V} (M : Term V) → NfDec M
nf-decidable (var x) = nfNfDec (nfvar x)
nf-decidable (app -bot []) = nfNfDec nf⊥
nf-decidable (app -imp (φ ∷ ψ ∷ [])) with nf-decidable φ
nf-decidable (app -imp (φ ∷ ψ ∷ [])) | nfNfDec nfφ with nf-decidable ψ
nf-decidable (app -imp (φ ∷ ψ ∷ [])) | nfNfDec nfφ | nfNfDec nfψ = nfNfDec (nf⊃ nfφ nfψ)
nf-decidable (app -imp (φ ∷ ψ ∷ [])) | nfNfDec nfφ | redNfDec ψ⇒ψ' = redNfDec (app (appr (appl ψ⇒ψ')))
nf-decidable (app -imp (φ ∷ ψ ∷ [])) | redNfDec φ⇒φ' = redNfDec (app (appl φ⇒φ'))
nf-decidable (app (-lamTerm A) (M ∷ [])) with nf-decidable M
nf-decidable (app (-lamTerm A) (M ∷ [])) | nfNfDec nfM = nfNfDec (nfΛT A nfM)
nf-decidable (app (-lamTerm A) (M ∷ [])) | redNfDec M⇒M' = redNfDec (app (appl M⇒M'))
nf-decidable (app -appTerm (M ∷ N ∷ [])) with nf-decidable M
nf-decidable (app -appTerm (M ∷ N ∷ [])) | nfNfDec nfM with nf-decidable N
nf-decidable (app -appTerm (var x ∷ N ∷ [])) | nfNfDec nfM | nfNfDec nfN = nfNfDec (nfappTvar x nfN)
nf-decidable (app -appTerm (app -bot [] ∷ N ∷ [])) | nfNfDec nfM | nfNfDec nfN = nfNfDec (nfappT⊥ nfN)
nf-decidable (app -appTerm (app -imp (φ ∷ ψ ∷ []) ∷ N ∷ [])) | nfNfDec (nf⊃ nfφ nfψ) | nfNfDec nfN = nfNfDec (nfappT⊃ nfφ nfψ nfN)
nf-decidable (app -appTerm (app (-lamTerm A) (M ∷ []) ∷ N ∷ [])) | nfNfDec nfM | nfNfDec nfN = redNfDec (redex (βR βT))
nf-decidable (app -appTerm (app -appTerm (M₁ ∷ M₂ ∷ []) ∷ N ∷ [])) | nfNfDec nfM | nfNfDec nfN = nfNfDec (nfappTappT nfM nfN)
nf-decidable (app -appTerm (M ∷ N ∷ [])) | nfNfDec nfM | redNfDec N⇒N' = redNfDec (app (appr (appl N⇒N')))
nf-decidable (app -appTerm (M ∷ N₁ ∷ [])) | redNfDec M⇒M' = redNfDec (app (appl M⇒M'))

SN-imp-WN : ∀ {V} {M : Term V} → SN M → Σ[ N ∈ Term V ] nf N × M ↠ N
SN-imp-WN {M = M} (SNI _ SNM) with nf-decidable M
SN-imp-WN {M = M} (SNI .M SNM) | nfNfDec nfM = M ,p nfM ,p ref
SN-imp-WN {M = M} (SNI .M SNM) | redNfDec M⇒M' = 
  let M₀ ,p nfM₀ ,p M'↠M₀ = SN-imp-WN (SNM _ M⇒M') in 
  M₀ ,p nfM₀ ,p RTClose.trans (inc M⇒M') M'↠M₀
