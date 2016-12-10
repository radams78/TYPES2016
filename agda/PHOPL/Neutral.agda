module PHOPL.Neutral where

open import Data.Product renaming (_,_ to _,p_)
open import Data.Sum
open import Prelims
open import PHOPL.Grammar
open import PHOPL.Canon
open import PHOPL.Red

data NeutralT : Alphabet → Set where

data NeutralE (V : Alphabet) : Set where
  app*N : Term V → Term V → NeutralE V → Path V → NeutralE V

data NeutralP (V : Alphabet) : Set where
  app : NeutralP V → Proof V → NeutralP V
  plusN : NeutralE V → NeutralP V
  minusN : NeutralE V → NeutralP V

decode-NeutralT : ∀ {V} → NeutralT V → Term V
decode-NeutralT ()

decode-NeutralE : ∀ {V} → NeutralE V → Path V
decode-NeutralE (app*N M N P Q) = app* M N (decode-NeutralE P) Q

decode-NeutralP : ∀ {V} → NeutralP V → Proof V
decode-NeutralP (app δ ε) = appP (decode-NeutralP δ) ε
decode-NeutralP (plusN P) = plus (decode-NeutralE P)
decode-NeutralP (minusN P) = minus (decode-NeutralE P)

nrepE : ∀ {U V} → Rep U V → NeutralE U → NeutralE V
nrepE ρ (app*N M N ν P) = app*N (M 〈 ρ 〉) (N 〈 ρ 〉) (nrepE ρ ν) (P 〈 ρ 〉)

decode-nrepE : ∀ {U V} {ρ : Rep U V} {ν : NeutralE U} → decode-NeutralE (nrepE ρ ν) ≡ decode-NeutralE ν 〈 ρ 〉
decode-nrepE {ρ = ρ} {app*N M N ν P} = cong (λ x → app* (M 〈 ρ 〉) (N 〈 ρ 〉) x (P 〈 ρ 〉)) decode-nrepE

nrepP : ∀ {U V} → Rep U V → NeutralP U → NeutralP V
nrepP ρ (app ν δ) = app (nrepP ρ ν) (δ 〈 ρ 〉)
nrepP ρ (plusN P) = plusN (nrepE ρ P)
nrepP ρ (minusN P) = minusN (nrepE ρ P)

decode-nrepP : ∀ {U V} {ρ : Rep U V} {ν : NeutralP U} → decode-NeutralP (nrepP ρ ν) ≡ decode-NeutralP ν 〈 ρ 〉
decode-nrepP {ρ = ρ} {ν = app ν δ} = cong (λ x → appP x (δ 〈 ρ 〉)) (decode-nrepP {ρ = ρ} {ν = ν})
decode-nrepP {ν = plusN P} = cong plus decode-nrepE
decode-nrepP {ν = minusN P} = cong minus decode-nrepE

neutralE-osr : ∀ {V} {P : NeutralE V} {Q} → decode-NeutralE P ⇒ Q →
  Σ[ Q' ∈ NeutralE V ] Q ≡ decode-NeutralE Q'
neutralE-osr {P = app*N M N (app*N L L' P P') Q} (app*l P⇒Q) = 
  let Q' ,p Q≡Q' = neutralE-osr {P = app*N L L' P P'} P⇒Q in 
  (app*N M N Q' Q) ,p (cong (λ x → app* M N x Q) Q≡Q')

neutralP-red : ∀ {V} (δ : NeutralP V) {ε} → RClose _⇒_ (decode-NeutralP δ) ε →
  Σ[ ε' ∈ NeutralP V ] ε ≡ decode-NeutralP ε'
neutralP-red (app (app δ ε) ε') (inc (appPl δε⇒χ)) = 
  let χ' ,p χ≡χ' = neutralP-red (app δ ε) (inc δε⇒χ) in 
  app χ' ε' ,p cong (λ x → appP x ε') χ≡χ'
neutralP-red (app (plusN (app*N M N P Q)) δ) (inc (appPl δ⇒χ)) = 
  let χ' ,p χ≡χ' = neutralP-red (plusN (app*N M N P Q)) (inc δ⇒χ) in
  app χ' δ ,p cong (λ x → appP x δ) χ≡χ'
neutralP-red (app (minusN (app*N M N P Q)) δ) (inc (appPl δ⇒χ)) =
  let χ' ,p χ≡χ' = neutralP-red (minusN (app*N M N P Q)) (inc δ⇒χ) in
  app χ' δ ,p cong (λ x → appP x δ) χ≡χ'
neutralP-red (plusN P) (inc (plusR P⇒Q)) = 
  let Q' ,p Q≡Q' = neutralE-osr P⇒Q in 
  plusN Q' ,p cong plus Q≡Q'
neutralP-red (minusN P) (inc (minusR P⇒Q)) = 
  let Q' ,p Q≡Q' = neutralE-osr P⇒Q in 
  minusN Q' ,p cong minus Q≡Q'
neutralP-red δ ref = δ ,p refl

-- Canonical Paths

data CanonE (V : Alphabet) : Set where
  neutral : NeutralE V → CanonE V
  reffC   : Term V → CanonE V
  univC   : Term V → Term V → Proof V → Proof V → CanonE V

decode-CanonE : ∀ {V} → CanonE V → Path V
decode-CanonE (neutral P) = decode-NeutralE P
decode-CanonE (reffC M) = reff M
decode-CanonE (univC φ ψ δ ε) = univ φ ψ δ ε

Lemma35a : ∀ {V} {P : Path V} {pp : snocList (Var V -Proof)} {δ} →
  APPP (plus P) (snocmap var pp) ⇒ δ →
  Σ[ Q ∈ Path V ] P ⇒ Q × δ ≡ APPP (plus Q) (snocmap var pp) ⊎
  Σ[ Q ∈ CanonE V ] P ≡ decode-CanonE Q
Lemma35a {pp = []} (plusR P⇒Q) = inj₁ (_ ,p P⇒Q ,p refl)
Lemma35a {pp = [] snoc _} (appPl (plusR P⇒Q)) = inj₁ (_ ,p P⇒Q ,p refl)
Lemma35a {pp = [] snoc _} refplus = inj₂ (reffC _ ,p refl)
Lemma35a {pp = pp snoc x snoc _} (appPl Pppx⇒δ) with Lemma35a {pp = pp snoc x} Pppx⇒δ
Lemma35a {pp = _ snoc _ snoc y} (appPl _) | inj₁ (Q ,p P⇒Q ,p δ≡Qppx) = inj₁ (Q ,p P⇒Q ,p cong (λ z → appP z (var y)) δ≡Qppx)
Lemma35a {pp = _ snoc _ snoc _} (appPl _) | inj₂ Pcanon = inj₂ Pcanon

Lemma35b : ∀ {V} {P : Path V} (pp : snocList (Var V -Proof)) {α β} →
  α ↠ β → α ≡ APPP (plus P) (snocmap var pp) →
  Σ[ Q ∈ Path V ] P ↠ Q × β ≡ APPP (plus Q) (snocmap var pp) ⊎
  Σ[ Q ∈ CanonE V ] P ↠ decode-CanonE Q
Lemma35b pp {β = β} (inc α⇒β) α≡Ppp with Lemma35a {pp = pp} (subst (λ x → x ⇒ β) α≡Ppp α⇒β) 
Lemma35b _ (inc α⇒β) α≡Ppp | inj₁ (Q ,p P⇒Q ,p β≡Q+pp) = inj₁ (Q ,p inc P⇒Q ,p β≡Q+pp)
Lemma35b {P = P} _ (inc α⇒β) α≡Ppp | inj₂ (Q ,p P≡Q) = inj₂ (Q ,p subst (λ x → P ↠ x) P≡Q ref)
Lemma35b {P = P} _ ref β≡Ppp = inj₁ (P ,p ref ,p β≡Ppp)
Lemma35b pp (trans α↠β β↠γ) α≡P+pp with Lemma35b pp α↠β α≡P+pp
Lemma35b pp (trans α↠β β↠γ) α≡P+pp | inj₁ (Q ,p P↠Q ,p β≡Q+pp) with Lemma35b pp β↠γ β≡Q+pp
Lemma35b pp (trans α↠β β↠γ) α≡P+pp | inj₁ (Q ,p P↠Q ,p β≡Q+pp) | inj₁ (R ,p Q↠R ,p γ≡R+pp) = inj₁ (R ,p trans P↠Q Q↠R ,p γ≡R+pp)
Lemma35b pp (trans α↠β β↠γ) α≡P+pp | inj₁ (Q ,p P↠Q ,p β≡Q+pp) | inj₂ (R ,p Q↠R) = inj₂ (R ,p (trans P↠Q Q↠R))
Lemma35b pp (trans α↠β β↠γ) α≡P+pp | inj₂ Predcanon = inj₂ Predcanon

Lemma35c : ∀ {V} {P : Path V} (pp : snocList (Var V -Proof)) (δ : NeutralP V) →
  APPP (plus P) (snocmap var pp) ↠ decode-NeutralP δ →
  Σ[ Q ∈ CanonE V ] P ↠ decode-CanonE Q
Lemma35c pp _ P+pp↠δ with Lemma35b pp P+pp↠δ refl
Lemma35c [] (app _ _) _ | inj₁ (_ ,p _ ,p ())
Lemma35c {P = P} [] (plusN R) _ | inj₁ (_ ,p P↠Q ,p R+≡Q+) = (neutral R) ,p (subst (λ x → P ↠ x) (≡-sym (plus-inj R+≡Q+)) P↠Q)
Lemma35c [] (minusN _) _ | inj₁ (_ ,p _ ,p ())
Lemma35c {P = P} (pp snoc p) (app δ x) P+pp↠δ | inj₁ (Q ,p P↠Q ,p Q+pp≡δ) = 
  Lemma35c pp δ (subst (λ x₃ → APPP (plus P) (snocmap var pp) ↠ x₃) (≡-sym (appP-injl Q+pp≡δ)) (↠-APPP (snocmap var pp) (↠-plus P↠Q)))
Lemma35c (pp snoc p) (plusN x) P+pp↠δ | inj₁ (Q ,p P↠Q ,p ())
Lemma35c (pp snoc p) (minusN x) P+pp↠δ | inj₁ (Q ,p P↠Q ,p ())
Lemma35c _ _ P+pp↠δ | inj₂ Pcanon = Pcanon
