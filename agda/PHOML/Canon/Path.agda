module PHOML.Canon.Path where
open import Data.Sum
open import Data.Product renaming (_,_ to _,p_)
open import Prelims
open import PHOML.Grammar
open import PHOML.Neutral
open import PHOML.Red

data CanonE (V : Alphabet) : Set where
  neutral : NeutralE V → CanonE V
  reffC   : Term V → CanonE V
  univC   : Term V → Term V → Proof V → Proof V → CanonE V

decode-CanonE : ∀ {V} → CanonE V → Path V
decode-CanonE (neutral P) = decode-NeutralE P
decode-CanonE (reffC M) = reff M
decode-CanonE (univC φ ψ δ ε) = univ φ ψ δ ε

reflect-canonE : ∀ {U V} {P : Path U} {Q : CanonE V} {ρ : Rep U V} →
  P 〈 ρ 〉 ≡ decode-CanonE Q → Σ[ P' ∈ CanonE U ] P ≡ decode-CanonE P'
reflect-canonE {P = P} {neutral Q} {ρ} Pρ≡Q = 
  let P' ,p P≡P' = reflect-NeutralE P Q ρ Pρ≡Q in
  neutral P' ,p P≡P'
reflect-canonE {P = var _} {reffC _} ()
reflect-canonE {P = app -ref (M ∷ [])} {reffC N} Pρ≡refM = 
  (reffC M) ,p refl
reflect-canonE {P = app -imp* x₁} {reffC M} ()
reflect-canonE {P = app -univ x₁} {reffC M} ()
reflect-canonE {P = app (-lll x) x₁} {reffC M} ()
reflect-canonE {P = app -app* x₁} {reffC M} ()
reflect-canonE {P = var x} {univC x₁ x₂ x₃ x₄} ()
reflect-canonE {P = app -ref x₁} {univC x₂ x₃ x₄ x₅} ()
reflect-canonE {P = app -imp* x₁} {univC x₂ x₃ x₄ x₅} ()
reflect-canonE {P = app -univ (M₁ ∷ M₂ ∷ δ₁ ∷ δ₂ ∷ [])} {univC N₁ N₂ Q₁ Q₂} Pρ≡Q = univC M₁ M₂ δ₁ δ₂ ,p refl
reflect-canonE {P = app (-lll x) x₁} {univC x₂ x₃ x₄ x₅} ()
reflect-canonE {P = app -app* x₁} {univC x₂ x₃ x₄ x₅} ()

Lemma35a : ∀ {V} {P : Path V} {pp : snocList (Var V -Proof)} {δ d} →
  APPP (dir d P) (snocmap var pp) ⇒ δ →
  Σ[ Q ∈ Path V ] P ⇒ Q × δ ≡ APPP (dir d Q) (snocmap var pp) ⊎
  Σ[ Q ∈ CanonE V ] P ≡ decode-CanonE Q
Lemma35a {pp = []} (dirR P⇒Q) = inj₁ (_ ,p P⇒Q ,p refl)
Lemma35a {pp = []} refdir = inj₂ ((reffC _) ,p refl)
Lemma35a {pp = []} univplus = inj₂ ((univC _ _ _ _) ,p refl)
Lemma35a {pp = [] snoc p} (appPl univplus) = inj₂ ((univC _ _ _ _) ,p refl)
Lemma35a {pp = [] snoc _} (appPl (dirR P⇒Q)) = inj₁ (_ ,p P⇒Q ,p refl)
Lemma35a {pp = [] snoc _} (appPl refdir) = inj₂ (reffC _ ,p refl)
Lemma35a {pp = pp snoc x snoc _} (appPl Pppx⇒δ) with Lemma35a {pp = pp snoc x} Pppx⇒δ
Lemma35a {pp = _ snoc _ snoc y} (appPl _) | inj₁ (Q ,p P⇒Q ,p δ≡Qppx) = inj₁ (Q ,p P⇒Q ,p cong (λ z → appP z (var y)) δ≡Qppx)
Lemma35a {pp = _ snoc _ snoc _} (appPl _) | inj₂ Pcanon = inj₂ Pcanon

Lemma35b : ∀ {V} {P : Path V} (pp : snocList (Var V -Proof)) {α β d} →
  α ↠ β → α ≡ APPP (dir d P) (snocmap var pp) →
  Σ[ Q ∈ Path V ] P ↠ Q × β ≡ APPP (dir d Q) (snocmap var pp) ⊎
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

Lemma35c : ∀ {V} {P : Path V} (pp : snocList (Var V -Proof)) (δ : NeutralP V) {d} →
  APPP (dir d P) (snocmap var pp) ↠ decode-NeutralP δ →
  Σ[ Q ∈ CanonE V ] P ↠ decode-CanonE Q
Lemma35c pp _ P+pp↠δ with Lemma35b pp P+pp↠δ refl
Lemma35c [] (var _) _ | inj₁ (_ ,p _ ,p ())
Lemma35c (pp snoc p) (var q) P+pp↠q | inj₁ (_ ,p _ ,p ())
Lemma35c [] (app _ _) _ | inj₁ (_ ,p _ ,p ())
Lemma35c {P = P} [] (dirN -plus R) {d = -plus} _ | inj₁ (_ ,p P↠Q ,p R+≡Q+) = (neutral R) ,p (subst (λ x → P ↠ x) (≡-sym (dir-inj R+≡Q+)) P↠Q)
Lemma35c {P = P} [] (dirN -plus R) {d = -minus} _ | inj₁ (_ ,p _ ,p ())
Lemma35c {P = P} [] (dirN -minus R) {d = -plus} _ | inj₁ (_ ,p _ ,p ())
Lemma35c {P = P} [] (dirN -minus R) {d = -minus} _ | inj₁ (_ ,p P↠Q ,p R+≡Q+) = (neutral R) ,p (subst (λ x → P ↠ x) (≡-sym (dir-inj R+≡Q+)) P↠Q)
Lemma35c {P = P} (pp snoc p) (app δ x) {d} P+pp↠δ | inj₁ (Q ,p P↠Q ,p Q+pp≡δ) = 
  Lemma35c pp δ (subst (λ x₃ → APPP (dir d P) (snocmap var pp) ↠ x₃) (≡-sym (appP-injl Q+pp≡δ)) (↠-APPP (snocmap var pp) (↠-dir P↠Q)))
Lemma35c (pp snoc p) (dirN _ x) P+pp↠δ | inj₁ (Q ,p P↠Q ,p ())
Lemma35c _ _ P+pp↠δ | inj₂ Pcanon = Pcanon
