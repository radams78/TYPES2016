module PHOML.Neutral where

open import Data.Product renaming (_,_ to _,p_)
open import Data.Sum
open import Prelims
open import PHOML.Grammar
open import PHOML.Red

data NeutralT : Alphabet → Set where

data NeutralE (V : Alphabet) : Set where
  app*N : Term V → Term V → NeutralE V → Path V → NeutralE V
  imp*l : NeutralE V → Path V → NeutralE V
  imp*r : Path V → NeutralE V → NeutralE V

data NeutralP (V : Alphabet) : Set where
  var : Var V -Proof → NeutralP V
  app : NeutralP V → Proof V → NeutralP V
  dirN : Dir → NeutralE V → NeutralP V

decode-NeutralT : ∀ {V} → NeutralT V → Term V
decode-NeutralT ()

decode-NeutralE : ∀ {V} → NeutralE V → Path V
decode-NeutralE (app*N M N P Q) = app* M N (decode-NeutralE P) Q
decode-NeutralE (imp*l P Q) = decode-NeutralE P ⊃* Q
decode-NeutralE (imp*r P Q) = P ⊃* decode-NeutralE Q

decode-NeutralP : ∀ {V} → NeutralP V → Proof V
decode-NeutralP (var p) = var p
decode-NeutralP (app δ ε) = appP (decode-NeutralP δ) ε
decode-NeutralP (dirN d P) = dir d (decode-NeutralE P)

nrepE : ∀ {U V} → Rep U V → NeutralE U → NeutralE V
nrepE ρ (app*N M N ν P) = app*N (M 〈 ρ 〉) (N 〈 ρ 〉) (nrepE ρ ν) (P 〈 ρ 〉)
nrepE ρ (imp*l P Q) = imp*l (nrepE ρ P) (Q 〈 ρ 〉)
nrepE ρ (imp*r P Q) = imp*r (P 〈 ρ 〉) (nrepE ρ Q)

decode-nrepE : ∀ {U V} {ρ : Rep U V} (ν : NeutralE U) → decode-NeutralE (nrepE ρ ν) ≡ decode-NeutralE ν 〈 ρ 〉
decode-nrepE {ρ = ρ} {app*N M N ν P} = cong (λ x → app* (M 〈 ρ 〉) (N 〈 ρ 〉) x (P 〈 ρ 〉)) (decode-nrepE ν)
decode-nrepE {ρ = ρ} {imp*l P Q} = cong (λ x → x ⊃* Q 〈 ρ 〉) (decode-nrepE P)
decode-nrepE {ρ = ρ} {imp*r P Q} = cong (λ x → P 〈 ρ 〉 ⊃* x) (decode-nrepE Q)

nrepP : ∀ {U V} → Rep U V → NeutralP U → NeutralP V
nrepP ρ (var p) = var (ρ _ p)
nrepP ρ (app ν δ) = app (nrepP ρ ν) (δ 〈 ρ 〉)
nrepP ρ (dirN d P) = dirN d (nrepE ρ P)

decode-nrepP : ∀ {U V} {ρ : Rep U V} {ν : NeutralP U} → decode-NeutralP (nrepP ρ ν) ≡ decode-NeutralP ν 〈 ρ 〉
decode-nrepP {ρ = ρ} {ν = var p} = refl
decode-nrepP {ρ = ρ} {ν = app ν δ} = cong (λ x → appP x (δ 〈 ρ 〉)) (decode-nrepP {ρ = ρ} {ν = ν})
decode-nrepP {ν = dirN d P} = cong (dir d) (decode-nrepE P)

reflect-neutralE : ∀ {U V} (P : Path U) (Q : NeutralE V) (ρ : Rep U V) →
  P 〈 ρ 〉 ≡ decode-NeutralE Q → Σ[ P' ∈ NeutralE U ] P ≡ decode-NeutralE P'
reflect-neutralE (var _) (app*N _ _ _ _) _ ()
reflect-neutralE (var _) (imp*l _ _) _ ()
reflect-neutralE (var _) (imp*r _ _) _ ()
reflect-neutralE (app -ref _) (app*N _ _ _ _) _ ()
reflect-neutralE (app -ref _) (imp*l _ _) _ ()
reflect-neutralE (app -ref _) (imp*r _ _) _ ()
reflect-neutralE (app -imp* _) (app*N _ _ _ _) _ ()
reflect-neutralE (app -imp* (P ∷ Q ∷ [])) (imp*l P' Q') ρ Pρ≡Q = 
  let P₀ ,p P₀≡P = reflect-neutralE (P) (P') ρ (⊃*-injl Pρ≡Q) in
  imp*l P₀ Q ,p cong (λ x → x ⊃* Q) P₀≡P
reflect-neutralE (app -imp* (P ∷ Q ∷ [])) (imp*r P' Q') ρ Pρ≡Q = 
  let Q₀ ,p Q₀≡Q = reflect-neutralE (Q) (Q') ρ (⊃*-injr Pρ≡Q) in 
  imp*r P Q₀ ,p cong (λ x → P ⊃* x) Q₀≡Q
reflect-neutralE (app -univ _) (app*N _ _ _ _) _ ()
reflect-neutralE (app -univ _) (imp*l P Q) _ ()
reflect-neutralE (app -univ _) (imp*r P Q) _ ()
reflect-neutralE (app (-lll _) _) (app*N _ _ _ _) _ ()
reflect-neutralE (app (-lll _) _) (imp*l P Q) _ ()
reflect-neutralE (app (-lll _) _) (imp*r P Q) _ ()
reflect-neutralE (app -app* (M₁ ∷ M₂ ∷ P₁ ∷ P₂ ∷ [])) (app*N N₁ N₂ Q₁ Q₂) (ρ) Pρ≡Q = 
  let P₁' ,p P₁≡P₁' = reflect-neutralE P₁ Q₁ ρ (app*-injl Pρ≡Q) in
  (app*N M₁ M₂ P₁' P₂) ,p (cong (λ x → app* M₁ M₂ x P₂) P₁≡P₁')
reflect-neutralE (app -app* _) (imp*l P Q) _ ()
reflect-neutralE (app -app* _) (imp*r P Q) _ ()

neutralE-osr : ∀ {V} (P : NeutralE V) {Q} → decode-NeutralE P ⇒ Q →
  Σ[ Q' ∈ NeutralE V ] Q ≡ decode-NeutralE Q'
neutralE-osr (app*N M M' (app*N N N' P P') Q) (app*l P⇒Q) = 
  let Q' ,p Q≡Q' = neutralE-osr (app*N N N' P P') P⇒Q in
  app*N M M' Q' Q ,p (cong (λ x → app* M M' x Q) Q≡Q')
neutralE-osr (app*N M M' (imp*l P P') Q) (app*l P⇒Q) =
  let Q' ,p Q≡Q' = neutralE-osr (imp*l P P') P⇒Q in
  app*N M M' Q' Q ,p (cong (λ x → app* M M' x Q) Q≡Q')
neutralE-osr (app*N M M' (imp*r P P') Q) (app*l P⇒Q) =
  let Q' ,p Q≡Q' = neutralE-osr (imp*r P P') P⇒Q in
  app*N M M' Q' Q ,p (cong (λ x → app* M M' x Q) Q≡Q')
neutralE-osr (imp*l (app*N M M' P P') Q) (imp*l P⇒Q) = 
  let P' ,p P≡P' = neutralE-osr (app*N M M' P P') P⇒Q in
  imp*l P' Q ,p cong (λ x → x ⊃* Q) P≡P'
neutralE-osr (imp*l (app*N M M' P P') Q) (imp*r P⇒Q) =
  imp*l (app*N M M' P P') _ ,p refl
neutralE-osr (imp*l (imp*l P P') Q) (imp*l Q⇒Q') =
  let P' ,p P≡P' = neutralE-osr (imp*l P P') Q⇒Q' in
  imp*l P' Q ,p cong (λ x → x ⊃* Q) P≡P'
neutralE-osr (imp*l (imp*l P P') Q) (imp*r P⇒Q) =
  imp*l (imp*l P P') _ ,p refl
neutralE-osr (imp*l (imp*r P P') Q) (imp*l PP'⇒P₀) =
  let P₀ ,p P₀≡P₀ = neutralE-osr (imp*r P P') PP'⇒P₀ in
  imp*l P₀ Q ,p cong (λ x → x ⊃* Q) P₀≡P₀
neutralE-osr (imp*l (imp*r P P') Q) (imp*r P⇒Q) =
  imp*l (imp*r P P') _ ,p refl
neutralE-osr (imp*r _ (app*N M N Q Q')) (imp*l _) =
  imp*r _ (app*N M N Q Q') ,p refl
neutralE-osr (imp*r P (app*N M N Q Q')) (imp*r QQ'⇒Q₀) =
  let Q₀ ,p Q₀≡Q₀ = neutralE-osr (app*N M N Q Q') QQ'⇒Q₀ in
  imp*r P Q₀ ,p (cong (λ x → P ⊃* x) Q₀≡Q₀)
neutralE-osr (imp*r _ (imp*l Q Q')) (imp*l _) =
  imp*r _ (imp*l Q Q') ,p refl
neutralE-osr (imp*r P (imp*l Q Q')) (imp*r Q⊃*Q'⇒Q₀) =
  let Q₀ ,p Q₀≡Q₀ = neutralE-osr (imp*l Q Q') Q⊃*Q'⇒Q₀ in
  imp*r P Q₀ ,p (cong (λ x → P ⊃* x) Q₀≡Q₀)
neutralE-osr (imp*r _ (imp*r Q Q')) (imp*l _) =
  imp*r _ (imp*r Q Q') ,p refl
neutralE-osr (imp*r P (imp*r Q Q')) (imp*r Q⊃*Q'⇒Q₀) =
  let Q₀ ,p Q₀≡Q₀ = neutralE-osr (imp*r Q Q') Q⊃*Q'⇒Q₀ in
  imp*r P Q₀ ,p (cong (λ x → P ⊃* x) Q₀≡Q₀)

neutralP-red : ∀ {V} (δ : NeutralP V) {ε} → RClose _⇒_ (decode-NeutralP δ) ε →
  Σ[ ε' ∈ NeutralP V ] ε ≡ decode-NeutralP ε'
neutralP-red (var _) (inc ())
neutralP-red (app (var _) _) (inc (appPl ()))
neutralP-red (app (app δ ε) ε') (inc (appPl δε⇒χ)) = 
  let χ' ,p χ≡χ' = neutralP-red (app δ ε) (inc δε⇒χ) in 
  app χ' ε' ,p cong (λ x → appP x ε') χ≡χ'
neutralP-red (app (dirN d (app*N M N P Q)) δ) (inc (appPl δ⇒χ)) = 
  let χ' ,p χ≡χ' = neutralP-red (dirN d (app*N M N P Q)) (inc δ⇒χ) in
  app χ' δ ,p cong (λ x → appP x δ) χ≡χ'
neutralP-red (app (dirN d (imp*l P P')) δ) (inc (appPl P⊃*P'⇒χ)) =
  let χ' ,p χ≡χ' = neutralP-red (dirN d (imp*l P P')) (inc P⊃*P'⇒χ) in
  app χ' δ ,p cong (λ x → appP x δ) χ≡χ'
neutralP-red (app (dirN d (imp*r P P')) δ) (inc (appPl P⊃*P'⇒χ)) =
  let χ' ,p χ≡χ' = neutralP-red (dirN d (imp*r P P')) (inc P⊃*P'⇒χ) in
  app χ' δ ,p cong (λ x → appP x δ) χ≡χ'
neutralP-red (dirN d P) (inc (dirR P⇒Q)) = 
  let Q' ,p Q≡Q' = neutralE-osr P P⇒Q in 
  dirN d Q' ,p cong (dir d) Q≡Q'
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

reflect-canonE : ∀ {U V} {P : Path U} {Q : CanonE V} {ρ : Rep U V} →
  P 〈 ρ 〉 ≡ decode-CanonE Q → Σ[ P' ∈ CanonE U ] P ≡ decode-CanonE P'
reflect-canonE {P = P} {neutral Q} {ρ} Pρ≡Q = 
  let P' ,p P≡P' = reflect-neutralE P Q ρ Pρ≡Q in
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
Lemma35a {pp = [] snoc _} (appPl (dirR P⇒Q)) = inj₁ (_ ,p P⇒Q ,p refl)
Lemma35a {pp = [] snoc _} refdir = inj₂ (reffC _ ,p refl)
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
