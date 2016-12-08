module PHOPL.Canon where

open import Data.Empty renaming (⊥ to Empty)
open import Data.Product renaming (_,_ to _,p_)
open import Prelims
open import PHOPL.Grammar
open import PHOPL.Red

data CanonProp : Set where
  bot : CanonProp
  imp : CanonProp → CanonProp → CanonProp

decode : ∀ {V} → CanonProp → Term V
decode bot = ⊥
decode (imp φ ψ) = decode φ ⊃ decode ψ

canon-nf : ∀ {V θ} {φ : Term V} → decode θ ⇒ φ → Empty
canon-nf {θ = bot} ()
canon-nf {θ = imp φ _} (impl θ⇒φ) = canon-nf {θ = φ} θ⇒φ
canon-nf {θ = imp _ ψ} (impr θ⇒φ) = canon-nf {θ = ψ} θ⇒φ

canon-nf' : ∀ {V} θ {φ ψ : Term V} → φ ↠ ψ → decode θ ≡ φ → decode θ ≡ ψ
canon-nf' θ (inc φ⇒ψ) θ≡φ = ⊥-elim (canon-nf {θ = θ} (subst (λ x → x ⇒ _) (≡-sym θ≡φ) φ⇒ψ))
canon-nf' _ ref θ≡φ = θ≡φ
canon-nf' θ (trans φ↠ψ ψ↠ψ') θ≡φ = canon-nf' θ ψ↠ψ' (canon-nf' θ φ↠ψ θ≡φ)

red-canon : ∀ {V} {φ ψ : Term V} {θ : CanonProp} →
  φ ↠ decode θ → φ ≃ ψ → ψ ↠ decode θ
red-canon {V} {φ} {ψ} {θ} φ↠θ φ≃ψ = 
  let cr χ θ↠χ ψ↠χ = diamond-CR (λ _ _ _ → diamond) (decode θ) ψ (trans (sym (sub-RT-RST φ↠θ)) φ≃ψ) in 
  subst (λ x → ψ ↠ x) (≡-sym (canon-nf' θ θ↠χ refl)) ψ↠χ

data is-⊃ {V} : Term V → Set where
  ⊃I : ∀ {φ} {ψ} → is-⊃ (φ ⊃ ψ)

imp-red-imp : ∀ {V} {E F : Term V} → E ↠ F → is-⊃ E → is-⊃ F
imp-red-imp (inc (impl _)) ⊃I = ⊃I
imp-red-imp (inc (impr _)) ⊃I = ⊃I
imp-red-imp ref is⊃E = is⊃E
imp-red-imp (trans E↠F F↠G) is⊃E = imp-red-imp F↠G (imp-red-imp E↠F is⊃E)

imp-not-red-bot : ∀ {V} {φ ψ : Term V} → φ ⊃ ψ ↠ ⊥ → Empty
imp-not-red-bot φ⊃ψ↠⊥ with imp-red-imp φ⊃ψ↠⊥ ⊃I
imp-not-red-bot φ⊃ψ↠⊥ | ()
