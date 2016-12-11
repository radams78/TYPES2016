module PHOPL.Red.RRed where
open import Data.Bool
open import Data.Product renaming (_,_ to _,p_)
open import Prelims
open import PHOPL.Grammar
open import PHOPL.Red.Base

infix 10 _⇒?_
_⇒?_ : ∀ {V K} → Expression V K → Expression V K → Set
_⇒?_ = RClose _⇒_

--TODO Duplication below
⇒?-appTl : ∀ {V} {M M' N : Term V} → M ⇒? M' → appT M N ⇒? appT M' N
⇒?-appTl = respects-R' _ _⇒_ (λ _ _ → appTl) _ _

⇒?-impl : ∀ {V} {φ φ' ψ : Term V} → φ ⇒? φ' → φ ⊃ ψ ⇒? φ' ⊃ ψ
⇒?-impl = respects-R' _ _⇒_ (λ _ _ → impl) _ _

⇒?-impr : ∀ {V} {φ ψ ψ' : Term V} → ψ ⇒? ψ' → φ ⊃ ψ ⇒? φ ⊃ ψ'
⇒?-impr = respects-R' _ _⇒_ (λ _ _ → impr) _ _

⇒?-imp*l : ∀ {V} {P P' Q : Path V} → P ⇒? P' → P ⊃* Q ⇒? P' ⊃* Q
⇒?-imp*l = respects-R' _ _⇒_ (λ _ _ → imp*l) _ _

⇒?-imp*r : ∀ {V} {P Q Q' : Path V} → Q ⇒? Q' → P ⊃* Q ⇒? P ⊃* Q'
⇒?-imp*r = respects-R' _ _⇒_ (λ _ _ → imp*r) _ _

⇒?-app*l : ∀ {V} {M N : Term V} {P P' Q} → P ⇒? P' → app* M N P Q ⇒? app* M N P' Q
⇒?-app*l = respects-R' _ _⇒_ (λ _ _ → app*l) _ _

⇒?-appPl : ∀ {V} {δ δ' ε : Proof V} → δ ⇒? δ' → appP δ ε ⇒? appP δ' ε
⇒?-appPl = respects-R' _ _⇒_ (λ _ _ → appPl) _ _

⇒?-dir : ∀ {V} {P Q : Path V} {d} → P ⇒? Q → dir d P ⇒? dir d Q
⇒?-dir = respects-R₂ (λ _ _ → dirR) _ _

⇒?-reff : ∀ {V} {M N : Term V} → M ⇒? N → reff M ⇒? reff N
⇒?-reff = respects-R₂ (λ _ _ → reffR) _ _

imp-osr-inj₁ : ∀ {V} {φ ψ χ : Term V} → φ ⊃ ψ ⇒ χ → Σ[ φ' ∈ Term V ] Σ[ ψ' ∈ Term V ]
  χ ≡ φ' ⊃ ψ' × φ ⇒? φ'
imp-osr-inj₁ {ψ = ψ} (impl {φ' = φ'} φ⊃φ') = φ' ,p ψ ,p refl ,p inc φ⊃φ'
imp-osr-inj₁ {φ = φ} (impr {ψ' = ψ'} _) = φ ,p ψ' ,p refl ,p ref

