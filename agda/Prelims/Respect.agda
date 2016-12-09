module Prelims.Respect where
open import Level
open import Relation.Binary

Respects : ∀ {i} {A : Set} → (A → A) → Rel A i → Set i
Respects f R = ∀ x y → R x y → R (f x) (f y)

Respects-dep : ∀ {i} {A : Set} {B : A → Set} (R : ∀ a → Rel (B a) i) {a b : A}
  (f : B a → B b) → Set i
Respects-dep R {a} {b} f = ∀ x y → R a x y → R b (f x) (f y)

Respects₂ : ∀ {i j} {A B : Set} (f : A → B) (R : Rel A i) (S : Rel B j) → Set (i ⊔ j)
Respects₂ f R S = ∀ x y → R x y → S (f x) (f y)
