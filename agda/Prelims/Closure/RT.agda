module Prelims.Closure.RT where
open import Relation.Binary
open import Relation.Binary.PropositionalEquality hiding (trans)
import Relation.Binary.PropositionalEquality.Core
open import Prelims.Closure.R
open import Prelims.Respect

data RTClose {i} {A : Set} (R : Rel A i) : Rel A i where
  inc : ∀ {x} {y} → R x y → RTClose R x y
  ref : ∀ {x} → RTClose R x x
  trans : ∀ {x} {y} {z} → RTClose R x y → RTClose R y z → RTClose R x z

RTCLOSE : ∀ {i A} → Rel A i → Preorder _ _ _
RTCLOSE {i} {A} R = record { 
  Carrier = A ; 
  _≈_ = _≡_ ; 
  _∼_ = RTClose R ; 
  isPreorder = record { 
    isEquivalence = Relation.Binary.PropositionalEquality.Core.isEquivalence ; 
    reflexive = λ { {x} .{x} refl → ref } ; 
    trans = trans } }

monoRT : ∀ {i A} {R S : Rel A i} {x y} → (∀ {x y} → R x y → S x y) → RTClose R x y → RTClose S x y
monoRT R⊆S (inc Rxy) = inc (R⊆S Rxy)
monoRT R⊆S ref = ref
monoRT R⊆S (trans RTxy RTyz) = trans (monoRT R⊆S RTxy) (monoRT R⊆S RTyz)

sub-R-RT : ∀ {i} {A} {R : Rel A i} {x} {y} → RClose {A = A} R x y → RTClose R x y
sub-R-RT (inc xRy) = inc xRy
sub-R-RT ref = ref

respects-RT : ∀ {i} {A : Set} {B : A → Set} (R : ∀ a → Rel (B a) i) {a b : A}
  (f : B a → B b) → Respects₂ f (R a) (R b) → Respects₂ f (RTClose (R a)) (RTClose (R b))
respects-RT _ _ hyp x y (inc x⇒y) = inc (hyp x y x⇒y)
respects-RT _ _ _ _ _ ref = ref
respects-RT R f hyp x z (trans x↠y y↠z) = trans (respects-RT R f hyp x _ x↠y) (respects-RT R f hyp _ z y↠z)

respects-RT₂ : ∀ {i j A B} {R : Rel A i} {S : Rel B j} {f : A → B} →
  Respects₂ f R S → Respects₂ f (RTClose R) (RTClose S)
respects-RT₂ hyp x y (inc x⇒y) = inc (hyp x y x⇒y)
respects-RT₂ _ _ _ ref = ref
respects-RT₂ hyp x z (trans x↠y y↠z) = trans (respects-RT₂ hyp x _ x↠y) (respects-RT₂ hyp _ z y↠z)

