module Prelims.Red where
open import Relation.Binary

record Common-Reduct {i} {A : Set} (R S : Rel A i) (x y : A) : Set i where
  constructor cr
  field
    reduct : A
    left   : R x reduct
    right  : S y reduct

cr-sym : ∀ {i A R S x y} → Common-Reduct {i} {A} R S x y → Common-Reduct S R y x
cr-sym (cr z xRz ySz) = cr z ySz xRz

Diamond : ∀ {i} {A} → Rel A i → Rel A i → Set i
Diamond R S = ∀ x y z → R x y → S x z → Common-Reduct S R y z

diamond-sym : ∀ {i A} {R S : Rel A i} → Diamond R S → Diamond S R
diamond-sym diamond x y z xSy xRz = cr-sym (diamond x z y xRz xSy)

