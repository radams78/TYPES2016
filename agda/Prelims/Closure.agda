module Prelims.Closure where
open import Relation.Binary.PropositionalEquality hiding (sym;trans)
import Relation.Binary.PropositionalEquality.Core
open import Relation.Binary
open import Data.Product renaming (_,_ to _,p_)

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

data RClose {i} {A : Set} (R : Rel A i) : Rel A i where
  inc : ∀ {x} {y} → R x y → RClose R x y
  ref : ∀ {x} → RClose R x x

data TClose {i} {A : Set} (R : Rel A i) : Rel A i where
  inc : ∀ {x} {y} → R x y → TClose R x y
  trans : ∀ {x} {y} {z} → TClose R x y → TClose R y z → TClose R x z

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

sub-T-RT : ∀ {i} {A} {R : Rel A i} {x} {y} → TClose {A = A} R x y → RTClose R x y
sub-T-RT (inc xRy) = inc xRy
sub-T-RT (trans xRy yRz) = trans (sub-T-RT xRy) (sub-T-RT yRz)

diamondRT : ∀ {i A} {R S : Rel A i} →
  Diamond R S → Diamond R (RTClose S)
diamondRT diamond x y z xRy (inc xSz) =
  let cr w ySw zRw = diamond x y z xRy xSz in 
  cr w (inc ySw) zRw
diamondRT diamond x y .x xRy ref = cr y ref xRy
diamondRT diamond x y z' xRy (trans xRTz zRTz') = 
  let cr w yRTw zRw = diamondRT diamond x y _ xRy xRTz in 
  let cr w' wRTw' z'Rw' = diamondRT diamond _ w z' zRw zRTz' in 
  cr w' (trans yRTw wRTw') z'Rw'

diamondRTRT : ∀ {i A} {R S : Rel A i} → Diamond R S → Diamond (RTClose R) (RTClose S)
diamondRTRT diamond = diamondRT (diamond-sym (diamondRT (diamond-sym diamond)))

data RSTClose {i} {A : Set} (R : Rel A i) : Rel A i where
  inc : ∀ {x y} → R x y → RSTClose R x y
  ref : ∀ {x} → RSTClose R x x
  sym : ∀ {x y} → RSTClose R x y → RSTClose R y x
  trans : ∀ {x y z} → RSTClose R x y → RSTClose R y z → RSTClose R x z

RSTCLOSE : ∀ {i A} → Rel A i → Setoid _ _
RSTCLOSE {i} {A} R = record { 
  Carrier = A ; 
  _≈_ = RSTClose R ; 
  isEquivalence = record { 
    refl = ref ; 
    sym = sym ; 
    trans = trans } }

sub-RT-RST : ∀ {i A} {R : Rel A i} {x y} → RTClose {A = A} R x y → RSTClose R x y
sub-RT-RST (inc xRy) = inc xRy
sub-RT-RST ref = ref
sub-RT-RST (trans xRTy yRTz) = trans (sub-RT-RST xRTy) (sub-RT-RST yRTz)

Church-Rosser : ∀ {i A} → Rel A i → Set i
Church-Rosser R = ∀ x y → RSTClose R x y → Common-Reduct (RTClose R) (RTClose R) x y

diamondRT-CR : ∀ {i A} {R : Rel A i} →
  Diamond (RTClose R) (RTClose R) → Church-Rosser R
diamondRT-CR diamond x y (inc xRy) = cr y (inc xRy) ref
diamondRT-CR diamond x .x ref = cr x ref ref
diamondRT-CR diamond y x (sym x≃y) = cr-sym (diamondRT-CR diamond x y x≃y)
diamondRT-CR diamond x z (trans x≃y y≃z) = 
  let cr a x↠a y↠a = diamondRT-CR diamond x _ x≃y in 
  let cr b y↠b z↠b = diamondRT-CR diamond _ z y≃z in 
  let cr c a↠c b↠c = diamond _ a b y↠a y↠b in 
  cr c (trans x↠a a↠c) (trans z↠b b↠c)

diamond-CR : ∀ {i A} {R : Rel A i} → Diamond R R → Church-Rosser R
diamond-CR diamond = diamondRT-CR (diamondRTRT diamond)
