module Prelims.Red where
open import Relation.Binary
open import Prelims.Closure
open import Prelims.Closure.RST

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

Almost-Diamond : ∀ {i A} → Rel A i → Set i
Almost-Diamond R = ∀ x y z → R x y → R x z → Common-Reduct (RClose R) (RClose R) y z

diamond-R-RT : ∀ {i A} {R : Rel A i} → Almost-Diamond R → Diamond (RClose R) (RTClose R)
diamond-R-RT hyp x y z (inc x⇒y) (inc x⇒z) = let cr w y⇒?w z⇒?w = hyp x y z x⇒y x⇒z in 
  cr w (sub-R-RT y⇒?w) z⇒?w
diamond-R-RT hyp x .x z ref (inc x⇒z) = cr z (inc x⇒z) ref
diamond-R-RT hyp x y .x x⇒?y ref = cr y ref x⇒?y
diamond-R-RT hyp x y z' x⇒?y (trans x↠z z↠z') =
  let cr a y↠a z⇒?a = diamond-R-RT hyp x y _ x⇒?y x↠z in 
  let cr b a↠b z'⇒?b = diamond-R-RT hyp _ a z' z⇒?a z↠z' in 
  cr b (trans y↠a a↠b) z'⇒?b

diamond-RT-RT : ∀ {i A} {R : Rel A i} → Almost-Diamond R → Diamond (RTClose R) (RTClose R)
diamond-RT-RT hyp x y z (inc x⇒y) x↠z = 
  let cr a y↠a z⇒?a = diamond-R-RT hyp x y z (inc x⇒y) x↠z in 
  cr a y↠a (sub-R-RT z⇒?a)
diamond-RT-RT hyp x .x z ref x↠z = cr z x↠z ref
diamond-RT-RT hyp x y' z (trans x↠y y↠y') x↠z = 
  let cr a y↠a z↠a = diamond-RT-RT hyp x _ z x↠y x↠z in 
  let cr b y'↠b a↠b = diamond-RT-RT hyp _ y' a y↠y' y↠a in 
  cr b y'↠b (trans z↠a a↠b)

diamond-CR :  ∀ {i A} {R : Rel A i} → Almost-Diamond R → Church-Rosser R
diamond-CR hyp = diamondRT-CR (diamond-RT-RT hyp)
