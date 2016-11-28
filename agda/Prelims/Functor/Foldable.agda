module Prelims.Functor.Foldable where
open import Level
open import Function hiding (id)
open import Function.Equality hiding (cong) renaming (_∘_ to _∘∘_)
open import Algebra
open import Prelims.EqReasoning
open import Prelims.Functor.Base
open import Prelims.Endo
open import Data.Product hiding (map)

record IsFoldable (FF : Functor) : Set₂ where
  open Functor FF
  field
    foldl : ∀ {A} {B : Set₁} → (B → A → B) → B → F A → B
    foldl-cong : ∀ {A B} {f g : B → A → B} {b} aa →
      (∀ x y → f x y ≡ g x y) → foldl f b aa ≡ foldl g b aa
    foldl-nat : ∀ {A B C} {f : B → A → B} {g : C → A → C} (h : B → C) {b} {aa} →
      (∀ b a → h (f b a) ≡ g (h b) a) →
      h (foldl f b aa) ≡ foldl g (h b) aa
    depfoldl : ∀ {A B} {f : B → A → B} {b : B} {aa : F A}
      {C : B → Set} →
      (∀ x y → C x → C (f x y)) → C b → C (foldl f b aa)
    depfoldl-nat : ∀ {A B} {f : B → A → B} {b : B} {aa : F A}
      {C D : B → Set} {h : ∀ b → C b → D b}
      {k : ∀ x y → C x → C (f x y)} {l : ∀ x y → D x → D (f x y)} {c : C b} →
      (∀ x y z → h (f x y) (k x y z) ≡ l x y (h x z)) →
      h (foldl f b aa) (depfoldl k c) ≡ depfoldl l (h b c)
    depfoldl₂ : ∀ {A B} {f g : B → A → B} {b₁ b₂ : B} {aa : F A}
      {C : B → B → Set₁} →
      (∀ x y z → C x y → C (f x z) (g y z)) → C b₁ b₂ → C (foldl f b₁ aa) (foldl g b₂ aa)
    depfoldl₂-resp : ∀ {A B} {f g : B → A → B} {b₁ b₂ : B} {aa : F A}
      {C : B → B → Set₁}
      {h : ∀ x y z → C x y → C (f x z) (g y z)} {c c' : C b₁ b₂}
      {R : ∀ {x y} → C x y → C x y → Set} →
      (∀ x y z (a b : C x y) → R a b → R (h x y z a) (h x y z b)) →   
      R c c' → R (depfoldl₂ {aa = aa} h c) (depfoldl₂ h c')

  foldl₀ : ∀ {A B : Set} → (B → A → B) → B → F A → B
  foldl₀ {A} {B} f b aa = lower (foldl (λ b' a → lift (f (lower b') a)) (lift b) aa)

  depfoldl₂₀ : ∀ {A B : Set} {f g : B → A → B} {b₁ b₂ : B} {aa : F A}
      {C : B → B → Set} →
      (∀ x y z → C x y → C (f x z) (g y z)) → C b₁ b₂ → 
      C (lower (foldl (λ x y → lift (f (lower x) y)) (lift b₁) aa)) 
        (lower (foldl (λ x y → lift (g (lower x) y)) (lift b₂) aa))
  depfoldl₂₀ {C = C} f c = lower (depfoldl₂ {C = λ x y → Lift (C (lower x) (lower y))} (λ x y z t → lift (f (lower x) (lower y) z (lower t))) (lift c))

  depfoldl₂₀-resp : ∀ {A B} {f g : B → A → B} {b₁ b₂ : B} {aa : F A}
      {C : B → B → Set}
      {h : ∀ x y z → C x y → C (f x z) (g y z)} {c c' : C b₁ b₂}
      {R : ∀ {x y} → C x y → C x y → Set} →
      (∀ x y z (a b : C x y) → R a b → R (h x y z a) (h x y z b)) →   
      R c c' → R (depfoldl₂₀ {aa = aa} h c) (depfoldl₂₀ h c')
  depfoldl₂₀-resp {R = R} hyp = depfoldl₂-resp {R = λ a b → R (lower a) (lower b)} (λ x y z a b → hyp (lower x) (lower y) z (lower a) (lower b))

  module FoldMonoid (MM : Monoid zero zero) where
    open Monoid MM renaming (Carrier to M;_∙_ to _•_)

    fold : F M → M
    fold = foldl₀ _•_ ε

    foldMap : ∀ {A} → (A → M) → F A → M
    foldMap f aa = fold (map f aa)

  open FoldMonoid public

  foldr : ∀ {A B : Set} → (A → B → B) → F A → B → B
  foldr {A} {B} = foldMap (EndoR B)

record FoldFunc : Set₂ where
  field
    functor : Functor
    isFoldable : IsFoldable functor
  open Functor functor public
  open IsFoldable isFoldable public
