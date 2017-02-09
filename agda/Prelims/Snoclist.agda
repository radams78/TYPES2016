module Prelims.Snoclist where
open import Level
open import Relation.Binary.PropositionalEquality
open import Relation.Binary
open import Function.Equality hiding (cong)
open import Algebra
open import Data.Nat
open import Data.Fin

infixl 20 _snoc_
data snocList (A : Set) : Set where
  [] : snocList A
  _snoc_ : snocList A → A → snocList A

snocmap : ∀ {A B} → (A → B) → snocList A → snocList B
snocmap f [] = []
snocmap f (aa snoc a) = snocmap f aa snoc f a

snocmap-comp : ∀ {A B C} {g : B → C} {f : A → B} (l : snocList A) →
  snocmap (λ x → g (f x)) l ≡ snocmap g (snocmap f l)
snocmap-comp [] = refl
snocmap-comp {g = g} {f = f} (l snoc a) = cong (λ x → x snoc g (f a)) (snocmap-comp l)

replicate : ∀ {A} → ℕ → A → snocList A
replicate zero _ = []
replicate (suc n) a = replicate n a snoc a