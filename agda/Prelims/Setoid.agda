module Prelims.Setoid where
open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open import Function.Equality hiding (setoid;cong)
open import Data.Product

build-func : ∀ {A B : Set} → (A → B) → (setoid A ⟶ setoid B)
build-func f = record { 
  _⟨$⟩_ = f; 
  cong = cong _ }

prodf : ∀ {A B C D : Set} → (C → D) → (setoid A ⇨ setoid B) ⟶ (setoid (A × C) ⇨ setoid (B × D))
prodf f = record { 
  _⟨$⟩_ = λ g → build-func (λ {(a , c) → g ⟨$⟩ a , f c}) ;
  cong = λ g≡g' p≡p' → cong₂ _,_ (g≡g' (cong proj₁ p≡p')) (cong f (cong proj₂ p≡p')) }
