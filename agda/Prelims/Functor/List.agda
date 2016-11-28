module Prelims.Functor.List where
open import Level
open import Function
open import Function.Equality using (_⟶_) renaming (_∘_ to _○_)
open import Data.List hiding (foldl)
open import Prelims.EqReasoning
open import Prelims.Functor.Foldable

map-cong : ∀ {A B : Set} {f g : A → B} {aa : List A} →
         (∀ x → f x ≡ g x) → Data.List.map f aa ≡ Data.List.map g aa
map-cong {aa = []} _ = refl
map-cong {aa = a ∷ aa} f≡g = cong₂ _∷_ (f≡g a) (map-cong f≡g)

map-id : ∀ {A : Set} {aa : List A} → Data.List.map (λ x → x) aa ≡ aa
map-id {aa = []} = refl
map-id {aa = a ∷ aa} = cong (λ l → a ∷ l) map-id

map-comp : ∀ {A B C : Set} {g : B → C} {f : A → B} {aa : List A} →
  Data.List.map (g ∘ f) aa ≡ Data.List.map g (Data.List.map f aa)
map-comp {aa = []} = refl
map-comp {g = g} {f} {a ∷ aa} = cong (λ x → g (f a) ∷ x) map-comp

foldl : ∀ {A : Set} {B : Set₁} → (B → A → B) → B → List A → B
foldl f b [] = b
foldl f b (a ∷ aa) = foldl f (f b a) aa

foldl-cong : ∀ {A B} {f g : B → A → B} {b : B} (aa : List A) →
  (∀ x y → f x y ≡ g x y) → foldl f b aa ≡ foldl g b aa
foldl-cong [] f≡g = refl
foldl-cong {f = f} {g} {b} (a ∷ aa) f≡g = let open ≡-Reasoning in 
  begin
    foldl f (f b a) aa
  ≡⟨ foldl-cong aa f≡g ⟩
    foldl g (f b a) aa
  ≡⟨ cong (λ x → foldl g x aa) (f≡g b a) ⟩
    foldl g (g b a) aa
  ∎

foldl-nat :  ∀ {A B C} {f : B → A → B} {g : C → A → C} (h : B → C) {b} {aa} →
      (∀ b a → h (f b a) ≡ g (h b) a) →
      h (foldl f b aa) ≡ foldl g (h b) aa
foldl-nat _ {aa = []} _ = refl
foldl-nat {f = f} {g} h {b} {aa = a ∷ aa} hyp = let open ≡-Reasoning in 
  begin
    h (foldl f (f b a) aa)
  ≡⟨ foldl-nat h {aa = aa} hyp ⟩
    foldl g (h (f b a)) aa
  ≡⟨ cong (λ x → foldl g x aa) (hyp b a) ⟩
    foldl g (g (h b) a) aa
  ∎

depfoldl : ∀ {A : Set} {B : Set₁} {f : B → A → B} {b : B} {aa : List A}
      {C : B → Set} →
      ((x : B) (y : A) → C x → C (f x y)) → C b → C (foldl f b aa)
depfoldl {aa = []} _ c = c
depfoldl {aa = a ∷ aa} g c = depfoldl {aa = aa} g (g _ a c)

depfoldl₂ : {A : Set} {B : Set₁} {f g : B → A → B} {b₁ b₂ : B}
      {aa : List A} {C : B → B → Set₁} →
      ((x y : B) (z : A) → C x y → C (f x z) (g y z)) →
      C b₁ b₂ → C (foldl f b₁ aa) (foldl g b₂ aa)
depfoldl₂ {aa = []} h c = c
depfoldl₂ {aa = a ∷ aa} h c = depfoldl₂ {aa = aa} h (h _ _ a c)

depfold₂-resp : ∀ {A : Set} {B : Set₁} {f g : B → A → B} {b₁ b₂ : B} {aa : List A}
  {C : B → B → Set₁}
  {h : (x y : B) (z : A) → C x y → C (f x z) (g y z)}
  {c c' : C b₁ b₂} {R : {x y : B} → C x y → C x y → Set} →
  (∀ x y z (a b : C x y) → R a b → R (h x y z a) (h x y z b)) →
  R c c' → R (depfoldl₂ {aa = aa} h c) (depfoldl₂ {aa = aa} h c')
depfold₂-resp {aa = []} _ Rcc' = Rcc'
depfold₂-resp {aa = a ∷ aa} hyp Rcc' = depfold₂-resp {aa = aa} hyp (hyp _ _ a _ _ Rcc')

LIST : FoldFunc
LIST = record
  { functor = record
    { F = List
    ; map = Data.List.map
    ; map-cong = map-cong
    ; map-id = map-id
    ; map-comp = map-comp
    } 
  ; isFoldable = record 
    { foldl = foldl
    ; foldl-cong = foldl-cong
    ; foldl-nat = foldl-nat
    ; depfoldl = λ {_} {_} {_} {_} {aa} → depfoldl {aa = aa}
    ; depfoldl₂ = λ {_} {_} {_} {_} {_} {_} {aa} → depfoldl₂ {aa = aa}
    ; depfoldl₂-resp = λ {_} {_} {_} {_} {_} {_} {aa} → depfold₂-resp {aa = aa}
    }
  }
