module Prelims.Functor.Snoclist where
open import Level
open import Relation.Binary.PropositionalEquality
open import Relation.Binary
open import Function.Equality hiding (cong)
open import Algebra
open import Data.Nat
open import Data.Fin hiding (lift)
open import Prelims.Endo
open import Prelims.Functor.Foldable

infixl 20 _snoc_
data snocList (A : Set) : Set where
  [] : snocList A
  _snoc_ : snocList A → A → snocList A

snocmap : ∀ {A B} → (A → B) → snocList A → snocList B
snocmap f [] = []
snocmap f (aa snoc a) = snocmap f aa snoc f a

snocmapcong : ∀ {A B} {f g : A → B} {l : snocList A} →
  (∀ x → f x ≡ g x) → snocmap f l ≡ snocmap g l
snocmapcong {l = []} f≡g = refl
snocmapcong {l = l snoc x} f≡g = cong₂ _snoc_ (snocmapcong f≡g) (f≡g x)

snocmap-id : ∀ {A} {l : snocList A} →
  snocmap (λ x → x) l ≡ l
snocmap-id {l = []} = refl
snocmap-id {l = l snoc a} = cong₂ _snoc_ (snocmap-id {l = l}) refl

snocmap-comp : ∀ {A B C} {g : B → C} {f : A → B} {l : snocList A} →
  snocmap (λ x → g (f x)) l ≡ snocmap g (snocmap f l)
snocmap-comp {l = []} = refl
snocmap-comp {g = g} {f = f} {l = l snoc a} = cong (λ x → x snoc g (f a)) snocmap-comp

snocfoldl : ∀ {A} {B : Set₁} → (B → A → B) → B → snocList A → B
snocfoldl f b [] = b
snocfoldl f b (aa snoc a) = f (snocfoldl f b aa) a

snocfoldl-cong : ∀ {A B} {f g : B → A → B} {b : B} (aa : snocList A) →
  (∀ x y → f x y ≡ g x y) → snocfoldl f b aa ≡ snocfoldl g b aa
snocfoldl-cong [] _ = refl
snocfoldl-cong {f = f} {g} {b} (aa snoc a) f≡g = let open ≡-Reasoning in begin
    f (snocfoldl f b aa) a
  ≡⟨ f≡g _ _ ⟩
    g (snocfoldl f b aa) a
  ≡⟨ cong (λ x → g x a) (snocfoldl-cong aa f≡g) ⟩
    g (snocfoldl g b aa) a
  ∎

snocfoldl-nat : {A : Set} {B C : Set₁} {f : B → A → B} {g : C → A → C} (h : B → C)
  {b : B} {aa : snocList A} →
  ((b₁ : B) (a : A) → h (f b₁ a) ≡ g (h b₁) a) →
  h (snocfoldl f b aa) ≡ snocfoldl g (h b) aa
snocfoldl-nat _ {aa = []} _ = refl
snocfoldl-nat {f = f} {g} h {b} {aa = aa snoc a} hyp = let open ≡-Reasoning in 
  begin
    h (f (snocfoldl f b aa) a)
  ≡⟨ hyp (snocfoldl f b aa) a ⟩
    g (h (snocfoldl f b aa)) a
  ≡⟨ cong (λ x → g x a) (snocfoldl-nat h {aa = aa} hyp) ⟩
    g (snocfoldl g (h b) aa) a
  ∎

snocdepfoldl : {A : Set} {B : Set₁} {f : B → A → B} {b : B} {aa : snocList A}
  {C : B → Set} →
  ((x : B) (y : A) → C x → C (f x y)) → C b → C (snocfoldl f b aa)
snocdepfoldl {aa = []} _ j₀ = j₀
snocdepfoldl {aa = aa snoc a} f j₀ = f _ a (snocdepfoldl {aa = aa} f j₀)

snocdepfoldl₂ : {A : Set} {B : Set₁} {f g : B → A → B} {b₁ b₂ : B}
  {aa : snocList A} {C : B → B → Set₁} →
  ((x y : B) (z : A) → C x y → C (f x z) (g y z)) →
  C b₁ b₂ → C (snocfoldl f b₁ aa) (snocfoldl g b₂ aa)
snocdepfoldl₂ {aa = []} _ c = c
snocdepfoldl₂ {aa = aa snoc a} f c = f _ _ a (snocdepfoldl₂ {aa = aa} f c)

snocdepfoldl₂-resp : ∀ {A : Set} {B : Set₁} {f g : B → A → B} {b₁ b₂ : B}
      {aa : snocList A} {C : B → B → Set₁}
      {h : (x y : B) (z : A) → C x y → C (f x z) (g y z)}
      {c c' : C b₁ b₂} {R : {x y : B} → C x y → C x y → Set} →
      ((x y : B) (z : A) (a b : C x y) →
       R a b → R (h x y z a) (h x y z b)) →
      R c c' → R (snocdepfoldl₂ {aa = aa} h c) (snocdepfoldl₂ {aa = aa} h c')
snocdepfoldl₂-resp {aa = []} _ Rcc' = Rcc'
snocdepfoldl₂-resp {aa = aa snoc a} {h = h} {c} {c'} hyp Rcc' = hyp (snocfoldl _ _ aa) (snocfoldl _ _ aa) a (snocdepfoldl₂ {aa = aa} h c) (snocdepfoldl₂ {aa = aa} h c') (snocdepfoldl₂-resp {aa = aa} hyp Rcc')

SNOCLIST : FoldFunc
SNOCLIST = record { 
  functor = record {
    F = snocList ; 
    map = snocmap ;
    map-cong = snocmapcong ;
    map-id = snocmap-id ;
    map-comp = snocmap-comp } ;
  isFoldable = record {
    foldl = snocfoldl ;
    foldl-cong = snocfoldl-cong ;
    foldl-nat = snocfoldl-nat ;
    depfoldl = λ {_} {_} {_} {_} {aa} → snocdepfoldl {aa = aa} ;
    depfoldl₂ = λ {_} {_} {_} {_} {_} {_} {aa} → snocdepfoldl₂ {aa = aa} ;
    depfoldl₂-resp = λ {_} {_} {_} {_} {_} {_} {aa} → snocdepfoldl₂-resp {aa = aa}
  } }

replicate : ∀ {A} → ℕ → A → snocList A
replicate zero _ = []
replicate (suc n) a = replicate n a snoc a

data snocVec (A : Set) : ℕ → Set where
  [] : snocVec A ℕ.zero
  _snoc_ : ∀ {n} → snocVec A n → A → snocVec A (ℕ.suc n)

lookup : ∀ {A : Set} {n} → Fin n → snocVec A n → A
lookup zero (_ snoc x) = x
lookup (suc i) (v snoc _) = lookup i v
