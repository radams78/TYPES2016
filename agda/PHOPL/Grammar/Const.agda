module PHOPL.Grammar.Const where
open import Data.Empty renaming (⊥ to Empty)
open import Data.List
open import Prelims
open import PHOPL.Grammar.Base
open PHOPLgrammar public
open import Grammar PHOPL public

Proof : Alphabet → Set
Proof V = Expression V -vProof

Term : Alphabet → Set
Term V = Expression V -vTerm

Path : Alphabet → Set
Path V = Expression V -vPath

Equation : Alphabet → Set
Equation V = Expression V -nvEq

ty : ∀ {V} → Type → Expression V (nonVarKind -Type)
ty A = app (-ty A) []

⊥ : ∀ {V} → Term V
⊥ = app -bot []

infix 65 _⊃_
_⊃_ : ∀ {V} → Term V → Term V → Term V
φ ⊃ ψ = app -imp (φ ∷ ψ ∷ [])

data Is-⊃ {V} : Term V → Set where
  is-⊃ : ∀ {φ} {ψ} → Is-⊃ (φ ⊃ ψ)

ΛT : ∀ {V} → Type → Term (V , -Term) → Term V
ΛT A M = app (-lamTerm A) (M ∷ [])

appT : ∀ {V} → Term V → Term V → Term V
appT M N = app -appTerm (M ∷ N ∷ [])

ΛP : ∀ {V} → Term V → Proof (V , -Proof) → Proof V
ΛP φ δ = app -lamProof (φ ∷ δ ∷ [])

appP : ∀ {V} → Proof V → Proof V → Proof V
appP δ ε = app -appProof (δ ∷ ε ∷ [])

dir : ∀ {V} → Dir → Path V → Proof V
dir d P = app (-dir d) (P ∷ [])

plus : ∀ {V} → Path V → Proof V
plus P = dir -plus P

minus : ∀ {V} → Path V → Proof V
minus P = dir -minus P

reff : ∀ {V} → Term V → Path V
reff M = app -ref (M ∷ [])

infix 15 _⊃*_
_⊃*_ : ∀ {V} → Path V → Path V → Path V
P ⊃* Q = app -imp* (P ∷ Q ∷ [])

univ : ∀ {V} → Term V → Term V → Proof V → Proof V → Path V
univ φ ψ P Q = app -univ (φ ∷ ψ ∷ P ∷ Q ∷ [])

λλλ : ∀ {V} → Type → Path (V , -Term , -Term , -Path) → Path V
λλλ A P = app (-lll A) (P ∷ [])

app* : ∀ {V} → Term V → Term V → Path V → Path V → Path V
app* M N P Q = app -app* (M ∷ N ∷ P ∷ Q ∷ [])

infix 60 _≡〈_〉_
_≡〈_〉_ : ∀ {V} → Term V → Type → Term V → Equation V
M ≡〈 A 〉 N = app (-eq A) (M ∷ N ∷ [])

infixl 59 _,T_
_,T_ : ∀ {V} → Context V → Type → Context (V , -Term)
Γ ,T A = Γ , ty A

infixl 59 _,P_
_,P_ : ∀ {V} → Context V → Term V → Context (V , -Proof)
_,P_ = _,_

infixl 59 _,E_
_,E_ : ∀ {V} → Context V → Equation V → Context (V , -Path)
_,E_ = _,_

yt : ∀ {V} → Expression V (nonVarKind -Type) → Type
yt (app (-ty A) []) = A

typeof' : ∀ {V} → Var V -Term → Context V → Type
typeof' x Γ  = yt (typeof x Γ)

⊃-injl : ∀ {V} {φ φ' ψ ψ' : Term V} → φ ⊃ ψ ≡ φ' ⊃ ψ' → φ ≡ φ'
⊃-injl refl = refl

⊃-injr : ∀ {V} {φ φ' ψ ψ' : Term V} → φ ⊃ ψ ≡ φ' ⊃ ψ' → ψ ≡ ψ'
⊃-injr refl = refl

appT-injl : ∀ {V} {M M' N N' : Term V} → appT M N ≡ appT M' N' → M ≡ M'
appT-injl refl = refl

appT-injr : ∀ {V} {M N P Q : Term V} → appT M N ≡ appT P Q → N ≡ Q
appT-injr refl = refl

appP-injl : ∀ {V} {δ δ' ε ε' : Proof V} → appP δ ε ≡ appP δ' ε' → δ ≡ δ'
appP-injl refl = refl

app*-injl : ∀ {V} {M M' N N' : Term V} {P P' Q Q' : Path V} → app* M N P Q ≡ app* M' N' P' Q' → P ≡ P'
app*-injl refl = refl

eq-inj₁ : ∀ {V A A'} {M M' N N' : Term V} → M ≡〈 A 〉 N ≡ M' ≡〈 A' 〉 N' → M ≡ M'
eq-inj₁ refl = refl

dir-inj : ∀ {V} {P Q : Path V} {d} → dir d P ≡ dir d Q → P ≡ Q
dir-inj refl = refl

univ-injl : ∀ {V} {φ φ' ψ ψ' : Term V} {δ δ' ε ε' : Proof V} →
  univ φ ψ δ ε ≡ univ φ' ψ' δ' ε' → δ ≡ δ'
univ-injl refl = refl

⊃*-injl : ∀ {V} {P P' Q Q' : Path V} → P ⊃* Q ≡ P' ⊃* Q' → P ≡ P'
⊃*-injl refl = refl

⊃*-injr : ∀ {V} {P P' Q Q' : Path V} → P ⊃* Q ≡ P' ⊃* Q' → Q ≡ Q'
⊃*-injr refl = refl

APPl : ∀ {V} → Term V → snocList (Term V) → Term V
APPl M [] = M
APPl M (NN snoc N) = appT (APPl M NN) N

APPl-rep : ∀ {U V} {M : Term U} {NN : snocList (Term U)} {ρ : Rep U V} → (APPl M NN) 〈 ρ 〉 ≡ APPl (M 〈 ρ 〉) (snocmap (λ x → x 〈 ρ 〉) NN)
APPl-rep {NN = []} = refl
APPl-rep {NN = NN snoc N} {ρ} = cong (λ x → appT x (N 〈 ρ 〉)) (APPl-rep {NN = NN} {ρ})

type : ∀ {V} → Equation V → Type
type (app (-eq A) _) = A

type-rep : ∀ {U V} (E : Equation U) {ρ : Rep U V} → type (E 〈 ρ 〉) ≡ type E
type-rep (app (-eq _) _) = refl

left : ∀ {V} → Equation V → Term V
left (app (-eq _) (M ∷ _ ∷ [])) = M

left-rep : ∀ {U V} (E : Equation U) {ρ : Rep U V} → left E 〈 ρ 〉 ≡ left (E 〈 ρ 〉)
left-rep (app (-eq _) (_ ∷ _ ∷ [])) = refl

-- Mx1...xn =/= Λ M' for n >= 1
APPl-not-Λ : ∀ {V M N} {NN : snocList (Term V)} {A M'} → APPl (appT M N) NN ≡ ΛT A M' → Empty
APPl-not-Λ {NN = []} ()
APPl-not-Λ {NN = _ snoc _} ()

-- If Mx1...xn = (Λ M') N with n >= 1 then M = Λ M'
APPl-Λ : ∀ {V M N} {NN : snocList (Term V)} {A M' N'} →
  APPl (appT M N) NN ≡ appT (ΛT A M') N' → M ≡ ΛT A M'
APPl-Λ {NN = []} Mx≡ΛM'N = appT-injl Mx≡ΛM'N
APPl-Λ {NN = NN snoc _} Mx≡ΛM'N = ⊥-elim (APPl-not-Λ {NN = NN} (appT-injl Mx≡ΛM'N))

APPP : ∀ {V} → Proof V → snocList (Proof V) → Proof V
APPP δ [] = δ
APPP δ (εε snoc ε) = appP (APPP δ εε) ε

APPP-rep : ∀ {U V} {δ : Proof U} {εε : snocList (Proof U)} {ρ : Rep U V} →
  APPP δ εε 〈 ρ 〉 ≡ APPP (δ 〈 ρ 〉) (snocmap (λ ε → ε 〈 ρ 〉) εε)
APPP-rep {εε = []} = refl
APPP-rep {εε = εε snoc ε} {ρ} = cong (λ x → appP x (ε 〈 ρ 〉)) (APPP-rep {εε = εε})
