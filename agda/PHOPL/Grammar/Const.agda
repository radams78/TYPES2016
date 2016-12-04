module PHOPL.Grammar.Const where
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

Pi : ∀ {n} → snocVec Type n → Type → Type
Pi [] B = B
Pi (AA snoc A) B = Pi AA (A ⇛ B)

--APPF : ∀ {F V} → Term V → FoldFunc.F F (Term V) → Term V
--APPF {F} {V} = FoldFunc.foldl₀ F appT

--APPF-rep : ∀ {F U V} (M : Term U) (NN : FoldFunc.F F (Term U)) (ρ : Rep U V) →
--  (APPF {F} M NN) 〈 ρ 〉 ≡ APPF {F} (M 〈 ρ 〉) (FoldFunc.map F (λ N → N 〈 ρ 〉) NN)
--TODO

APP' : ∀ {V} → Term V → List (Term V) → Term V
APP' M [] = M
APP' M (N ∷ NN) = APP' (appT M N) NN

APP'-rep : ∀ {U V} (M : Term U) (NN : List (Term U)) (ρ : Rep U V) → (APP' M NN) 〈 ρ 〉 ≡ APP' (M 〈 ρ 〉) (Data.List.map (λ x → x 〈 ρ 〉) NN)
APP'-rep M [] ρ = refl
APP'-rep M (N ∷ NN) ρ = APP'-rep (appT M N) NN ρ

APPl : ∀ {V} → Term V → snocList (Term V) → Term V
APPl M [] = M
APPl M (NN snoc N) = appT (APPl M NN) N

APPl-rep : ∀ {U V} {M : Term U} {NN : snocList (Term U)} {ρ : Rep U V} → (APPl M NN) 〈 ρ 〉 ≡ APPl (M 〈 ρ 〉) (snocmap (λ x → x 〈 ρ 〉) NN)
APPl-rep {NN = []} = refl
APPl-rep {NN = NN snoc N} {ρ} = cong (λ x → appT x (N 〈 ρ 〉)) (APPl-rep {NN = NN} {ρ})

APP : ∀ {V n} → Term V → snocVec (Term V) n → Term V
APP M [] = M
APP M (NN snoc N) = appT (APP M NN) N

APP-rep : ∀ {U V n M} (NN : snocVec (Term U) n) {ρ : Rep U V} →
  (APP M NN) 〈 ρ 〉 ≡ APP (M 〈 ρ 〉) (snocVec-rep NN ρ)
APP-rep [] = refl
APP-rep (NN snoc N) {ρ} = cong (λ x → appT x (N 〈 ρ 〉)) (APP-rep NN)

APPP : ∀ {V} {n} → Proof V → snocVec (Proof V) n → Proof V
APPP δ [] = δ
APPP δ (εε snoc ε) = appP (APPP δ εε) ε

APPP-rep : ∀ {U V n δ} (εε : snocVec (Proof U) n) {ρ : Rep U V} →
  (APPP δ εε) 〈 ρ 〉 ≡ APPP (δ 〈 ρ 〉) (snocVec-rep εε ρ)
APPP-rep [] = refl
APPP-rep (εε snoc ε) {ρ} = cong (λ x → appP x (ε 〈 ρ 〉)) (APPP-rep εε)

APPP' : ∀ {V} → Proof V → List (Proof V) → Proof V
APPP' δ [] = δ
APPP' δ (ε ∷ εε) = APPP' (appP δ ε) εε

APP* : ∀ {V n} → snocVec (Term V) n → snocVec (Term V) n → Path V → snocVec (Path V) n → Path V
APP* [] [] P [] = P
APP* (MM snoc M) (NN snoc N) P (QQ snoc Q) = app* M N (APP* MM NN P QQ) Q

APP*-rep : ∀ {U V n} MM {NN : snocVec (Term U) n} {P QQ} {ρ : Rep U V} →
  (APP* MM NN P QQ) 〈 ρ 〉 ≡ APP* (snocVec-rep MM ρ) (snocVec-rep NN ρ) (P 〈 ρ 〉) (snocVec-rep QQ ρ)
APP*-rep [] {[]} {QQ = []} = refl
APP*-rep (MM snoc M) {NN snoc N} {QQ = QQ snoc Q} {ρ = ρ} = 
  cong (λ x → app* (M 〈 ρ 〉) (N 〈 ρ 〉) x (Q 〈 ρ 〉)) (APP*-rep MM)
