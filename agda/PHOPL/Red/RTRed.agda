module PHOPL.Red.RTRed where
open import Data.Product renaming (_,_ to _,p_)
open import Data.Sum
open import Prelims
open import PHOPL.Grammar
open import PHOPL.Red.Base
open import PHOPL.Red.RRed

_↠_ : ∀ {V K} → Expression V K → Expression V K → Set
_↠_ {V} {K} = RTClose (_⇒_ {V} {K})

↠-resp-rep : ∀ {U V K} {E F : Expression U K} {ρ : Rep U V} → E ↠ F → E 〈 ρ 〉 ↠ F 〈 ρ 〉
↠-resp-rep (inc E⇒F) = inc (⇒-resp-rep E⇒F)
↠-resp-rep ref = ref
↠-resp-rep (trans E↠F F↠G) = trans (↠-resp-rep E↠F) (↠-resp-rep F↠G)

data Reduces-to-Λ {V} (M : Term V) : Set where
  reduces-to-Λ : ∀ {A N} → M ↠ ΛT A N → Reduces-to-Λ M

-- If Mx1...xn ->> N with n >= 1 then either N = M'x1...xn where M ->> M', or M reduces to a lambda-term
APPl-red : ∀ {V M N M' N'} (NN : snocList (Term V)) →
  M ↠ N → M ≡ APPl (appT M' N') NN → Σ[ M'' ∈ Term V ] M' ↠ M'' × N ≡ APPl (appT M'' N') NN ⊎ Reduces-to-Λ M'
APPl-red NN (inc M⇒N) M≡M'NN with APPl-⇒ NN M⇒N M≡M'NN
APPl-red _ (inc M⇒N) M≡M'NN | inj₁ (M'' ,p M'⇒M'' ,p N≡M''NN) = inj₁ (M'' ,p inc M'⇒M'' ,p N≡M''NN)
APPl-red {M' = M'} _ (inc M⇒N) M≡M'NN | inj₂ (A ,p M'' ,p M'≡ΛM'') = inj₂ (reduces-to-Λ {A = A} {N = M''} (subst (λ x → M' ↠ x) M'≡ΛM'' ref))
APPl-red _ ref M≡M'NN = inj₁ (_ ,p ref ,p M≡M'NN)
APPl-red NN (trans M↠N N↠P) M≡M'NN with APPl-red NN M↠N M≡M'NN
APPl-red NN (trans M↠N N↠P) M≡M'NN | inj₁ (N' ,p M'↠N' ,p N≡N'NN) with APPl-red NN N↠P N≡N'NN
APPl-red NN (trans M↠N N↠P) M≡M'NN | inj₁ (N' ,p M'↠N' ,p N≡N'NN) | inj₁ (P' ,p N'↠P' ,p P≡P'NN) = inj₁ (P' ,p trans M'↠N' N'↠P' ,p P≡P'NN)
APPl-red NN (trans M↠N N↠P) M≡M'NN | inj₁ (N' ,p M'↠N' ,p N≡N'NN) | inj₂ (reduces-to-Λ N'↠ΛN₀) = inj₂ (reduces-to-Λ (trans M'↠N' N'↠ΛN₀))
APPl-red NN (trans M↠N N↠P) M≡M'NN | inj₂ N'rtΛ = inj₂ N'rtΛ

private imp-red-inj₁' : ∀ {V} {φ ψ χ χ' : Term V} → χ ↠ χ' → χ ≡ φ ⊃ ψ → Σ[ φ' ∈ Term V ] Σ[ ψ' ∈ Term V ]
                      χ' ≡ φ' ⊃ ψ' × φ ↠ φ'
imp-red-inj₁' {χ' = χ'} (inc χ⇒χ') χ≡φ⊃ψ with imp-osr-inj₁ (subst (λ x → x ⇒ χ') χ≡φ⊃ψ χ⇒χ')
imp-red-inj₁' (inc χ⇒χ') χ≡φ⊃ψ | φ' ,p ψ' ,p χ'≡φ'⊃ψ' ,p φ⇒?φ' = φ' ,p ψ' ,p χ'≡φ'⊃ψ' ,p sub-R-RT φ⇒?φ'
imp-red-inj₁' {φ = φ} {ψ} ref χ≡φ⊃ψ = φ ,p ψ ,p χ≡φ⊃ψ ,p ref
imp-red-inj₁' (trans χ₁↠χ₂ χ₂↠χ₃) χ₁≡φ⊃ψ with imp-red-inj₁' χ₁↠χ₂ χ₁≡φ⊃ψ
imp-red-inj₁' (trans χ₁↠χ₂ χ₂↠χ₃) χ₁≡φ⊃ψ | φ' ,p ψ' ,p χ₂≡φ'⊃ψ' ,p φ↠φ' with imp-red-inj₁' χ₂↠χ₃ χ₂≡φ'⊃ψ'
imp-red-inj₁' (trans χ₁↠χ₂ χ₂↠χ₃) χ₁≡φ⊃ψ | φ' ,p ψ' ,p χ₂≡φ'⊃ψ' ,p φ↠φ' | φ'' ,p ψ'' ,p χ₃≡φ''⊃ψ'' ,p φ'↠φ'' = φ'' ,p ψ'' ,p χ₃≡φ''⊃ψ'' ,p trans φ↠φ' φ'↠φ''

imp-red-inj₁ : ∀ {V} {φ φ' ψ ψ' : Term V} → φ ⊃ ψ ↠ φ' ⊃ ψ' → φ ↠ φ'
imp-red-inj₁ φ⊃ψ↠φ'⊃ψ' with imp-red-inj₁' φ⊃ψ↠φ'⊃ψ' refl
imp-red-inj₁ {φ = φ} φ⊃ψ↠φ'⊃ψ' | φ'' ,p ψ'' ,p φ'⊃ψ'≡φ''⊃ψ'' ,p φ↠φ'' = subst (λ x → φ ↠ x) (⊃-injl (≡-sym φ'⊃ψ'≡φ''⊃ψ'')) φ↠φ''

