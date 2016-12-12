module PHOML.Red.RTRed where
open import Data.Unit
open import Data.Bool
open import Data.Product renaming (_,_ to _,p_)
open import Data.Sum
open import Prelims
open import PHOML.Grammar
open import PHOML.PathSub
open import PHOML.Red.Base
open import PHOML.Red.RRed

infix 10 _↠_
_↠_ : ∀ {V K} → Expression V K → Expression V K → Set
_↠_ {V} {K} = RTClose (_⇒_ {V} {K})

↠-resp-rep : ∀ {U V K} {E F : Expression U K} {ρ : Rep U V} → E ↠ F → E 〈 ρ 〉 ↠ F 〈 ρ 〉
↠-resp-rep = respects-RT₂ (λ _ _ → ⇒-resp-rep) _ _

↠-resp-ps : ∀ {U V} {M N : Term U} {τ : PathSub U V} {ρ σ} → M ↠ N → M ⟦⟦ τ ∶ ρ ≡ σ ⟧⟧ ↠ N ⟦⟦ τ ∶ ρ ≡ σ ⟧⟧
↠-resp-ps = respects-RT₂ (λ _ _ → ⇒-resp-ps) _ _

↠-impl : ∀ {V} {φ φ' ψ : Term V} → φ ↠ φ' → φ ⊃ ψ ↠ φ' ⊃ ψ
↠-impl = respects-RT₂ (λ _ _ → impl) _ _

↠-impr : ∀ {V} {φ ψ ψ' : Term V} → ψ ↠ ψ' → φ ⊃ ψ ↠ φ ⊃ ψ'
↠-impr = respects-RT₂ (λ _ _ → impr) _ _

↠-imp : ∀ {V} {φ φ' ψ ψ' : Term V} → φ ↠ φ' → ψ ↠ ψ' → φ ⊃ ψ ↠ φ' ⊃ ψ'
↠-imp φ↠φ' ψ↠ψ' = trans (↠-impl φ↠φ') (↠-impr ψ↠ψ')

↠-appT : ∀ {V} {M M' N : Term V} → M ↠ M' → appT M N ↠ appT M' N
↠-appT = respects-RT₂ (λ _ _ → appTl) _ _

↠-appP : ∀ {V} {δ δ' ε : Proof V} → δ ↠ δ' → appP δ ε ↠ appP δ' ε
↠-appP = respects-RT₂ (λ _ _ → appPl) _ _

↠-dir : ∀ {V} {P Q : Path V} {d} → P ↠ Q → dir d P ↠ dir d Q
↠-dir = respects-RT₂ (λ _ _ → dirR) _ _

↠-imp*l : ∀ {V} {P P' Q : Path V} → P ↠ P' → P ⊃* Q ↠ P' ⊃* Q
↠-imp*l = respects-RT₂ (λ _ _ → imp*l) _ _

↠-imp*r : ∀ {V} {P Q Q' : Path V} → Q ↠ Q' → P ⊃* Q ↠ P ⊃* Q'
↠-imp*r = respects-RT₂ (λ _ _ → imp*r) _ _

↠-imp* : ∀ {V} {P P' Q Q' : Path V} → P ↠ P' → Q ↠ Q' → P ⊃* Q ↠ P' ⊃* Q'
↠-imp* P↠P' Q↠Q' = trans (↠-imp*l P↠P') (↠-imp*r Q↠Q')
--TODO Duplication

↠-app*l : ∀ {V} {M N : Term V} {P P' Q} → P ↠ P' → app* M N P Q ↠ app* M N P' Q
↠-app*l = respects-RT₂ (λ _ _ → app*l) _ _

↠-reff : ∀ {V} {M N : Term V} → M ↠ N → reff M ↠ reff N
↠-reff = respects-RT₂ (λ _ _ → reffR) _ _

↠-APPP : ∀ {V} {δ δ' : Proof V} εε → δ ↠ δ' → APPP δ εε ↠ APPP δ' εε
↠-APPP εε = respects-RT₂ (λ _ _ → ⇒-APPP εε) _ _

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

private imp-red-inj₂' : ∀ {V} {φ ψ χ χ' : Term V} → χ ↠ χ' → χ ≡ φ ⊃ ψ → Σ[ φ' ∈ Term V ] Σ[ ψ' ∈ Term V ]
                      χ' ≡ φ' ⊃ ψ' × ψ ↠ ψ'
imp-red-inj₂' {χ' = χ'} (inc χ⇒χ') χ≡φ⊃ψ with imp-osr-inj₂ (subst (λ x → x ⇒ χ') χ≡φ⊃ψ χ⇒χ')
imp-red-inj₂' (inc χ⇒χ') χ≡φ⊃ψ | φ' ,p ψ' ,p χ'≡φ'⊃ψ' ,p φ⇒?φ' = φ' ,p ψ' ,p χ'≡φ'⊃ψ' ,p sub-R-RT φ⇒?φ'
imp-red-inj₂' {φ = φ} {ψ} ref χ≡φ⊃ψ = φ ,p ψ ,p χ≡φ⊃ψ ,p ref
imp-red-inj₂' (trans χ₂↠χ₂ χ₂↠χ₃) χ₂≡φ⊃ψ with imp-red-inj₂' χ₂↠χ₂ χ₂≡φ⊃ψ
imp-red-inj₂' (trans χ₂↠χ₂ χ₂↠χ₃) χ₂≡φ⊃ψ | φ' ,p ψ' ,p χ₂≡φ'⊃ψ' ,p φ↠φ' with imp-red-inj₂' χ₂↠χ₃ χ₂≡φ'⊃ψ'
imp-red-inj₂' (trans χ₂↠χ₂ χ₂↠χ₃) χ₂≡φ⊃ψ | φ' ,p ψ' ,p χ₂≡φ'⊃ψ' ,p φ↠φ' | φ'' ,p ψ'' ,p χ₃≡φ''⊃ψ'' ,p φ'↠φ'' = φ'' ,p ψ'' ,p χ₃≡φ''⊃ψ'' ,p trans φ↠φ' φ'↠φ''

imp-red-inj₂ : ∀ {V} {φ φ' ψ ψ' : Term V} → φ ⊃ ψ ↠ φ' ⊃ ψ' → ψ ↠ ψ'
imp-red-inj₂ φ⊃ψ↠φ'⊃ψ' with imp-red-inj₂' φ⊃ψ↠φ'⊃ψ' refl
imp-red-inj₂ {ψ = ψ} φ⊃ψ↠φ'⊃ψ' | φ'' ,p ψ'' ,p φ'⊃ψ'≡φ''⊃ψ'' ,p ψ↠ψ'' = subst (λ x → ψ ↠ x) (⊃-injr (≡-sym φ'⊃ψ'≡φ''⊃ψ'')) ψ↠ψ''

{- ⇒-dir' : ∀ {V} {P : Path V} {δ d} → dir d P ⇒ δ → Σ[ Q ∈ Path V ] P ⇒ Q × δ ≡ dir d Q
⇒-dir' (dirR P⇒Q) = _ ,p P⇒Q ,p refl
⇒-dir' refdir = {!!}

↠-dir' : ∀ {V} {P : Path V} {δ ε : Proof V} {d} → 
  δ ↠ ε → δ ≡ dir d P → Σ[ Q ∈ Path V ] P ↠ Q × ε ≡ dir d Q
↠-dir' {ε = ε} (inc δ⇒ε) δ≡P+ = let Q ,p P⇒Q ,p ε≡Q+ = ⇒-dir' (subst (λ x → x ⇒ ε) δ≡P+ δ⇒ε) in Q ,p inc P⇒Q ,p ε≡Q+
↠-dir' ref δ≡P+ = _ ,p ref ,p δ≡P+
↠-dir' (trans δ↠ε ε↠ε') δ≡P+ =
  let Q ,p P↠Q ,p ε≡Q+ = ↠-dir' δ↠ε δ≡P+ in
  let R ,p Q↠R ,p ε'≡R+ = ↠-dir' ε↠ε' ε≡Q+ in 
  R ,p trans P↠Q Q↠R ,p ε'≡R+ -}