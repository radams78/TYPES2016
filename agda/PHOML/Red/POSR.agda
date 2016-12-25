--Parallel one-step reduction
module PHOML.Red.POSR where
open import Prelims.Closure.RT
open import PHOML.Grammar
open import PHOML.PathSub
open import PHOML.Red.Base
open import PHOML.Red.RTRed

data _▷_ : ∀ {V K} → VExpression V K → VExpression V K → Set where
  ref : ∀ {V K} {E : VExpression V K} → E ▷ E
  βT : ∀ {V A M} {N : Term V} → appT (ΛT A M) N ▷ M ⟦ x₀:= N ⟧
  appTl : ∀ {V} {M M' N : Term V} → M ▷ M' → appT M N ▷ appT M' N
  imp : ∀ {V} {φ φ' ψ ψ' : Term V} → φ ▷ φ' → ψ ▷ ψ' → φ ⊃ ψ ▷ φ' ⊃ ψ'
  βP : ∀ {V} {φ : Term V} {δ ε} → appP (ΛP φ δ) ε ▷ δ ⟦ x₀:= ε ⟧
  refdir : ∀ {V} {φ : Term V} {d} → dir d (reff φ) ▷ ΛP φ (var x₀)
  ΛPR : ∀ {V} {φ φ' : Term V} {δ} → φ ▷ φ' → ΛP φ δ ▷ ΛP φ' δ
  appPl : ∀ {V} {δ δ' ε : Proof V} → δ ▷ δ' → appP δ ε ▷ appP δ' ε
  univplus : ∀ {V} {φ ψ : Term V} {δ ε} → plus (univ φ ψ δ ε) ▷ δ
  univminus : ∀ {V} {φ ψ : Term V} {δ ε} → minus (univ φ ψ δ ε) ▷ ε
  dirR : ∀ {V} {P Q : Path V} {d} → P ▷ Q → dir d P ▷ dir d Q
  βE : ∀ {V} {M N : Term V} {A P Q} → app* M N (λλλ A P) Q ▷ P ⟦ x₂:= M ,x₁:= N ,x₀:= Q ⟧
  βPP : ∀ {V} {N N' : Term V} {A M P} → app* N N' (reff (ΛT A M)) P ▷ M ⟦⟦ x₀::= P ∶ x₀:= N ≡ x₀:= N' ⟧⟧
  ref⊃*ref : ∀ {V} {φ ψ : Term V} → (reff φ ⊃* reff ψ) ▷ reff (φ ⊃ ψ)
  ref⊃*univ : ∀ {V} {φ ψ χ : Term V} {δ ε} → 
    (reff φ ⊃* univ ψ χ δ ε) ▷ univ (φ ⊃ ψ) (φ ⊃ χ) (ΛP (φ ⊃ ψ) (ΛP (φ ⇑) (appP (δ ⇑ ⇑) (appP (var x₁) (var x₀))))) (ΛP (φ ⊃ χ) (ΛP (φ ⇑) (appP (ε ⇑ ⇑) (appP (var x₁) (var x₀)))))
  univ⊃*ref : ∀ {V} {φ ψ χ : Term V} {δ ε} →
    (univ φ ψ δ ε ⊃* reff χ) ▷ univ (φ ⊃ χ) (ψ ⊃ χ) (ΛP (φ ⊃ χ) (ΛP (ψ ⇑) (appP (var x₁) (appP (ε ⇑ ⇑) (var x₀))))) (ΛP (ψ ⊃ χ) (ΛP (φ ⇑) (appP (var x₁) (appP (δ ⇑ ⇑) (var x₀)))))
  univ⊃*univ : ∀ {V} {φ φ' ψ ψ' : Term V} {δ δ' ε ε'} →
    (univ φ ψ δ ε ⊃* univ φ' ψ' δ' ε') ▷ univ (φ ⊃ φ') (ψ ⊃ ψ') (ΛP (φ ⊃ φ') (ΛP (ψ ⇑) (appP (δ' ⇑ ⇑) (appP (var x₁) (appP (ε ⇑ ⇑) (var x₀)))))) (ΛP (ψ ⊃ ψ') (ΛP (φ ⇑) (appP (ε' ⇑ ⇑) (appP (var x₁) (appP (δ ⇑ ⇑) (var x₀))))))
  app*l : ∀ {V M N} {P P' Q : Path V} → P ▷ P' → app* M N P Q ▷ app* M N P' Q
  reffR : ∀ {V} {M N : Term V} → M ▷ N → reff M ▷ reff N
  ⊃* : ∀ {V} {P P' Q Q' : Path V} → P ▷ P' → Q ▷ Q' → (P ⊃* Q) ▷ (P' ⊃* Q')
  univR : ∀ {V} {φ φ' ψ ψ' : Term V} {δ δ' ε ε'} → φ ▷ φ' → ψ ▷ ψ' → δ ▷ δ' → ε ▷ ε' → univ φ ψ δ ε ▷ univ φ' ψ' δ' ε'

sub-⇒-▷ : ∀ {V K} {E F : VExpression V K} → E ⇒ F → E ▷ F
sub-⇒-▷ βT = βT
sub-⇒-▷ (appTl E⇒F) = appTl (sub-⇒-▷ E⇒F)
sub-⇒-▷ (impl E⇒F) = imp (sub-⇒-▷ E⇒F) ref
sub-⇒-▷ (impr E⇒F) = imp ref (sub-⇒-▷ E⇒F)
sub-⇒-▷ βP = βP
sub-⇒-▷ refdir = refdir
sub-⇒-▷ (ΛPR φ⇒φ') = ΛPR (sub-⇒-▷ φ⇒φ')
sub-⇒-▷ (appPl E⇒F) = appPl (sub-⇒-▷ E⇒F)
sub-⇒-▷ univplus = univplus
sub-⇒-▷ univminus = univminus
sub-⇒-▷ (dirR E⇒F) = dirR (sub-⇒-▷ E⇒F)
sub-⇒-▷ βE = βE
sub-⇒-▷ βPP = βPP
sub-⇒-▷ ref⊃* = ref⊃*ref
sub-⇒-▷ ref⊃*univ = ref⊃*univ
sub-⇒-▷ univ⊃*ref = univ⊃*ref
sub-⇒-▷ univ⊃*univ = univ⊃*univ
sub-⇒-▷ (app*l E⇒F) = app*l (sub-⇒-▷ E⇒F)
sub-⇒-▷ (reffR E⇒F) = reffR (sub-⇒-▷ E⇒F)
sub-⇒-▷ (imp*l E⇒F) = ⊃* (sub-⇒-▷ E⇒F) ref
sub-⇒-▷ (imp*r E⇒F) = ⊃* ref (sub-⇒-▷ E⇒F)
sub-⇒-▷ (univ₁ φ⇒φ') = univR (sub-⇒-▷ φ⇒φ') ref ref ref
sub-⇒-▷ (univ₂ ψ⇒ψ') = univR ref (sub-⇒-▷ ψ⇒ψ') ref ref
sub-⇒-▷ (univ₃ δ⇒δ') = univR ref ref (sub-⇒-▷ δ⇒δ') ref
sub-⇒-▷ (univ₄ ε⇒ε') = univR ref ref ref (sub-⇒-▷ ε⇒ε')

sub-▷-↠ : ∀ {V K} {E F : VExpression V K} → E ▷ F → E ↠ F
sub-▷-↠ ref = ref
sub-▷-↠ βT = inc βT
sub-▷-↠ (appTl E▷F) = ↠-appT (sub-▷-↠ E▷F)
sub-▷-↠ (imp φ▷φ' ψ▷ψ') = ↠-imp (sub-▷-↠ φ▷φ') (sub-▷-↠ ψ▷ψ')
sub-▷-↠ βP = inc βP
sub-▷-↠ refdir = inc refdir
sub-▷-↠ (ΛPR φ▷φ') = ↠-ΛP (sub-▷-↠ φ▷φ')
sub-▷-↠ (appPl E▷F) = ↠-appP (sub-▷-↠ E▷F)
sub-▷-↠ univplus = inc univplus
sub-▷-↠ univminus = inc univminus
sub-▷-↠ (dirR E▷F) = ↠-dir (sub-▷-↠ E▷F)
sub-▷-↠ βE = inc βE
sub-▷-↠ βPP = inc βPP
sub-▷-↠ ref⊃*ref = inc ref⊃*
sub-▷-↠ ref⊃*univ = inc ref⊃*univ
sub-▷-↠ univ⊃*ref = inc univ⊃*ref
sub-▷-↠ univ⊃*univ = inc univ⊃*univ
sub-▷-↠ (app*l E▷F) = ↠-app*l (sub-▷-↠ E▷F)
sub-▷-↠ (reffR E▷F) = ↠-reff (sub-▷-↠ E▷F)
sub-▷-↠ (⊃* P▷P' Q▷Q') = ↠-imp* (sub-▷-↠ P▷P') (sub-▷-↠ Q▷Q')
sub-▷-↠ (univR φ▷φ' ψ▷ψ' P▷P' Q▷Q') = ↠-univ (sub-▷-↠ φ▷φ') (sub-▷-↠ ψ▷ψ') (sub-▷-↠ P▷P') (sub-▷-↠ Q▷Q')
