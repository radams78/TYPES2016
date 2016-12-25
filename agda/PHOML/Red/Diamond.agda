module PHOML.Red.Diamond where
open import Prelims
open import PHOML.Grammar
open import PHOML.PathSub
open import PHOML.Red.Base
open import PHOML.Red.RRed
open import PHOML.Red.RTRed

data _▷_ : ∀ {V K} → VExpression V K → VExpression V K → Set where
  ref : ∀ {V K} {E : VExpression V K} → E ▷ E
  βT : ∀ {V A M} {N : Term V} → appT (ΛT A M) N ▷ M ⟦ x₀:= N ⟧
  appTl : ∀ {V} {M M' N : Term V} → M ▷ M' → appT M N ▷ appT M' N
  imp : ∀ {V} {φ φ' ψ ψ' : Term V} → φ ▷ φ' → ψ ▷ ψ' → φ ⊃ ψ ▷ φ' ⊃ ψ'
  βP : ∀ {V} {φ : Term V} {δ ε} → appP (ΛP φ δ) ε ▷ δ ⟦ x₀:= ε ⟧
  refdir : ∀ {V} {φ : Term V} {d} → dir d (reff φ) ▷ ΛP φ (var x₀)
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

_▷*_ : ∀ {V K} → VExpression V K → VExpression V K → Set
_▷*_ = RTClose _▷_

sub-↠-▷* : ∀ {V K} {E F : VExpression V K} → E ↠ F → E ▷* F
sub-↠-▷* = monoRT sub-⇒-▷

sub-▷-↠ : ∀ {V K} {E F : VExpression V K} → E ▷ F → E ↠ F
sub-▷-↠ ref = ref
sub-▷-↠ βT = inc βT
sub-▷-↠ (appTl E▷F) = ↠-appT (sub-▷-↠ E▷F)
sub-▷-↠ (imp φ▷φ' ψ▷ψ') = ↠-imp (sub-▷-↠ φ▷φ') (sub-▷-↠ ψ▷ψ')
sub-▷-↠ βP = inc βP
sub-▷-↠ refdir = inc refdir
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

sub-▷*-↠ : ∀ {V K} {E F : VExpression V K} → E ▷* F → E ↠ F
sub-▷*-↠ (inc E▷F) = sub-▷-↠ E▷F
sub-▷*-↠ ref = ref
sub-▷*-↠ (trans E▷*F F▷*G) = trans (sub-▷*-↠ E▷*F) (sub-▷*-↠ F▷*G)

postulate diamond : ∀ {V K} {E F G : Expression V K} → E ↠ F → E ↠ G →
                  Common-Reduct _↠_ _↠_ F G

{- diamond : ∀ {V K} {E F G : Expression V K} → E ⇒ F → E ⇒ G →
  Common-Reduct (_⇒?_ {V} {K}) (RClose _⇒_) F G
diamond βT βT = cr _ ref ref
diamond (appTl ()) βT
diamond βT (appTl ())
diamond (appTl {N = N} M⇒M') (appTl M⇒M'') = 
  let cr M₀ M'⇒?M₀ M''⇒?M₀ = diamond M⇒M' M⇒M'' in 
  cr (appT M₀ N) (⇒?-appTl M'⇒?M₀) (⇒?-appTl M''⇒?M₀)
diamond (impl {ψ = ψ} φ⇒φ') (impl φ⇒φ'') = 
  let cr φ₀ φ'⇒?φ₀ φ''⇒?φ₀ = diamond φ⇒φ' φ⇒φ'' in 
  cr (φ₀ ⊃ ψ) (⇒?-impl φ'⇒?φ₀) (⇒?-impl φ''⇒?φ₀)
diamond (impl {φ' = φ'} φ⇒φ') (impr {ψ' = ψ'} ψ⇒ψ') = cr (φ' ⊃ ψ') (inc (impr ψ⇒ψ')) (inc (impl φ⇒φ'))
diamond (impr {ψ' = ψ'} ψ⇒ψ') (impl {φ' = φ'} φ⇒φ') = cr (φ' ⊃ ψ') (inc (impl φ⇒φ')) (inc (impr ψ⇒ψ'))
diamond (impr {φ = φ} ψ⇒ψ') (impr ψ⇒ψ'') = 
  let cr ψ₀ ψ'⇒?ψ₀ ψ''⇒?ψ₀ = diamond ψ⇒ψ' ψ⇒ψ'' in 
  cr (φ ⊃ ψ₀) (⇒?-impr ψ'⇒?ψ₀) (⇒?-impr ψ''⇒?ψ₀)
diamond (appPl {ε = ε} δ⇒δ') (appPl δ⇒δ'') = 
  let cr δ₀ δ'⇒?δ₀ δ''⇒?δ₀ = diamond δ⇒δ' δ⇒δ'' in 
  cr (appP δ₀ ε) (⇒?-appPl δ'⇒?δ₀) (⇒?-appPl δ''⇒?δ₀)
diamond refdir (dirR (reffR _)) = cr _ ref {!!}
diamond (dirR (reffR _)) refdir = cr _ {!!} ref
diamond refdir refdir = cr _ ref ref
diamond (dirR P⇒P') (dirR P⇒P'') = 
  let cr P₀ P'⇒?P₀ P''⇒?P₀ = diamond P⇒P' P⇒P'' in 
  cr (dir _ P₀) (⇒?-dir P'⇒?P₀) (⇒?-dir P''⇒?P₀)
diamond βE βE = cr _ ref ref
diamond ref⊃* ref⊃* = cr _ ref ref
diamond (imp*l (reffR φ⇒φ')) ref⊃* = cr _ (inc ref⊃*) (inc (reffR (impl φ⇒φ')))
diamond (imp*r (reffR φ⇒φ')) ref⊃* = cr _ (inc ref⊃*) (inc (reffR (impr φ⇒φ')))
diamond ref⊃* (imp*l (reffR φ⇒φ')) = cr _ (inc (reffR (impl φ⇒φ'))) (inc ref⊃*)
diamond ref⊃* (imp*r (reffR φ⇒φ')) = cr _ (inc (reffR (impr φ⇒φ'))) (inc ref⊃*)
diamond (imp*l {Q = Q} P⇒P') (imp*l P⇒P'') = 
  let cr P₀ P'⇒?P₀ P''⇒?P₀ = diamond P⇒P' P⇒P'' in 
  cr (P₀ ⊃* Q) (⇒?-imp*l P'⇒?P₀) (⇒?-imp*l P''⇒?P₀)
diamond (imp*r {Q' = Q'} Q⇒Q') (imp*l {P' = P'} P⇒P') = cr (P' ⊃* Q') (inc (imp*l P⇒P')) (inc (imp*r Q⇒Q'))
diamond (imp*l {P' = P'} P⇒P') (imp*r {Q' = Q'} Q⇒Q') = cr (P' ⊃* Q') (inc (imp*r Q⇒Q')) (inc (imp*l P⇒P'))
diamond (imp*r {P = P} Q⇒Q') (imp*r Q⇒Q'') = 
  let cr Q₀ Q'⇒?Q₀ Q''⇒?Q₀ = diamond Q⇒Q' Q⇒Q'' in 
  cr (P ⊃* Q₀) (⇒?-imp*r Q'⇒?Q₀) (⇒?-imp*r Q''⇒?Q₀)
diamond (app*l ()) βE
diamond βP βP = cr _ ref ref
diamond (app*l (reffR ())) βP
diamond βP (app*l (reffR ()))
diamond βE (app*l ())
diamond (app*l {M = M} {N = N} {Q = Q} P⇒P') (app*l P⇒P'') = 
  let cr P₀ P'⇒?P₀ P''⇒?P₀ = diamond P⇒P' P⇒P'' in 
  cr (app* M N P₀ Q) (⇒?-app*l P'⇒?P₀) (⇒?-app*l P''⇒?P₀)
diamond (reffR M⇒N₁) (reffR M⇒N₂) = 
  let cr L N₁⇒?L N₂⇒?L = diamond M⇒N₁ M⇒N₂ in 
  cr (reff L) (⇒?-reff N₁⇒?L) (⇒?-reff N₂⇒?L) -}
