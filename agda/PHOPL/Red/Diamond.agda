module PHOPL.Red.Diamond where
open import Prelims
open import PHOPL.Grammar
open import PHOPL.Red.Base

diamond : ∀ {V K} {E F G : Expression V K} → E ⇒ F → E ⇒ G →
  Common-Reduct (RClose (_⇒_ {V})) (RClose _⇒_) F G
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
diamond (plusR P⇒P') (plusR P⇒P'') = 
  let cr P₀ P'⇒?P₀ P''⇒?P₀ = diamond P⇒P' P⇒P'' in 
  cr (plus P₀) (⇒?-plus P'⇒?P₀) (⇒?-plus P''⇒?P₀)
diamond (minusR P⇒P') (minusR P⇒P'') = 
  let cr P₀ P'⇒?P₀ P''⇒?P₀ = diamond P⇒P' P⇒P'' in 
  cr (minus P₀) (⇒?-minus P'⇒?P₀) (⇒?-minus P''⇒?P₀)
diamond βE βE = cr _ ref ref
diamond (imp*l {Q = Q} P⇒P') (imp*l P⇒P'') = 
  let cr P₀ P'⇒?P₀ P''⇒?P₀ = diamond P⇒P' P⇒P'' in 
  cr (P₀ ⊃* Q) (⇒?-imp*l P'⇒?P₀) (⇒?-imp*l P''⇒?P₀)
diamond (imp*r {Q' = Q'} Q⇒Q') (imp*l {P' = P'} P⇒P') = cr (P' ⊃* Q') (inc (imp*l P⇒P')) (inc (imp*r Q⇒Q'))
diamond (imp*l {P' = P'} P⇒P') (imp*r {Q' = Q'} Q⇒Q') = cr (P' ⊃* Q') (inc (imp*r Q⇒Q')) (inc (imp*l P⇒P'))
diamond (imp*r {P = P} Q⇒Q') (imp*r Q⇒Q'') = 
  let cr Q₀ Q'⇒?Q₀ Q''⇒?Q₀ = diamond Q⇒Q' Q⇒Q'' in 
  cr (P ⊃* Q₀) (⇒?-imp*r Q'⇒?Q₀) (⇒?-imp*r Q''⇒?Q₀)
diamond (app*l ()) βE
diamond βE (app*l ())
diamond (app*l {M = M} {N = N} {Q = Q} P⇒P') (app*l P⇒P'') = 
  let cr P₀ P'⇒?P₀ P''⇒?P₀ = diamond P⇒P' P⇒P'' in 
  cr (app* M N P₀ Q) (⇒?-app*l P'⇒?P₀) (⇒?-app*l P''⇒?P₀)

