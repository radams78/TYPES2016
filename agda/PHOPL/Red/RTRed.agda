module PHOPL.Red.RTRed where
open import Prelims
open import PHOPL.Grammar
open import PHOPL.Red.Base

_↠_ : ∀ {V K} → Expression V K → Expression V K → Set
_↠_ {V} {K} = RTClose (_⇒_ {V} {K})

↠-resp-rep : ∀ {U V K} {E F : Expression U K} {ρ : Rep U V} → E ↠ F → E 〈 ρ 〉 ↠ F 〈 ρ 〉
↠-resp-rep (inc E⇒F) = inc (⇒-resp-rep E⇒F)
↠-resp-rep ref = ref
↠-resp-rep (trans E↠F F↠G) = trans (↠-resp-rep E↠F) (↠-resp-rep F↠G)
