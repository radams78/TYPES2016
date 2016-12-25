--Parallel reduction
module PHOML.Red.PRed where
open import Prelims.Closure.RT
open import PHOML.Grammar
open import PHOML.Red.RTRed
open import PHOML.Red.POSR

_▷*_ : ∀ {V K} → VExpression V K → VExpression V K → Set
_▷*_ = RTClose _▷_

sub-↠-▷* : ∀ {V K} {E F : VExpression V K} → E ↠ F → E ▷* F
sub-↠-▷* = monoRT sub-⇒-▷

sub-▷*-↠ : ∀ {V K} {E F : VExpression V K} → E ▷* F → E ↠ F
sub-▷*-↠ (inc E▷F) = sub-▷-↠ E▷F
sub-▷*-↠ ref = ref
sub-▷*-↠ (trans E▷*F F▷*G) = trans (sub-▷*-↠ E▷*F) (sub-▷*-↠ F▷*G)
