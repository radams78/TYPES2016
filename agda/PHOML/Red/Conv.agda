module PHOML.Red.Conv where
open import Data.Unit
open import Data.Product
open import Prelims
open import Prelims.Closure.RST
open import PHOML.Grammar
open import PHOML.Red.Base
open import PHOML.Red.RTRed
open import PHOML.Red.Diamond

_≃_ : ∀ {V K} → Expression V K → Expression V K → Set
_≃_ {V} {K} = RSTClose (_⇒_ {V} {K})

≃-resp-rep : ∀ {U V K} {E F : Expression U K} {ρ : Rep U V} → E ≃ F → E 〈 ρ 〉 ≃ F 〈 ρ 〉
≃-resp-rep {ρ = ρ} = respects-RST (λ V → _⇒_ {V}) (λ x → x 〈 ρ 〉) (λ _ _ → ⇒-resp-rep) _ _

≃-resp-sub : ∀ {U V} {M N : Term U} {σ : Sub U V} → M ≃ N → M ⟦ σ ⟧ ≃ N ⟦ σ ⟧
≃-resp-sub = respects-RST₂ (λ _ _ → ⇒-resp-sub) _ _

≃-impl : ∀ {V} {φ φ' ψ : Term V} → φ ≃ φ' → φ ⊃ ψ ≃ φ' ⊃ ψ
≃-impl {V} = respects-RST {A = ⊤} (λ _ → _⇒_ {V} { -vTerm}) _ (λ _ _ → impl) _ _

≃-impr : ∀ {V} {φ ψ ψ' : Term V} → ψ ≃ ψ' → φ ⊃ ψ ≃ φ ⊃ ψ'
≃-impr {V} = respects-RST {A = ⊤} (λ _ → _⇒_ {V} { -vTerm}) _ (λ _ _ → impr) _ _

≃-imp : ∀ {V} {φ φ' ψ ψ' : Term V} → φ ≃ φ' → ψ ≃ ψ' → φ ⊃ ψ ≃ φ' ⊃ ψ'
≃-imp φ≃φ' ψ≃ψ' = trans (≃-impl φ≃φ') (≃-impr ψ≃ψ')

≃-appTl : ∀ {V} {M M' N : Term V} → M ≃ M' → appT M N ≃ appT M' N
≃-appTl {V} = respects-RST {A = ⊤} (λ _ → _⇒_ {V} { -vTerm}) _ (λ _ _ → appTl) _ _

PHOML-Church-Rosser : ∀ {V K} {E F : Expression V K} → E ≃ F → Common-Reduct _↠_ _↠_ E F
PHOML-Church-Rosser (inc E⇒F) = cr _ (inc E⇒F) ref
PHOML-Church-Rosser ref = cr _ ref ref
PHOML-Church-Rosser (sym E≃F) = 
  let cr G E↠G F↠G = PHOML-Church-Rosser E≃F in cr G F↠G E↠G
PHOML-Church-Rosser (trans E≃F F≃G) = 
  let cr H E↠H F↠H = PHOML-Church-Rosser E≃F in 
  let cr K F↠K G↠K = PHOML-Church-Rosser F≃G in 
  let cr L H↠L K↠L = diamond F↠H F↠K in 
  cr L (trans E↠H H↠L) (trans G↠K K↠L)
