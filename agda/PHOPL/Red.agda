module PHOPL.Red where

open import Level
open import Data.Product
open import Prelims.Closure
open import PHOPL.Grammar
open import PHOPL.PathSub

data _⇒_ : ∀ {V K} → Expression V K → Expression V K → Set where

diamond : ∀ {V K} → Diamond (_⇒_ {V} {K}) _⇒_
diamond _ _ _ ()

⇒-resp-rep : ∀ {U V K} {E F : Expression U K} {ρ : Rep U V} → E ⇒ F → E 〈 ρ 〉 ⇒ F 〈 ρ 〉
⇒-resp-rep ()

⇒-resp-ps : ∀ {U V} {M N : Term U} {τ : PathSub U V} {ρ σ} → M ⇒ N → M ⟦⟦ τ ∶ ρ ∼ σ ⟧⟧ ⇒ N ⟦⟦ τ ∶ ρ ∼ σ ⟧⟧
⇒-resp-ps ()

_↠_ : ∀ {V K} → Expression V K → Expression V K → Set
_↠_ {V} {K} = RTClose (_⇒_ {V} {K})

↠-resp-rep : ∀ {U V K} {E F : Expression U K} {ρ : Rep U V} → E ↠ F → E 〈 ρ 〉 ↠ F 〈 ρ 〉
↠-resp-rep (inc E⇒F) = inc (⇒-resp-rep E⇒F)
↠-resp-rep ref = ref
↠-resp-rep (trans E↠F F↠G) = trans (↠-resp-rep E↠F) (↠-resp-rep F↠G)

_≃_ : ∀ {V K} → Expression V K → Expression V K → Set
_≃_ {V} {K} = RSTClose (_⇒_ {V} {K})

≃-resp-rep : ∀ {U V K} {E F : Expression U K} {ρ : Rep U V} → E ≃ F → E 〈 ρ 〉 ≃ F 〈 ρ 〉
≃-resp-rep (inc E⇒F) = inc (⇒-resp-rep E⇒F)
≃-resp-rep ref = ref
≃-resp-rep (sym E≃F) = sym (≃-resp-rep E≃F)
≃-resp-rep (trans E≃F F≃G) = trans (≃-resp-rep E≃F) (≃-resp-rep F≃G)
