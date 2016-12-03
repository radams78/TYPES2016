module PHOPL.Red where

open import Level
open import Data.Product
open import Prelims.Closure
open import PHOPL.Grammar
open import PHOPL.PathSub

data _⇒_ : ∀ {V K} → Expression V K → Expression V K → Set where

_↠_ : ∀ {V K} → Expression V K → Expression V K → Set
_↠_ {V} {K} = RTClose (_⇒_ {V} {K})

_≃_ : ∀ {V K} → Expression V K → Expression V K → Set
_≃_ {V} {K} = RSTClose (_⇒_ {V} {K})

diamond : ∀ {V K} → Diamond (_⇒_ {V} {K}) _⇒_
diamond _ _ _ ()

red-resp-ps : ∀ {U V} {M N : Term U} {τ : PathSub U V} {ρ σ} → M ⇒ N → M ⟦⟦ τ ∶ ρ ∼ σ ⟧⟧ ⇒ N ⟦⟦ τ ∶ ρ ∼ σ ⟧⟧
red-resp-ps ()

