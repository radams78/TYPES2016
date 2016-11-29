open import Grammar.Base

module Reduction.SN (G : Grammar) (R : Grammar.Reduction G) where

open import Prelims
open import Prelims.Closure
open import Grammar G
open import Reduction.Base G R

data SN {V C K} : Subexp V C K → Set where
  SNI : ∀ E → (∀ F → E ⇒ F → SN F) → SN E

SNapp' : ∀ {V K AA} {c : Con (SK AA K)} {E : ListAbs V AA} → SN (app c E) → SN E
SNapp' {c = c} {E = E} (SNI _ SNcE) = SNI E (λ F E→F → SNapp' (SNcE (app c F) (app E→F)))

SNappl' : ∀ {V A L M N} → SN (_∷_ {V} {A} {L} M N) → SN M
SNappl' {V} {A} {L} {M} {N} (SNI _ SNM) = 
  SNI M (λ M' M⇒M' → SNappl' (SNM (M' ∷ N) (appl M⇒M')))

SNappr' : ∀ {V A L M N} → SN (_∷_ {V} {A} {L} M N) → SN N
SNappr' {V} {A} {L} {M} {N} (SNI _ SNN) = 
  SNI N (λ N' N⇒N' → SNappr' (SNN (M ∷ N') (appr N⇒N')))

SNap' : ∀ {Ops U V C K} {E : Subexp U C K} {σ : OpFamily.Op Ops U V} →
  respects' Ops → SN (OpFamily.ap Ops σ E) → SN E
SNap' {Ops} {E = E} {σ = σ} hyp (SNI _ SNσE) = 
  SNI E (λ F E→F → SNap' {Ops} hyp (SNσE _ (aposrr Ops hyp E→F)))

SNrep : ∀ {U V C K} {E : Subexp U C K} {σ : Rep U V} →
  creates' REP → SN E → SN (E 〈 σ 〉)
SNrep {U} {V} {C} {K} {E} {σ} hyp (SNI .E SNE) = SNI (E 〈 σ 〉) (λ F σE⇒F → 
  let open creation {Ops = REP} (create-osr hyp E σE⇒F) in
  subst SN ap-created (SNrep hyp (SNE created red-created)))

SNred : ∀ {V K} {E F : Expression V K} → SN E → E ↠ F → SN F
SNred {V} {K} {E} {F} (SNI .E SNE) (inc E→F) = SNE F E→F
SNred SNE ref = SNE
SNred SNE (trans E↠F F↠G) = SNred (SNred SNE E↠F) F↠G

SNvar : ∀ {V} {K} (x : Var V K) → SN (var x)
SNvar x = SNI (var x) (λ _ ())
