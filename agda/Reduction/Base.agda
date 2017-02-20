import Relation.Binary.PropositionalEquality.Core
open import Level
open import Relation.Binary hiding (_⇒_)
open import Data.List
open import Prelims
open import Prelims.Closure
open import Grammar.Base

module Reduction.Base (G : Grammar) (R : Grammar.Reduction G) where
open import Grammar G

infix 4 _⇒_
data _⇒_ : Rewrite where
  redex : ∀ {V AA K} {c : Con (SK AA K)} {E : ListAbs V AA} {F} → 
    R c E F → app c E ⇒ F
  app : ∀ {V AA K} {c : Con (SK AA K)} {E F : ListAbs V AA} → 
    E ⇒ F → app c E ⇒ app c F
  appl : ∀ {V A AA E E' F} → 
    E ⇒ E' → _∷_ {V} {A} {AA} E F ⇒ E' ∷ F
  appr : ∀ {V A AA E F F'} → 
    F ⇒ F' → _∷_ {V} {A} {AA} E F ⇒ E ∷ F'

_⇒?_ : Rewrite
_⇒?_ = RClose _⇒_

_↠⁺_ : Rewrite
_↠⁺_ = TClose _⇒_

_↠_ : Rewrite
_↠_ = RTClose _⇒_

_≃_ : Rewrite
_≃_ = RSTClose _⇒_

redex-conv : ∀ {V} {K} {C} {c} {E} {F} → R {V} {K} {C} c E F → app c E ≃ F
redex-conv rcEF = inc (redex rcEF)

red-conv : ∀ {V} {C} {K} {M N : Subexp V C K} → M ↠ N → M ≃ N
red-conv = RT-sub-RST

respects : ∀ {U} {V} {K} {C} {L} {D} → Rewrite → (Subexp U K C → Subexp V L D) → Set
respects R f = ∀ {M N} → R M N → R (f M) (f N)

resp-RST : ∀ {U V K C L D} (R : Rewrite) f → respects {U} {V} {K} {C} {L} {D} R f → respects (RSTClose R) f
resp-RST R₁ f R-resp-f (inc xRy) = inc (R-resp-f xRy)
resp-RST R₁ f R-resp-f ref = ref
resp-RST R₁ f R-resp-f (RSTClose.sym RSTxy) = RSTClose.sym (resp-RST R₁ f R-resp-f RSTxy)
resp-RST R₁ f R-resp-f (RSTClose.trans RSTxy RSTyz) = RSTClose.trans (resp-RST R₁ f R-resp-f RSTxy) (resp-RST R₁ f R-resp-f RSTyz)

convl : ∀ {V} {A} {AA} {E E' : Abs V A} {FF : ListAbs V AA} → 
  E ≃ E' → (_∷_ {V} {A} {AA} E FF) ≃ (E' ∷ FF)
convl = resp-RST _⇒_ (λ x → x ∷ _) appl

convr : ∀ {V} {A} {AA} {E : Abs V A} {FF FF' : ListAbs V AA} → 
  FF ≃ FF' → (_∷_ {V} {A} {AA} E FF) ≃ (E ∷ FF')
convr (inc x) = inc (appr x)
convr ref = ref
convr (sym E≃E') = RSTClose.sym (convr E≃E')
convr (trans E≃E' E'≃E'') = RSTClose.trans (convr E≃E') (convr E'≃E'')

app-resp-red? : ∀ {V AA K} {c : Con (SK AA K)} {EE FF : ListAbs V AA} → EE ⇒? FF → app c EE ⇒? app c FF
app-resp-red? (inc EE⇒FF) = inc (app EE⇒FF)
app-resp-red? ref = ref

appl-resp-red? : ∀ {V A AA} {E E' : Abs V A} {FF : ListAbs V AA} → E ⇒? E' → (_∷_ {A = A} {AA} E FF) ⇒? (E' ∷ FF)
appl-resp-red? (inc E⇒E') = inc (appl E⇒E')
appl-resp-red? ref = ref

appr-resp-red? : ∀ {V A AA} {E : Abs V A} {FF FF' : ListAbs V AA} → FF ⇒? FF' → (_∷_ {A = A} {AA} E FF) ⇒? (E ∷ FF')
appr-resp-red? (inc FF⇒FF') = inc (appr FF⇒FF')
appr-resp-red? ref = ref

app-resp-conv : ∀ {V} {AA} {K} {c : Con (SK AA K)} {EE FF : ListAbs V AA} → EE ≃ FF → app c EE ≃ app c FF
app-resp-conv (inc EE⇒FF) = inc (app EE⇒FF)
app-resp-conv ref = ref
app-resp-conv (sym EE≃FF) = RSTClose.sym (app-resp-conv EE≃FF)
app-resp-conv (trans EE≃FF FF≃GG) = RSTClose.trans (app-resp-conv EE≃FF) (app-resp-conv FF≃GG)

respects₂ : ∀ {U} {V} {W} {K} {C} {L} {D} {M} {E} → Rewrite → (Subexp U K C → Subexp V L D → Subexp W M E) → Set
respects₂ R f = ∀ {M M' N N'} → R M M' → R N N' → R (f M N) (f M' N')

respects-red+ : ∀ {U} {V} {K} {C} {L} {D} {f} → 
  respects {U} {V} {K} {C} {L} {D} _⇒_ f → respects _↠⁺_ f
respects-red+ hyp (inc E→F) = inc (hyp E→F)
respects-red+ hyp (trans E↠F F↠G) = 
  Prelims.Closure.trans (respects-red+ hyp E↠F) (respects-red+ hyp F↠G)

respects-red : ∀ {U} {V} {K} {C} {L} {D} {f} → 
  respects {U} {V} {K} {C} {L} {D} _⇒_ f → respects _↠_ f
respects-red hyp (inc E→F) = inc (hyp E→F)
respects-red hyp ref = ref
respects-red hyp (trans E↠F F↠G) = 
  Prelims.Closure.trans (respects-red hyp E↠F) (respects-red hyp F↠G)

respects-conv : ∀ {U} {V} {K} {C} {L} {D} {f} → 
  respects {U} {V} {K} {C} {L} {D} _⇒_ f → respects _≃_ f
respects-conv hyp (inc E→F) = inc (hyp E→F)
respects-conv hyp ref = ref
respects-conv hyp (sym E≃F) = RSTClose.sym (respects-conv hyp E≃F)
respects-conv hyp (trans E≃F F≃G) = RSTClose.trans (respects-conv hyp E≃F) (respects-conv hyp F≃G)

app-resp-red : ∀ {V} {AA} {K} {c : Con (SK AA K)} {EE FF : ListAbs V AA} → EE ↠ FF → app c EE ↠ app c FF
app-resp-red = respects-red app

appl-resp-red : ∀ {V} {AA} {A} {E E' : Abs V A} {FF : ListAbs V AA} → E ↠ E' → (_∷_ {V} {A} {AA} E FF) ↠ (E' ∷ FF)
appl-resp-red = respects-red appl

appr-resp-red : ∀ {V} {AA} {A} {E : Abs V A} {FF FF' : ListAbs V AA} → FF ↠ FF' → (_∷_ {V} {A} {AA} E FF) ↠ (E ∷ FF')
appr-resp-red = respects-red appr

∷-red : ∀ {V} {AA} {A} {E E' : Abs V A} {FF FF' : ListAbs V AA} → E ↠ E' → FF ↠ FF' → (_∷_ {V} {A} {AA} E FF) ↠ (E' ∷ FF')
∷-red E↠E' FF↠FF' = Prelims.Closure.trans (appl-resp-red E↠E') (appr-resp-red FF↠FF')

module OpFamilies (Ops : OpFamily) where
  open OpFamily Ops

  respects' : Set
  respects' = ∀ {U V C K c M N σ} → 
    R {U} {C} {K} c M N → R {V} c (ap σ M) (ap σ N)

  aposrr : ∀ {U} {V} {C} {K} {σ : Op U V} → 
    respects' → respects _⇒_ (ap {C = C} {K = K} σ)
  aposrr hyp (redex M▷N) = redex (hyp M▷N)
  aposrr hyp (app MM→NN) = app (aposrr hyp MM→NN)
  aposrr hyp (appl M→N) = appl (aposrr hyp M→N)
  aposrr hyp (appr NN→PP) = appr (aposrr hyp NN→PP)

  apredr : ∀ {U} {V} {C} {K} {σ : Op U V} {E F : Subexp U C K} → 
    respects' → E ↠ F → ap σ E ↠ ap σ F
  apredr resp = respects-red (aposrr resp)

  _↠op_ : ∀ {U V} → Op U V → Op U V → Set
  _↠op_ {U} {V} σ τ = ∀ K (x : Var U K) → apV σ x ↠ apV τ x

  liftOp-red : ∀ {U V K} {ρ σ : Op U V} → respects' →
    ρ ↠op σ → liftOp K ρ ↠op liftOp K σ
  liftOp-red _ _ _ x₀ = subst₂ _↠_ (Prelims.sym liftOp-x₀) (Prelims.sym liftOp-x₀) ref
  liftOp-red hyp ρ↠σ K (↑ x) = subst₂ _↠_ (Prelims.sym (liftOp-↑ x)) (Prelims.sym (liftOp-↑ x)) 
    (apredr hyp (ρ↠σ K x))

  liftsOp-red : ∀ {U V A} {ρ σ : Op U V} → respects' → 
    ρ ↠op σ → liftsOp A ρ ↠op liftsOp A σ
  liftsOp-red {A = []} _ ρ↠σ = ρ↠σ
  liftsOp-red {A = K ∷ A} hyp ρ↠σ = liftsOp-red {A = A} hyp (liftOp-red hyp ρ↠σ)

  apredl : ∀ {U V C K} {ρ σ : Op U V} {E : Subexp U C K} → 
    respects' → ρ ↠op σ → ap ρ E ↠ ap σ E
  apredl {E = var x} hyp ρ↠σ = ρ↠σ _ x
  apredl {E = app _ E} hyp ρ↠σ = respects-red app (apredl {E = E} hyp ρ↠σ)
  apredl {E = []} _ _ = ref
  apredl {E = _∷_ {A = SK A _} E F} hyp ρ↠σ = Prelims.Closure.trans (respects-red appl (apredl {E = E} hyp (liftsOp-red {A = A} hyp ρ↠σ))) (respects-red appr (apredl {E = F} hyp ρ↠σ))

  record creation (_▷_ : Rewrite) {U V C K} 
    (M : Subexp U C K) {N} 
    {σ : Op U V} (δ : ap σ M ▷ N) : Set where
    field
      created : Subexp U C K
      red-created : M ▷ created
      ap-created : ap σ created ≡ N

  creates : Rewrite → Set
  creates ▷ = ∀ {U V C K} M {N σ} δ → 
    creation ▷ {U} {V} {C} {K} M {N} {σ} δ

  record creation' {U V C K c} M {N} 
    {σ : Op U V} (δ : R {V} {C} {K} c (ap σ M) N) : Set where
    field
      created : Expression U K
      red-created : R c M created
      ap-created : ap σ created ≡ N

  creates' : Set
  creates' = ∀ {U V C K c} M {N σ} δ → 
    creation' {U} {V} {C} {K} {c} M {N} {σ} δ

open OpFamilies public

_↠s_ : ∀ {U V} → Sub U V → Sub U V → Set
_↠s_ = _↠op_ SUB

botsub-red : ∀ {V} {K} {E F : Expression V (varKind K)} → 
  E ⇒ F → x₀:= E ↠s x₀:= F
botsub-red E⇒F _ x₀ = inc E⇒F
botsub-red _ _ (↑ _) = ref

create-osr : creates' REP → creates REP _⇒_
create-osr _ (var _) ()
create-osr hyp (app c E) (redex cσE⇒F) =
  let open creation' (hyp E cσE⇒F) in
  record { 
    created = created;
    red-created = redex red-created;
    ap-created = ap-created 
    }
create-osr hyp (app c E) (app σE⇒F) =     
  let open creation (create-osr hyp E σE⇒F) in 
  record { 
    created = app c created; 
    red-created = app red-created; 
    ap-created = cong (app c) ap-created 
    }
create-osr _ [] ()
create-osr hyp (_∷_ E F) {σ = σ} (appl σE⇒E') =     
  let open creation (create-osr hyp E σE⇒E') in 
  record { 
    created = _∷_ created F; 
    red-created = appl red-created; 
    ap-created = cong (λ x → _∷_ x (F 〈 σ 〉)) ap-created
    }
create-osr hyp (_∷_ {A = SK A _} E F) {σ = σ} (appr {F' = F'} σF⇒F') =     
  let open creation {Ops = REP} (create-osr hyp F σF⇒F') in 
  record { 
    created = _∷_ E created; 
    red-created = appr red-created; 
    ap-created = cong (_∷_ (E 〈 OpFamily.liftsOp REP A σ 〉)) ap-created
    }

