module PHOPL.Red.Base where

open import Level
open import Data.Bool
open import Data.Product
open import Prelims
open import PHOPL.Grammar
open import PHOPL.PathSub

infix 10 _⇒_
data _⇒_ : ∀ {V K} → Expression V K → Expression V K → Set where
  βT : ∀ {V A M} {N : Term V} → appT (ΛT A M) N ⇒ M ⟦ x₀:= N ⟧
  appTl : ∀ {V} {M M' N : Term V} → M ⇒ M' → appT M N ⇒ appT M' N
  impl : ∀ {V} {φ φ' ψ : Term V} → φ ⇒ φ' → φ ⊃ ψ ⇒ φ' ⊃ ψ
  impr : ∀ {V} {φ ψ ψ' : Term V} → ψ ⇒ ψ' → φ ⊃ ψ ⇒ φ ⊃ ψ'
  appPl : ∀ {V} {δ δ' ε : Proof V} → δ ⇒ δ' → appP δ ε ⇒ appP δ' ε
  plusR : ∀ {V} {P Q : Path V} → P ⇒ Q → plus P ⇒ plus Q
  minusR : ∀ {V} {P Q : Path V} → P ⇒ Q → minus P ⇒ minus Q
  βE : ∀ {V A M N P} {Q : Path V} → app* M N (λλλ A P) Q ⇒ P ⟦ x₂:= M ,x₁:= N ,x₀:= Q ⟧
  imp*l : ∀ {V} {P P' Q : Path V} → P ⇒ P' → P ⊃* Q ⇒ P' ⊃* Q
  imp*r : ∀ {V} {P Q Q' : Path V} → Q ⇒ Q' → P ⊃* Q ⇒ P ⊃* Q'
  app*l : ∀ {V} {M N : Term V} {P P' Q} → P ⇒ P' → app* M N P Q ⇒ app* M N P' Q

infix 10 _⇒?_
_⇒?_ : ∀ {V K} → VExpression V K → VExpression V K → Set
_⇒?_ = RClose _⇒_

--TODO Duplication below
⇒?-appTl : ∀ {V} {M M' N : Term V} → M ⇒? M' → appT M N ⇒? appT M' N
⇒?-appTl = respects-R' _ _⇒_ (λ _ _ → appTl) _ _

⇒?-impl : ∀ {V} {φ φ' ψ : Term V} → φ ⇒? φ' → φ ⊃ ψ ⇒? φ' ⊃ ψ
⇒?-impl = respects-R' _ _⇒_ (λ _ _ → impl) _ _

⇒?-impr : ∀ {V} {φ ψ ψ' : Term V} → ψ ⇒? ψ' → φ ⊃ ψ ⇒? φ ⊃ ψ'
⇒?-impr = respects-R' _ _⇒_ (λ _ _ → impr) _ _

⇒?-imp*l : ∀ {V} {P P' Q : Path V} → P ⇒? P' → P ⊃* Q ⇒? P' ⊃* Q
⇒?-imp*l = respects-R' _ _⇒_ (λ _ _ → imp*l) _ _

⇒?-imp*r : ∀ {V} {P Q Q' : Path V} → Q ⇒? Q' → P ⊃* Q ⇒? P ⊃* Q'
⇒?-imp*r = respects-R' _ _⇒_ (λ _ _ → imp*r) _ _

⇒?-app*l : ∀ {V} {M N : Term V} {P P' Q} → P ⇒? P' → app* M N P Q ⇒? app* M N P' Q
⇒?-app*l = respects-R' _ _⇒_ (λ _ _ → app*l) _ _

⇒?-appPl : ∀ {V} {δ δ' ε : Proof V} → δ ⇒? δ' → appP δ ε ⇒? appP δ' ε
⇒?-appPl = respects-R' _ _⇒_ (λ _ _ → appPl) _ _

⇒?-plus : ∀ {V} {P Q : Path V} → P ⇒? Q → plus P ⇒? plus Q
⇒?-plus {V} = respects-R {A = Bool} {B = λ b → VExpression V (if b then -Path else -Proof)} (λ _ → _⇒_ ) {true} {false} plus (λ x y → plusR) _ _

⇒?-minus : ∀ {V} {P Q : Path V} → P ⇒? Q → minus P ⇒? minus Q
⇒?-minus {V} = respects-R {A = Bool} {B = λ b → VExpression V (if b then -Path else -Proof)} (λ _ → _⇒_ ) {true} {false} minus (λ x y → minusR) _ _

⇒-resp-rep : ∀ {U V K} {E F : Expression U K} {ρ : Rep U V} → E ⇒ F → E 〈 ρ 〉 ⇒ F 〈 ρ 〉
⇒-resp-rep {ρ = ρ} (βT {V} {A} {M} {N}) = subst (λ x → (appT (ΛT A M) N 〈 ρ 〉) ⇒ x) 
  (≡-sym (compRS-botSub M))
  βT
⇒-resp-rep (appTl M⇒M') = appTl (⇒-resp-rep M⇒M')
⇒-resp-rep (impl φ⇒φ') = impl (⇒-resp-rep φ⇒φ')
⇒-resp-rep (impr ψ⇒ψ') = impr (⇒-resp-rep ψ⇒ψ')
⇒-resp-rep (appPl δ⇒δ') = appPl (⇒-resp-rep δ⇒δ')
⇒-resp-rep (plusR P⇒Q) = plusR (⇒-resp-rep P⇒Q)
⇒-resp-rep (minusR P⇒Q) = minusR (⇒-resp-rep P⇒Q)
⇒-resp-rep {ρ = ρ} (βE {V} {A} {M} {N} {P} {Q}) = subst (λ x → (app* M N (λλλ A P) Q 〈 ρ 〉) ⇒ x) (botSub₃-liftRep₃ P) βE
⇒-resp-rep (imp*l P⇒P') = imp*l (⇒-resp-rep P⇒P')
⇒-resp-rep (imp*r Q⇒Q') = imp*r (⇒-resp-rep Q⇒Q')
⇒-resp-rep (app*l P⇒P') = app*l (⇒-resp-rep P⇒P')

⇒-resp-ps : ∀ {U V} {M N : Term U} {τ : PathSub U V} {ρ σ} → M ⇒ N → M ⟦⟦ τ ∶ ρ ≡ σ ⟧⟧ ⇒ N ⟦⟦ τ ∶ ρ ≡ σ ⟧⟧
⇒-resp-ps {V = V} {τ = τ} {ρ} {σ} (βT {U} {A} {M} {N}) = 
  let μ : Sub (extend V pathDom) V
      μ = x₂:= N ⟦ ρ ⟧ ,x₁:= N ⟦ σ ⟧ ,x₀:= N ⟦⟦ τ ∶ ρ ≡ σ ⟧⟧ in
  subst (λ x → app* (N ⟦ ρ ⟧) (N ⟦ σ ⟧) (λλλ A (M ⟦⟦ liftPathSub τ ∶ sub↖ ρ ≡ sub↗ σ ⟧⟧))
    (N ⟦⟦ τ ∶ ρ ≡ σ ⟧⟧) ⇒ x) 
  (let open ≡-Reasoning in 
  begin
    M ⟦⟦ liftPathSub τ ∶ sub↖ ρ ≡ sub↗ σ ⟧⟧ ⟦ μ ⟧
  ≡⟨⟨ pathSub-•SP M ⟩⟩
    M ⟦⟦ μ •SP liftPathSub τ ∶ μ • sub↖ ρ ≡ μ • sub↗ σ ⟧⟧
  ≡⟨⟨ pathSub-cong M •SP-botSub sub↖-botSub sub↗-botSub ⟩⟩
    M ⟦⟦ τ ∶ ρ ≡ σ •PS (x₀:= N) ∶ ρ • (x₀:= N) ≡ σ • (x₀:= N) ⟧⟧
  ≡⟨ pathSub-•PS M ⟩
    (M ⟦ x₀:= N ⟧) ⟦⟦ τ ∶ ρ ≡ σ ⟧⟧
  ∎) 
  βE
⇒-resp-ps (appTl M⇒M') = app*l (⇒-resp-ps M⇒M')
⇒-resp-ps (impl φ⇒φ') = imp*l (⇒-resp-ps φ⇒φ')
⇒-resp-ps (impr ψ⇒ψ') = imp*r (⇒-resp-ps ψ⇒ψ')
