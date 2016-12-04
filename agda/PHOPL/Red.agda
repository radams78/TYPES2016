module PHOPL.Red where

open import Level
open import Data.Product
open import Prelims
open import PHOPL.Grammar
open import PHOPL.PathSub

data _⇒_ : ∀ {V K} → Expression V K → Expression V K → Set where
  βT : ∀ {V A M} {N : Term V} → appT (ΛT A M) N ⇒ M ⟦ x₀:= N ⟧
  βE : ∀ {V A M N P} {Q : Path V} → app* M N (λλλ A P) Q ⇒ P ⟦ x₂:= M ,x₁:= N ,x₀:= Q ⟧

diamond : ∀ {V K} {E F G : Expression V K} → E ⇒ F → E ⇒ G →
  Common-Reduct (RClose (_⇒_ {V})) (RClose _⇒_) F G
diamond βT βT = cr _ ref ref
diamond βE βE = cr _ ref ref

⇒-resp-rep : ∀ {U V K} {E F : Expression U K} {ρ : Rep U V} → E ⇒ F → E 〈 ρ 〉 ⇒ F 〈 ρ 〉
⇒-resp-rep {ρ = ρ} (βT {V} {A} {M} {N}) = subst (λ x → (appT (ΛT A M) N 〈 ρ 〉) ⇒ x) 
  (≡-sym (compRS-botSub M))
  βT
⇒-resp-rep {ρ = ρ} (βE {V} {A} {M} {N} {P} {Q}) = subst (λ x → (app* M N (λλλ A P) Q 〈 ρ 〉) ⇒ x) (botSub₃-liftRep₃ P) βE

sub↖-botSub : ∀ {U V} {σ : Sub U V} {M N P} → σ • (x₀:= M) ∼ (x₂:= M ⟦ σ ⟧ ,x₁:= N ,x₀:= P) • sub↖ σ
sub↖-botSub x₀ = refl
sub↖-botSub {σ = σ} {M} {N} {P} (↑ x) = ≡-sym botSub-upRep₃

sub↗-botSub : ∀ {U V} {σ : Sub U V} {M N P} → σ • (x₀:= M) ∼ (x₂:= N ,x₁:= M ⟦ σ ⟧ ,x₀:= P) • sub↗ σ
sub↗-botSub x₀ = refl
sub↗-botSub {σ = σ} {M} {N} {P} (↑ x) = ≡-sym botSub-upRep₃

⇒-resp-ps : ∀ {U V} {M N : Term U} {τ : PathSub U V} {ρ σ} → M ⇒ N → M ⟦⟦ τ ∶ ρ ∼ σ ⟧⟧ ⇒ N ⟦⟦ τ ∶ ρ ∼ σ ⟧⟧
⇒-resp-ps {V = V} {τ = τ} {ρ} {σ} (βT {U} {A} {M} {N}) = 
  let μ : Sub (extend V pathDom) V
      μ = x₂:= N ⟦ ρ ⟧ ,x₁:= N ⟦ σ ⟧ ,x₀:= N ⟦⟦ τ ∶ ρ ∼ σ ⟧⟧ in
  subst (λ x → app* (N ⟦ ρ ⟧) (N ⟦ σ ⟧) (λλλ A (M ⟦⟦ liftPathSub τ ∶ sub↖ ρ ∼ sub↗ σ ⟧⟧))
    (N ⟦⟦ τ ∶ ρ ∼ σ ⟧⟧) ⇒ x) 
  (let open ≡-Reasoning in 
  begin
    M ⟦⟦ liftPathSub τ ∶ sub↖ ρ ∼ sub↗ σ ⟧⟧ ⟦ μ ⟧
  ≡⟨⟨ pathSub-•SP M ⟩⟩
    M ⟦⟦ μ •SP liftPathSub τ ∶ μ • sub↖ ρ ∼ μ • sub↗ σ ⟧⟧
  ≡⟨⟨ pathSub-cong M •SP-botSub sub↖-botSub sub↗-botSub ⟩⟩
    M ⟦⟦ τ ∶ ρ ≡ σ •PS (x₀:= N) ∶ ρ • (x₀:= N) ∼ σ • (x₀:= N) ⟧⟧
  ≡⟨ {!!} ⟩
    (M ⟦ x₀:= N ⟧) ⟦⟦ τ ∶ ρ ∼ σ ⟧⟧
  ∎) 
  βE

_↠_ : ∀ {V K} → Expression V K → Expression V K → Set
_↠_ {V} {K} = RTClose (_⇒_ {V} {K})

↠-resp-rep : ∀ {U V K} {E F : Expression U K} {ρ : Rep U V} → E ↠ F → E 〈 ρ 〉 ↠ F 〈 ρ 〉
↠-resp-rep (inc E⇒F) = inc (⇒-resp-rep E⇒F)
↠-resp-rep ref = ref
↠-resp-rep (trans E↠F F↠G) = trans (↠-resp-rep E↠F) (↠-resp-rep F↠G)

_≃_ : ∀ {V K} → Expression V K → Expression V K → Set
_≃_ {V} {K} = RSTClose (_⇒_ {V} {K})

≃-resp-rep : ∀ {U V K} {E F : Expression U K} {ρ : Rep U V} → E ≃ F → E 〈 ρ 〉 ≃ F 〈 ρ 〉
≃-resp-rep {ρ = ρ} = respects-RST (λ V → _⇒_ {V}) (λ x → x 〈 ρ 〉) (λ _ _ → ⇒-resp-rep) _ _
