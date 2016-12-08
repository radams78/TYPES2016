module PHOPL.Red where

open import Level
open import Data.Product
open import Prelims
open import PHOPL.Grammar
open import PHOPL.PathSub

data _⇒_ : ∀ {V K} → Expression V K → Expression V K → Set where
  βT : ∀ {V A M} {N : Term V} → appT (ΛT A M) N ⇒ M ⟦ x₀:= N ⟧
  βE : ∀ {V A M N P} {Q : Path V} → app* M N (λλλ A P) Q ⇒ P ⟦ x₂:= M ,x₁:= N ,x₀:= Q ⟧
  impl : ∀ {V} {φ φ' ψ : Term V} → φ ⇒ φ' → φ ⊃ ψ ⇒ φ' ⊃ ψ
  impr : ∀ {V} {φ ψ ψ' : Term V} → ψ ⇒ ψ' → φ ⊃ ψ ⇒ φ ⊃ ψ'

⇒?-impl : ∀ {V} {φ φ' ψ : Term V} → RClose _⇒_ φ φ' → RClose _⇒_ (φ ⊃ ψ) (φ' ⊃ ψ)
⇒?-impl (inc φ⇒φ') = inc (impl φ⇒φ')
⇒?-impl ref = ref

⇒?-impr : ∀ {V} {φ ψ ψ' : Term V} → RClose _⇒_ ψ ψ' → RClose _⇒_ (φ ⊃ ψ) (φ ⊃ ψ')
⇒?-impr (inc ψ⇒ψ') = inc (impr ψ⇒ψ')
⇒?-impr ref = ref

diamond : ∀ {V K} {E F G : Expression V K} → E ⇒ F → E ⇒ G →
  Common-Reduct (RClose (_⇒_ {V})) (RClose _⇒_) F G
diamond βT βT = cr _ ref ref
diamond βE βE = cr _ ref ref
diamond (impl {ψ = ψ} φ⇒φ') (impl φ⇒φ'') = 
  let cr φ₀ φ'⇒?φ₀ φ''⇒?φ₀ = diamond φ⇒φ' φ⇒φ'' in 
  cr (φ₀ ⊃ ψ) (⇒?-impl φ'⇒?φ₀) (⇒?-impl φ''⇒?φ₀)
diamond (impl {φ' = φ'} φ⇒φ') (impr {ψ' = ψ'} ψ⇒ψ') = cr (φ' ⊃ ψ') (inc (impr ψ⇒ψ')) (inc (impl φ⇒φ'))
diamond (impr {ψ' = ψ'} ψ⇒ψ') (impl {φ' = φ'} φ⇒φ') = cr (φ' ⊃ ψ') (inc (impl φ⇒φ')) (inc (impr ψ⇒ψ'))
diamond (impr {φ = φ} ψ⇒ψ') (impr ψ⇒ψ'') = 
  let cr ψ₀ ψ'⇒?ψ₀ ψ''⇒?ψ₀ = diamond ψ⇒ψ' ψ⇒ψ'' in 
  cr (φ ⊃ ψ₀) (⇒?-impr ψ'⇒?ψ₀) (⇒?-impr ψ''⇒?ψ₀)

⇒-resp-rep : ∀ {U V K} {E F : Expression U K} {ρ : Rep U V} → E ⇒ F → E 〈 ρ 〉 ⇒ F 〈 ρ 〉
⇒-resp-rep {ρ = ρ} (βT {V} {A} {M} {N}) = subst (λ x → (appT (ΛT A M) N 〈 ρ 〉) ⇒ x) 
  (≡-sym (compRS-botSub M))
  βT
⇒-resp-rep {ρ = ρ} (βE {V} {A} {M} {N} {P} {Q}) = subst (λ x → (app* M N (λλλ A P) Q 〈 ρ 〉) ⇒ x) (botSub₃-liftRep₃ P) βE
⇒-resp-rep (impl φ⇒φ') = impl (⇒-resp-rep φ⇒φ')
⇒-resp-rep (impr ψ⇒ψ') = impr (⇒-resp-rep ψ⇒ψ')

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
⇒-resp-ps (impl φ⇒φ') = {!!}
⇒-resp-ps (impr ψ⇒ψ') = {!!}

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
