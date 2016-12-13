module PHOML.Grammar.AddPath where
open import Data.Nat
open import Prelims
open import PHOML.Grammar.Base
open import PHOML.Grammar.Const

addpath : ∀ {V} → Context V → Type → Context (extend V pathDom)
addpath Γ A = Γ ,T A ,T A ,E var x₁ ≡〈 A 〉 var x₀

sub↖ : ∀ {U} {V} → Sub U V → Sub (U , -Term) (extend V pathDom)
sub↖ σ _ x₀ = var x₂
sub↖ σ _ (↑ x) = σ _ x ⇑ ⇑ ⇑

sub↖-cong : ∀ {U} {V} {ρ σ : Sub U V} → ρ ∼ σ → sub↖ ρ ∼ sub↖ σ
sub↖-cong ρ∼σ x₀ = refl
sub↖-cong ρ∼σ (↑ x) = rep-congl (rep-congl (rep-congl (ρ∼σ x))) -- TODO Build as setoid function

sub↖-•RS : ∀ {U} {V} {W} {ρ : Rep V W} {σ : Sub U V} →
  sub↖ (ρ •RS σ) ∼ liftRep -Path (liftRep -Term (liftRep -Term ρ)) •RS sub↖ σ
sub↖-•RS x₀ = refl
sub↖-•RS {σ = σ} (↑ x) = ≡-sym (liftRep-upRep₃ (σ _ x))

sub↖-comp : ∀ {U V W} {σ : Sub V W} {ρ : Sub U V} → sub↖ (σ • ρ) ∼ liftsSub pathDom σ • sub↖ ρ
sub↖-comp x₀ = refl
sub↖-comp {σ = σ} {ρ} (↑ x) = ≡-sym (liftSub-upRep₃ (ρ _ x))

sub↗ : ∀ {U} {V} → Sub U V → Sub (U , -Term) (V , -Term , -Term , -Path)
sub↗ σ _ x₀ = var x₁
sub↗ σ _ (↑ x) = σ _ x ⇑ ⇑ ⇑

sub↗-cong : ∀ {U} {V} {ρ σ : Sub U V} → ρ ∼ σ → sub↗ ρ ∼ sub↗ σ
sub↗-cong ρ∼σ x₀ = refl
sub↗-cong ρ∼σ (↑ x) = rep-congl (rep-congl (rep-congl (ρ∼σ x))) -- TODO Build as setoid function

sub↗-•RS : ∀ {U} {V} {W} {ρ : Rep V W} {σ : Sub U V} →
  sub↗ (ρ •RS σ) ∼ liftRep -Path (liftRep -Term (liftRep -Term ρ)) •RS sub↗ σ
sub↗-•RS x₀ = refl
sub↗-•RS {σ = σ} (↑ x) = ≡-sym (liftRep-upRep₃ (σ _ x))

sub↗-comp : ∀ {U V W} {σ : Sub V W} {ρ : Sub U V} → sub↗ (σ • ρ) ∼ liftsSub pathDom σ • sub↗ ρ
sub↗-comp x₀ = refl
sub↗-comp {σ = σ} {ρ} (↑ x) = ≡-sym (liftSub-upRep₃ (ρ _ x))

--REFACTOR Duplication

sub↖-•SR : ∀ {U V W} {σ : Sub V W} {ρ : Rep U V} → sub↖ (σ •SR ρ) ∼ sub↖ σ •SR liftRep _ ρ
sub↖-•SR x₀ = refl
sub↖-•SR (↑ x) = refl

sub↗-•SR : ∀ {U V W} {σ : Sub V W} {ρ : Rep U V} → sub↗ (σ •SR ρ) ∼ sub↗ σ •SR liftRep _ ρ
sub↗-•SR x₀ = refl
sub↗-•SR (↑ x) = refl

sub↖-• : ∀ {U V W} {σ : Sub V W} {ρ : Sub U V} → sub↖ (σ • ρ) ∼ sub↖ σ • liftSub _ ρ
sub↖-• x₀ = refl
sub↖-• {σ = σ} {ρ} (↑ x) = let open ≡-Reasoning in 
  begin
    ρ _ x ⟦ σ ⟧ ⇑ ⇑ ⇑
  ≡⟨⟨ rep-congl (rep-congl (sub-•RS (ρ _ x))) ⟩⟩
    ρ _ x ⟦ upRep •RS σ ⟧ ⇑ ⇑
  ≡⟨⟨ rep-congl (sub-•RS (ρ _ x)) ⟩⟩
    ρ _ x ⟦ upRep •RS (upRep •RS σ) ⟧ ⇑
  ≡⟨⟨ sub-•RS (ρ _ x) ⟩⟩
    ρ _ x ⟦ upRep •RS (upRep •RS (upRep •RS σ)) ⟧
  ≡⟨⟩
    ρ _ x ⟦ sub↖ σ •SR upRep ⟧
  ≡⟨ sub-•SR (ρ _ x) ⟩
    ρ _ x ⇑ ⟦ sub↖ σ ⟧
  ∎

sub↗-• : ∀ {U V W} {σ : Sub V W} {ρ : Sub U V} → sub↗ (σ • ρ) ∼ sub↗ σ • liftSub _ ρ
sub↗-• x₀ = refl
sub↗-• {σ = σ} {ρ} (↑ x) = let open ≡-Reasoning in 
  begin
    ρ _ x ⟦ σ ⟧ ⇑ ⇑ ⇑
  ≡⟨⟨ rep-congl (rep-congl (sub-•RS (ρ _ x))) ⟩⟩
    ρ _ x ⟦ upRep •RS σ ⟧ ⇑ ⇑
  ≡⟨⟨ rep-congl (sub-•RS (ρ _ x)) ⟩⟩
    ρ _ x ⟦ upRep •RS (upRep •RS σ) ⟧ ⇑
  ≡⟨⟨ sub-•RS (ρ _ x) ⟩⟩
    ρ _ x ⟦ upRep •RS (upRep •RS (upRep •RS σ)) ⟧
  ≡⟨⟩
    ρ _ x ⟦ sub↗ σ •SR upRep ⟧
  ≡⟨ sub-•SR (ρ _ x) ⟩
    ρ _ x ⇑ ⟦ sub↗ σ ⟧
  ∎

sub↖-botSub : ∀ {U V} {σ : Sub U V} {M N P} → σ • (x₀:= M) ∼ (x₂:= M ⟦ σ ⟧ ,x₁:= N ,x₀:= P) • sub↖ σ
sub↖-botSub x₀ = refl
sub↖-botSub {σ = σ} {M} {N} {P} (↑ x) = ≡-sym botSub-upRep₃

sub↗-botSub : ∀ {U V} {σ : Sub U V} {M N P} → σ • (x₀:= M) ∼ (x₂:= N ,x₁:= M ⟦ σ ⟧ ,x₀:= P) • sub↗ σ
sub↗-botSub x₀ = refl
sub↗-botSub {σ = σ} {M} {N} {P} (↑ x) = ≡-sym botSub-upRep₃

liftsRep-sub↖id : ∀ {U V} {ρ : Rep U V} → liftsRep pathDom ρ •RS sub↖ (idSub U) ∼ sub↖ (idSub V) •SR liftRep -Term ρ
liftsRep-sub↖id x₀ = refl
liftsRep-sub↖id (↑ _) = refl

liftsRep-sub↗id : ∀ {U V} {ρ : Rep U V} → liftsRep pathDom ρ •RS sub↗ (idSub U) ∼ sub↗ (idSub V) •SR liftRep -Term ρ
liftsRep-sub↗id x₀ = refl
liftsRep-sub↗id (↑ _) = refl

liftsRep-sub↖ : ∀ {U V W} {ρ : Rep V W} {σ : Sub U V} →
  liftsRep pathDom ρ •RS sub↖ σ ∼ sub↖ (ρ •RS σ)
liftsRep-sub↖ x₀ = refl
liftsRep-sub↖ {σ = σ} (↑ x) = liftRep-upRep₃ (σ _ x)

liftsRep-sub↗ : ∀ {U V W} {ρ : Rep V W} {σ : Sub U V} →
  liftsRep pathDom ρ •RS sub↗ σ ∼ sub↗ (ρ •RS σ)
liftsRep-sub↗ x₀ = refl
liftsRep-sub↗ {σ = σ} (↑ x) = liftRep-upRep₃ (σ _ x)

botSub₃-sub↖ : ∀ {U V} {M N : Term V} {P} {σ : Sub U V} →
  (x₂:= M ,x₁:= N ,x₀:= P) • sub↖ σ ∼ extendSub σ M
botSub₃-sub↖ x₀ = refl
botSub₃-sub↖ (↑ x) = botSub-upRep₃

botSub₃-sub↗ : ∀ {U V} {M N : Term V} {P} {σ : Sub U V} →
  (x₂:= M ,x₁:= N ,x₀:= P) • sub↗ σ ∼ extendSub σ N
botSub₃-sub↗ x₀ = refl
botSub₃-sub↗ (↑ x) = botSub-upRep₃
