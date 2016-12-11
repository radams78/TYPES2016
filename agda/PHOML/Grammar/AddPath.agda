module PHOPL.Grammar.AddPath where
open import Data.Nat
open import Data.Empty renaming (⊥ to Empty)
open import Data.List hiding (replicate)
open import Data.Vec hiding (map;replicate)
open import Prelims
open import Grammar.Taxonomy
open import Grammar.Base
open import PHOPL.Grammar.Base
open import PHOPL.Grammar.Const

addpath : ∀ {V} → Context V → Type → Context (extend V pathDom)
addpath Γ A = Γ ,T A ,T A ,E var x₁ ≡〈 A 〉 var x₀

sub↖ : ∀ {U} {V} → Sub U V → Sub (U , -Term) (extend V pathDom)
sub↖ σ _ x₀ = var x₂
sub↖ σ _ (↑ x) = σ _ x ⇑ ⇑ ⇑

postulate sub↖-cong : ∀ {U} {V} {ρ σ : Sub U V} → ρ ∼ σ → sub↖ ρ ∼ sub↖ σ

postulate sub↖-•RS : ∀ {U} {V} {W} {ρ : Rep V W} {σ : Sub U V} →
                  sub↖ (ρ •RS σ) ∼ liftRep -Path (liftRep -Term (liftRep -Term ρ)) •RS sub↖ σ

sub↖-comp : ∀ {U V W} {σ : Sub V W} {ρ : Sub U V} → sub↖ (σ • ρ) ∼ liftsSub pathDom σ • sub↖ ρ
sub↖-comp x₀ = refl
sub↖-comp {σ = σ} {ρ} (↑ x) = ≡-sym (liftSub-upRep₃ (ρ _ x))

sub↗ : ∀ {U} {V} → Sub U V → Sub (U , -Term) (V , -Term , -Term , -Path)
sub↗ σ _ x₀ = var x₁
sub↗ σ _ (↑ x) = σ _ x ⇑ ⇑ ⇑

postulate sub↗-cong : ∀ {U} {V} {ρ σ : Sub U V} → ρ ∼ σ → sub↗ ρ ∼ sub↗ σ

sub↗-•RS : ∀ {U} {V} {W} {ρ : Rep V W} {σ : Sub U V} →
  sub↗ (ρ •RS σ) ∼ liftRep -Path (liftRep -Term (liftRep -Term ρ)) •RS sub↗ σ
sub↗-•RS x₀ = refl
sub↗-•RS {ρ = ρ} {σ} (↑ x) = let open ≡-Reasoning in 
  begin
    σ _ x 〈 ρ 〉 ⇑ ⇑ ⇑
  ≡⟨⟨ liftRep-upRep₃ (σ _ x) ⟩⟩
    σ _ x ⇑ ⇑ ⇑ 〈 liftsRep pathDom ρ 〉
  ∎

sub↗-comp : ∀ {U V W} {σ : Sub V W} {ρ : Sub U V} → sub↗ (σ • ρ) ∼ liftsSub pathDom σ • sub↗ ρ
sub↗-comp x₀ = refl
sub↗-comp {σ = σ} {ρ} (↑ x) = ≡-sym (liftSub-upRep₃ (ρ _ x))

--REFACTOR Duplication

toSnocTypes : ∀ {V n} → snocVec Type n → snocTypes V (replicate n -Term)
toSnocTypes [] = []
toSnocTypes (AA snoc A) = toSnocTypes AA snoc ty A

toSnocTypes-rep : ∀ {U V n} {AA : snocVec Type n} {ρ : Rep U V} → snocTypes-rep (toSnocTypes AA) ρ ≡ toSnocTypes AA
toSnocTypes-rep {AA = []} = refl
toSnocTypes-rep {AA = AA snoc A} = cong (λ x → x snoc ty A) toSnocTypes-rep

eqmult : ∀ {V n} → snocVec (Term V) n → snocVec Type n → snocVec (Term V) n → snocTypes V (Prelims.replicate n -Path)
eqmult [] [] [] = []
eqmult {n = suc n} (MM snoc M) (AA snoc A) (NN snoc N) = eqmult MM AA NN snoc (_⇑⇑ {KK = replicate n -Path} M) ≡〈 A 〉 (_⇑⇑ {KK = replicate n -Path} N)

eqmult-rep : ∀ {U V n} {MM : snocVec (Term U) n} {AA NN} {ρ : Rep U V} →
  snocTypes-rep (eqmult MM AA NN) ρ ≡ eqmult (snocVec-rep MM ρ) AA (snocVec-rep NN ρ)
eqmult-rep {MM = []} {[]} {[]} = refl
eqmult-rep {n = suc n} {MM = MM snoc M} {AA snoc A} {NN snoc N} = cong₃ (λ a b c → a snoc b ≡〈 A 〉 c) 
  eqmult-rep 
  (liftsnocRep-ups (Prelims.replicate n -Path) M) (liftsnocRep-ups (Prelims.replicate n -Path) N)

toSnocListExp : ∀ {V K n} → snocVec (Expression V (varKind K)) n → HetsnocList (VExpression V) (replicate n K)
toSnocListExp [] = []
toSnocListExp (MM snoc M) = toSnocListExp MM snoc M

toSnocListExp-rep : ∀ {U V K n} {MM : snocVec (Expression U (varKind K)) n} {ρ : Rep U V} →
  snocListExp-rep (toSnocListExp MM) ρ ≡ toSnocListExp (snocVec-rep MM ρ)
toSnocListExp-rep {MM = []} = refl
toSnocListExp-rep {MM = MM snoc M} {ρ} = cong (λ x → x snoc M 〈 ρ 〉) toSnocListExp-rep

data not-app V : Set where
  navar : Var V -Term → not-app V
  na⊥   : not-app V
  na⊃   : Term V → Term V → not-app V
  naΛ   : Type → Term (V , -Term) → not-app V

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
