open import Grammar.Base

module Grammar.Substitution.OpFamily (G : Grammar) where
open import Prelims
open Grammar G
open import Grammar.OpFamily G
open import Grammar.Replacement G
open import Grammar.Substitution.PreOpFamily G
open import Grammar.Substitution.Lifting G
open import Grammar.Substitution.LiftFamily G
open import Grammar.Substitution.RepSub G

infixl 60 _•RS_
_•RS_ : ∀ {U} {V} {W} → Rep V W → Sub U V → Sub U W
(ρ •RS σ) K x = (σ K x) 〈 ρ 〉

liftSub-compRS' : ∀ {U} {V} {W} {K} {ρ : Rep V W} {σ : Sub U V} → liftSub K (ρ •RS σ) ∼ liftRep K ρ •RS liftSub K σ
liftSub-compRS' {K = K} x₀ = refl
liftSub-compRS' {U} {V} {W} {K} {ρ} {σ} {L} (↑ x) = let open ≡-Reasoning {A = Expression (W , K) (varKind L)} in 
  begin 
    (σ L x) 〈 ρ 〉 〈 upRep 〉
  ≡⟨⟨ rep-comp (σ L x) ⟩⟩
    (σ L x) 〈 upRep •R ρ 〉
  ≡⟨⟩
    (σ L x) 〈 liftRep K ρ •R upRep 〉
  ≡⟨ rep-comp (σ L x) ⟩
    (σ L x) 〈 upRep 〉 〈 liftRep K ρ 〉
  ∎

--TODO Version of composition that takes OpFamilies
COMPRS : Composition Rep∶LF SubLF SubLF
COMPRS = record { 
  _∘_ = _•RS_ ; 
  liftOp-comp' = liftSub-compRS' ; 
  apV-comp = refl }

sub-•RS : ∀ {U} {V} {W} {C} {K} 
  (E : Subexp U C K) {ρ : Rep V W} {σ : Sub U V} →
  E ⟦ ρ •RS σ ⟧ ≡ E ⟦ σ ⟧ 〈 ρ 〉
sub-•RS E = Composition.ap-comp COMPRS E

infixl 60 _•SR_
_•SR_ : ∀ {U} {V} {W} → Sub V W → Rep U V → Sub U W
(σ •SR ρ) K x = σ K (ρ K x)

liftSub-compSR : ∀ {U} {V} {W} {K} {σ : Sub V W} {ρ : Rep U V} → 
  liftSub K (σ •SR ρ) ∼ liftSub K σ •SR liftRep K ρ
liftSub-compSR {K = K} x₀ = refl
liftSub-compSR (↑ x) = refl

COMPSR : Composition SubLF Rep∶LF SubLF
COMPSR = record { 
  _∘_ = _•SR_ ; 
  liftOp-comp' = liftSub-compSR ; 
  apV-comp = refl }

sub-•SR : ∀ {U} {V} {W} {C} {K} 
  (E : Subexp U C K) {σ : Sub V W} {ρ : Rep U V} → 
  E ⟦ σ •SR ρ ⟧ ≡ E 〈 ρ 〉 ⟦ σ ⟧
sub-•SR E = Composition.ap-comp COMPSR E

liftSub-upRep : ∀ {U} {V} {C} {K} {L} (E : Subexp U C K) {σ : Sub U V} →
  E 〈 upRep 〉 ⟦ liftSub L σ ⟧ ≡ E ⟦ σ ⟧ 〈 upRep 〉
liftSub-upRep E = liftOp-up-mixed COMPSR COMPRS (λ {_} {_} {_} {_} {E} → ≡-sym (up-is-up' {E = E})) {E}

infixl 60 _•_
_•_ : ∀ {U} {V} {W} → Sub V W → Sub U V → Sub U W
(σ • ρ) K x = ρ K x ⟦ σ ⟧

liftSub-comp : ∀ {U} {V} {W} {ρ : Sub U V} {σ : Sub V W} {K} → 
  liftSub K (σ • ρ) ∼ liftSub K σ • liftSub K ρ
liftSub-comp x₀ = refl
liftSub-comp {W = W} {ρ = ρ} {σ = σ} {K = K} {L} (↑ x) = ≡-sym (liftSub-upRep (ρ L x))

liftSub-upRep₂ : ∀ {U} {V} {C} {K} {L} {M} (E : Subexp U C M) {σ : Sub U V} → E ⇑ ⇑ ⟦ liftSub K (liftSub L σ) ⟧ ≡ E ⟦ σ ⟧ ⇑ ⇑
liftSub-upRep₂ {U} {V} {C} {K} {L} {M} E {σ} = let open ≡-Reasoning in 
  begin
    E ⇑ ⇑ ⟦ liftSub K (liftSub L σ) ⟧
  ≡⟨ liftSub-upRep (E ⇑) ⟩
    E ⇑ ⟦ liftSub L σ ⟧ ⇑
  ≡⟨ rep-congl (liftSub-upRep E) ⟩
    E ⟦ σ ⟧ ⇑ ⇑
  ∎

liftSub-upRep₃ : ∀ {U} {V} {C} {K} {L} {M} {N} (E : Subexp U C N) {σ : Sub U V} → E ⇑ ⇑ ⇑ ⟦ liftSub K (liftSub L (liftSub M σ)) ⟧ ≡ E ⟦ σ ⟧ ⇑ ⇑ ⇑
liftSub-upRep₃ {U} {V} {C} {K} {L} {M} {N} E {σ} = let open ≡-Reasoning in 
  begin
    E ⇑ ⇑ ⇑ ⟦ liftSub K (liftSub L (liftSub M σ)) ⟧
  ≡⟨ liftSub-upRep₂ (E ⇑) ⟩
    E ⇑ ⟦ liftSub M σ ⟧ ⇑ ⇑
  ≡⟨ rep-congl (rep-congl (liftSub-upRep E)) ⟩
    E ⟦ σ ⟧ ⇑ ⇑ ⇑
  ∎

liftRep-liftSub-upRep₃ : ∀ {U} {V} {W} {K1} {K2} {K3} {C} {K4} 
                   (M : Subexp U C K4)
                   (σ : Sub U V) (ρ : Rep V W) →
                    M ⇑ ⇑ ⇑ ⟦ liftSub K1 (liftSub K2 (liftSub K3 σ)) ⟧ 〈 liftRep K1 (liftRep K2 (liftRep K3 ρ)) 〉
                    ≡ M ⟦ σ ⟧ 〈 ρ 〉 ⇑ ⇑ ⇑
liftRep-liftSub-upRep₃ M σ ρ = ≡-trans (rep-congl (liftSub-upRep₃ M {σ})) (liftRep-upRep₃ (M ⟦ σ ⟧))

assocRSSR : ∀ {U} {V} {W} {X} {ρ : Sub W X} {σ : Rep V W} {τ : Sub U V} →
            ρ • (σ •RS τ) ∼ (ρ •SR σ) • τ
assocRSSR {ρ = ρ} {σ} {τ} x = ≡-sym (sub-•SR (τ _ x))

SUB : OpFamily
SUB = record { 
  liftFamily = SubLF;
  comp = record { 
    _∘_ = _•_ ; 
    liftOp-comp' = liftSub-comp ; 
    apV-comp = refl }
  }

open OpFamily SUB using (comp-congl;comp-congr)
  renaming (liftOp-idOp to liftSub-idOp;
           ap-idOp to sub-idSub;
           ap-congr to sub-congl;
           unitl to sub-unitl;
           unitr to sub-unitr;
           ∼-sym to sub-sym;
           ∼-trans to sub-trans;
           assoc to sub-assoc)
  public

sub-congr : ∀ {U V C K} {ρ σ : Sub U V} (E : Subexp U C K) → ρ ∼ σ → E ⟦ ρ ⟧ ≡ E ⟦ σ ⟧
sub-congr E ρ∼σ = OpFamily.ap-congl SUB ρ∼σ E

liftSub-compRS : ∀ {U V W K C L} {ρ : Rep V W} {σ : Sub U V} (M : Subexp (U , K) C L) → M ⟦ liftSub K (ρ •RS σ) ⟧ ≡ M ⟦ liftSub K σ ⟧ 〈 liftRep K ρ 〉
liftSub-compRS M = Composition.liftOp-comp COMPRS {M = M}

sub-comp : ∀ {U} {V} {W} {C} {K}
  (E : Subexp U C K) {σ : Sub V W} {ρ : Sub U V} →
  E ⟦ σ • ρ ⟧ ≡ E ⟦ ρ ⟧ ⟦ σ ⟧
sub-comp = OpFamily.ap-comp SUB

liftsSub : ∀ {U V} AA → Sub U V → Sub (extend U AA) (extend V AA)
liftsSub = OpFamily.liftsOp SUB
