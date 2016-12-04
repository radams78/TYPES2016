open import Grammar.Base
  
module Grammar.Substitution.Botsub (G : Grammar) where
open import Prelims
open Grammar G
open import Grammar.OpFamily G
open import Grammar.Replacement G
open import Grammar.Substitution.PreOpFamily G
open import Grammar.Substitution.Lifting G
open import Grammar.Substitution.LiftFamily G
open import Grammar.Substitution.OpFamily G

botSub : ∀ {V} {AA} → HetsnocList (VExpression V) AA → Sub (snoc-extend V AA) V
botSub {AA = []} _ _ x = var x
botSub {AA = _ snoc _} (_ snoc E) _ x₀ = E
botSub {AA = _ snoc _} (EE snoc _) L (↑ x) = botSub EE L x

infix 65 x₀:=_
x₀:=_ : ∀ {V} {K} → Expression V (varKind K) → Sub (V , K) V
x₀:= E = botSub ([] snoc E)

infix 65 xx₀:=_
xx₀:=_ : ∀ {V KK} → HetsnocList (VExpression V) KK → Sub (snoc-extend V KK) V
xx₀:=_ = botSub -- TODO Inline

liftsnocRep-botSub' : ∀ {U V} KK {MM : HetsnocList (VExpression U) KK} {ρ : Rep U V} → ρ •RS xx₀:= MM ∼ xx₀:= snocListExp-rep MM ρ •SR liftsnocRep KK ρ
liftsnocRep-botSub' [] _ = refl
liftsnocRep-botSub' (_ snoc _) {_ snoc _} x₀ = refl
liftsnocRep-botSub' (KK snoc _) {_ snoc _} (↑ x) = liftsnocRep-botSub' KK x

liftsnocRep-botSub : ∀ {U V KK} {MM : HetsnocList (VExpression U) KK} {ρ : Rep U V} {C K} {E : Subexp (snoc-extend U KK) C K} → E ⟦ xx₀:= MM ⟧ 〈 ρ 〉 ≡ E 〈 liftsnocRep KK ρ 〉 ⟦ xx₀:= snocListExp-rep MM ρ ⟧
liftsnocRep-botSub {KK = KK} {MM = MM} {ρ = ρ} {E = E} = let open ≡-Reasoning in
  begin
    E ⟦ xx₀:= MM ⟧ 〈 ρ 〉
  ≡⟨⟨ sub-•RS E ⟩⟩
    E ⟦ ρ •RS xx₀:= MM ⟧
  ≡⟨ sub-congr E (liftsnocRep-botSub' KK) ⟩
    E ⟦ xx₀:= snocListExp-rep MM ρ •SR liftsnocRep KK ρ ⟧
  ≡⟨ sub-•SR E ⟩
    E 〈 liftsnocRep KK ρ 〉 ⟦ xx₀:= snocListExp-rep MM ρ ⟧
  ∎

botSub-ups' : ∀ {V} KK {MM : HetsnocList (VExpression V) KK} → xx₀:= MM •SR ups KK ∼ idSub V
botSub-ups' [] _ = refl
botSub-ups' (KK snoc _) {_ snoc _} x = botSub-ups' KK x

botSub-ups : ∀ {V} KK {C K} {MM : HetsnocList (VExpression V) KK} {E : Subexp V C K} → E 〈 ups KK 〉 ⟦ xx₀:= MM ⟧ ≡ E
botSub-ups {V} KK {MM = MM} {E} = let open ≡-Reasoning in 
  begin
    E 〈 ups KK 〉 ⟦ xx₀:= MM ⟧
  ≡⟨⟨ sub-•SR E ⟩⟩
    E ⟦ xx₀:= MM •SR ups KK ⟧
  ≡⟨ sub-congr E (botSub-ups' KK) ⟩
    E ⟦ idSub V ⟧
  ≡⟨ sub-idSub ⟩
    E
  ∎

open LiftFamily

botSub-up' : ∀ {F} {V} {K} {E : Expression V (varKind K)} (comp : Composition SubLF F SubLF) →
  Composition._∘_ comp (x₀:= E) (up F) ∼ idSub V
botSub-up' {F} {V} {K} {E} comp x = let open ≡-Reasoning in 
  begin
    (Composition._∘_ comp (x₀:= E) (up F)) _ x
  ≡⟨ Composition.apV-comp comp ⟩
    apV F (up F) x ⟦ x₀:= E ⟧
  ≡⟨ sub-congl (apV-up F) ⟩
    var x
  ∎

botSub-up : ∀ {F} {V} {K} {C} {L} {E : Expression V (varKind K)} (comp : Composition SubLF F SubLF) {E' : Subexp V C L} →
  ap F (up F) E' ⟦ x₀:= E ⟧ ≡ E'
botSub-up {F} {V} {K} {C} {L} {E} comp {E'} = let open ≡-Reasoning in
  begin
    ap F (up F) E' ⟦ x₀:= E ⟧
  ≡⟨⟨ Composition.ap-comp comp E' ⟩⟩
    E' ⟦ Composition._∘_ comp (x₀:= E) (up F) ⟧
  ≡⟨ sub-congr E' (botSub-up' comp)⟩
    E' ⟦ idSub V ⟧
  ≡⟨ sub-idSub ⟩
    E'
  ∎

comp-botSub' : ∀ {F} {U} {V} {K} {E : Expression U (varKind K)} 
  (comp₁ : Composition F SubLF SubLF) 
  (comp₂ : Composition SubLF F SubLF)
  {σ : Op F U V} →
  Composition._∘_ comp₁ σ (x₀:= E) ∼ Composition._∘_ comp₂ (x₀:= (ap F σ E)) (liftOp F K σ)
comp-botSub' {F} {U} {V} {K} {E} comp₁ comp₂ {σ} x₀ = let open ≡-Reasoning in 
  begin
    (Composition._∘_ comp₁ σ (x₀:= E)) _ x₀
  ≡⟨ Composition.apV-comp comp₁ ⟩
    ap F σ E
  ≡⟨⟨ sub-congl (liftOp-x₀ F) ⟩⟩
    (apV F (liftOp F K σ) x₀) ⟦ x₀:= (ap F σ E) ⟧
  ≡⟨⟨ Composition.apV-comp comp₂ ⟩⟩
    (Composition._∘_ comp₂ (x₀:= (ap F σ E)) (liftOp F K σ)) _ x₀
  ∎
comp-botSub' {F} {U} {V} {K} {E} comp₁ comp₂ {σ} (↑ x) = let open ≡-Reasoning in 
  begin
    (Composition._∘_ comp₁ σ (x₀:= E)) _ (↑ x)
  ≡⟨ Composition.apV-comp comp₁ ⟩
    apV F σ x
  ≡⟨⟨ sub-idSub ⟩⟩
    apV F σ x ⟦ idSub V ⟧
  ≡⟨⟨ sub-congr (apV F σ x) (botSub-up' comp₂) ⟩⟩
    apV F σ x ⟦ Composition._∘_ comp₂ (x₀:= (ap F σ E)) (up F) ⟧
  ≡⟨ Composition.ap-comp comp₂ (apV F σ x) ⟩
    ap F (up F) (apV F σ x) ⟦ x₀:= (ap F σ E) ⟧
  ≡⟨⟨ sub-congl (liftOp-↑ F x) ⟩⟩
    (apV F (liftOp F K σ) (↑ x)) ⟦ x₀:= (ap F σ E) ⟧
  ≡⟨⟨ Composition.apV-comp comp₂ ⟩⟩
    (Composition._∘_ comp₂ (x₀:= (ap F σ E)) (liftOp F K σ)) _ (↑ x)
  ∎

comp-botSub : ∀ {F} {U} {V} {K} {C} {L} 
  {E : Expression U (varKind K)} {E' : Subexp (U , K) C L} {σ : Op F U V} →
  Composition F SubLF SubLF →
  Composition SubLF F SubLF →
  ap F σ (E' ⟦ x₀:= E ⟧) ≡ (ap F (liftOp F K σ) E') ⟦ x₀:= (ap F σ E) ⟧
comp-botSub {E' = E'} comp₁ comp₂ = ap-comp-sim comp₁ comp₂ (comp-botSub' comp₁ comp₂) E'

compRS-botSub : ∀ {U} {V} {C} {K} {L} (E : Subexp (U , K) C L) {F : Expression U (varKind K)} {ρ : Rep U V} →
  E ⟦ x₀:= F ⟧ 〈 ρ 〉 ≡ E 〈 liftRep K ρ 〉 ⟦ x₀:= (F 〈 ρ 〉) ⟧
--TODO Common pattern with liftRep-botSub₃
compRS-botSub E = comp-botSub {E' = E} COMPRS COMPSR

comp-botSub'' : ∀ {U} {V} {C} {K} {L} 
  {E : Expression U (varKind K)} {σ : Sub U V} (F : Subexp (U , K) C L) →
   F ⟦ x₀:= E ⟧ ⟦ σ ⟧ ≡ F ⟦ liftSub K σ ⟧ ⟦ x₀:= (E ⟦ σ ⟧) ⟧
--TODO Better name
comp-botSub'' F = let COMP = OpFamily.comp SUB in comp-botSub {E' = F} COMP COMP

botSub-upRep : ∀ {U} {C} {K} {L}
  (E : Subexp U C K) {F : Expression U (varKind L)} → 
  E 〈 upRep 〉 ⟦ x₀:= F ⟧ ≡ E
botSub-upRep _ = botSub-up COMPSR

botSub-botSub' : ∀ {V} {K} {L} (N : Expression V (varKind K)) (N' : Expression V (varKind L)) → x₀:= N' • liftSub L (x₀:= N) ∼ x₀:= N • x₀:= (N' ⇑)
botSub-botSub' N N' x₀ = ≡-sym (botSub-upRep N')
botSub-botSub' N N' (↑ x₀) = botSub-upRep N
botSub-botSub' N N' (↑ (↑ x)) = refl

botSub-botSub : ∀ {V} {K} {L} {M} (E : Expression (V , K , L) M) F G → E ⟦ liftSub L (x₀:= F) ⟧ ⟦ x₀:= G ⟧ ≡ E ⟦ x₀:= (G ⇑) ⟧ ⟦ x₀:= F ⟧
botSub-botSub {V} {K} {L} {M} E F G = let COMP = OpFamily.comp SUB in ap-comp-sim COMP COMP (botSub-botSub' F G) E -- TODO Duplication with comp-botSub'' ?

x₂:=_,x₁:=_,x₀:=_ : ∀ {V} {K1} {K2} {K3} → Expression V (varKind K1) → Expression V (varKind K2) → Expression V (varKind K3) → Sub (V , K1 , K2 , K3) V
x₂:=_,x₁:=_,x₀:=_ M1 M2 M3 = botSub ([] snoc M1 snoc M2 snoc M3)

botSub₃-upRep₃' : ∀ {V K₁ K₂ K₃ L} {M : Expression V L} {N₁ : VExpression V K₁} {N₂ : VExpression V K₂} {N₃ : VExpression V K₃} →
  (x₂:= N₁ ,x₁:= N₂ ,x₀:= N₃) •SR upRep •SR upRep  •SR upRep ∼ idSub V
botSub₃-upRep₃' x₀ = refl
botSub₃-upRep₃' (↑ x₀) = refl
botSub₃-upRep₃' (↑ (↑ x₀)) = refl
botSub₃-upRep₃' (↑ (↑ (↑ _))) = refl

postulate botSub-upRep₃ : ∀ {V} {K1} {K2} {K3} {L} {M : Expression V L} 
                          {N1 : Expression V (varKind K1)} {N2 : Expression V (varKind K2)} {N3 : Expression V (varKind K3)} →
                          M ⇑ ⇑ ⇑ ⟦ x₂:= N1 ,x₁:= N2 ,x₀:= N3 ⟧ ≡ M

--TODO Definition for Expression varKind*
botSub₃-liftRep₃' : ∀ {U} {V} {K2} {K1} {K0}
  {M2 : Expression U (varKind K1)} {M1 : Expression U (varKind K2)} {M0 : Expression U (varKind K0)} {ρ : Rep U V} →
  (x₂:= M2 〈 ρ 〉 ,x₁:= M1 〈 ρ 〉 ,x₀:= M0 〈 ρ 〉) •SR liftRep _ (liftRep _ (liftRep _ ρ))
  ∼ ρ •RS (x₂:= M2 ,x₁:= M1 ,x₀:= M0)
botSub₃-liftRep₃' x₀ = refl
botSub₃-liftRep₃' (↑ x₀) = refl
botSub₃-liftRep₃' (↑ (↑ x₀)) = refl 
botSub₃-liftRep₃' (↑ (↑ (↑ x))) = refl

botSub₃-liftRep₃ : ∀ {U} {V} {K2} {K1} {K0} {L}
  {M2 : Expression U (varKind K2)} {M1 : Expression U (varKind K1)} {M0 : Expression U (varKind K0)} {ρ : Rep U V} (N : Expression (U , K2 , K1 , K0) L) →
  N 〈 liftRep _ (liftRep _ (liftRep _ ρ)) 〉 ⟦ x₂:= M2 〈 ρ 〉 ,x₁:= M1 〈 ρ 〉 ,x₀:= M0 〈 ρ 〉 ⟧
  ≡ N ⟦ x₂:= M2 ,x₁:= M1 ,x₀:= M0 ⟧ 〈 ρ 〉
botSub₃-liftRep₃ {M2 = M2} {M1} {M0} {ρ} N = let open ≡-Reasoning in
              begin
                N 〈 liftRep _ (liftRep _ (liftRep _ ρ)) 〉 ⟦ x₂:= M2 〈 ρ 〉 ,x₁:= M1 〈 ρ 〉 ,x₀:= M0 〈 ρ 〉 ⟧
              ≡⟨⟨ sub-•SR N ⟩⟩
                N ⟦ (x₂:= M2 〈 ρ 〉 ,x₁:= M1 〈 ρ 〉 ,x₀:= M0 〈 ρ 〉) •SR liftRep _ (liftRep _ (liftRep _ ρ)) ⟧
              ≡⟨ sub-congr N botSub₃-liftRep₃' ⟩
                N ⟦ ρ •RS (x₂:= M2 ,x₁:= M1 ,x₀:= M0) ⟧
              ≡⟨ sub-•RS N ⟩
                N ⟦ x₂:= M2 ,x₁:= M1 ,x₀:= M0 ⟧ 〈 ρ 〉
              ∎
--TODO General lemma for this
--TODO Deletable?

extendSub : ∀ {U} {V} {K} → Sub U V → Expression V (varKind K) → Sub (U , K) V
extendSub σ M _ x₀ = M
extendSub σ M _ (↑ x) = σ _ x

postulate extendSub-decomp : ∀ {U} {V} {σ : Sub U V} {K} {M : Expression V (varKind K)} {C} {L} (E : Subexp (U , K) C L) →
                           E ⟦ extendSub σ M ⟧ ≡ E ⟦ liftSub K σ ⟧ ⟦ x₀:= M ⟧

•-botsub : ∀ {U V K} {σ : Sub U V} {N : VExpression U K} → σ • (x₀:= N) ∼ extendSub σ (N ⟦ σ ⟧)
•-botsub x₀ = refl
•-botsub (↑ _) = refl
