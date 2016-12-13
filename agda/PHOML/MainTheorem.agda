module PHOML.MainTheorem where
open import Data.Product hiding (_,_)
open import Prelims
open import PHOML.Grammar
open import PHOML.PathSub
open import PHOML.Red
open import PHOML.Rules
open import PHOML.Canon
open import PHOML.Compute
open import PHOML.Lemma35

⊧S_∶_ : ∀ {U V} → Sub U V → Context U → Set
⊧S σ ∶ Γ = ∀ {K} x → ⊧ σ K x ∶ (typeof x Γ) ⟦ σ ⟧

⊧_∶_≡_∶_ : ∀ {U V} → PathSub U V → Sub U V → Sub U V → Context U → Set
⊧ τ ∶ ρ ≡ σ ∶ Γ = ∀ x → ⊧E τ x ∶ ρ -Term x ≡〈 yt (typeof x Γ) 〉 σ -Term x

⊧RS : ∀ {U V W} {ρ : Rep V W} {σ : Sub U V} {Γ : Context U} → ⊧S σ ∶ Γ → ⊧S ρ •RS σ ∶ Γ
⊧RS {U} {V} {W} {ρ = ρ} {σ = σ} {Γ} ⊧σ∶Γ x = subst (λ y → ⊧ σ _ x 〈 ρ 〉 ∶ y) (≡-sym (sub-•RS (typeof x Γ))) (⊧rep {E = σ _ x} (⊧σ∶Γ x))

⊧extendSub : ∀ {U V K} {σ : Sub U V} {Γ} {E : VExpression V K} {T : Expression U (parent K)} → ⊧S σ ∶ Γ → ⊧ E ∶ T ⟦ σ ⟧ → ⊧S extendSub σ E ∶ Γ , T
⊧extendSub {E = E} {T} ⊧σ∶Γ ⊧E∶T x₀ = subst (λ x → ⊧ E ∶ x) (sub-•SR T) ⊧E∶T
⊧extendSub {σ = σ} {Γ} ⊧σ∶Γ ⊧E∶T (↑ x) = subst (λ y → ⊧ σ _ x ∶ y) (sub-•SR (typeof x Γ)) (⊧σ∶Γ x)

⊧extend : ∀ {U V} {Q : Path V} {N N'} {σ : Sub U V} {Γ A} → ⊧S σ ∶ Γ → ⊧E Q ∶ N ≡〈 A 〉 N' → ⊧ x₀::= Q ∶ x₀:= N ≡ x₀:= N' •PS liftSub -Term σ ∶ x₀:= N • liftSub -Term σ ≡ x₀:= N' • liftSub -Term σ ∶ Γ ,T A
⊧extend ⊧σ∶Γ ⊧Q∶N≡N' x₀ = ⊧Q∶N≡N'
⊧extend {V = V} {Q = Q} {N} {N'} {σ = σ} {Γ} {A = A} ⊧σ∶Γ ⊧Q∶N≡N' (↑ x) = subst₄ ⊧E_∶_≡〈_〉_ 
  (let open ≡-Reasoning in 
  begin
    σ _ x ⟦⟦ refSub ∶ idSub V ≡ idSub V ⟧⟧
  ≡⟨ pathSub-cong (σ _ x) (∼∼-sym (botPathSub-upRep {P = Q})) (sub-sym (botSub-upRep' N)) (sub-sym (botSub-upRep' N')) ⟩
    σ _ x ⟦⟦ x₀::= Q •PR upRep ∶ x₀:= N •SR upRep ≡ x₀:= N' •SR upRep ⟧⟧
  ≡⟨⟨ pathSub-•PR (σ _ x) ⟩⟩
    σ _ x ⇑ ⟦⟦ x₀::= Q ∶ x₀:= N ≡ x₀:= N' ⟧⟧
  ∎) 
  (≡-sym (botSub-upRep (σ _ x))) 
  (let open ≡-Reasoning in 
  begin
    yt (typeof x Γ ⟦ σ ⟧)
  ≡⟨ yt-sub {A = typeof x Γ} ⟩
    yt (typeof x Γ)
  ≡⟨⟨ yt-rep {A = typeof x Γ} ⟩⟩
    yt (typeof x Γ ⇑)
  ∎)
  (≡-sym (botSub-upRep (σ _ x))) 
  (⊧σ∶Γ x)

soundness : ∀ {U V} {Γ : Context U} {K} {E : VExpression U K} {T} {σ : Sub U V} → 
  Γ ⊢ E ∶ T → ⊧S σ ∶ Γ → ⊧ E ⟦ σ ⟧ ∶ T ⟦ σ ⟧
soundness-path : ∀ {U V} {Γ : Context U} {M A} {τ : PathSub U V} {ρ σ} →
  Γ ⊢ M ∶ ty A → ⊧ τ ∶ ρ ≡ σ ∶ Γ → ⊧E M ⟦⟦ τ ∶ ρ ≡ σ ⟧⟧ ∶ M ⟦ ρ ⟧ ≡〈 A 〉 M ⟦ σ ⟧

botSub-liftSub₃' : ∀ {U V L₂ L₁ L₀} {F₂ : VExpression U L₂} {F₁ : VExpression U L₁} {F₀ : VExpression U L₀} {σ : Sub U V} →
  (x₂:= F₂ ⟦ σ ⟧ ,x₁:= F₁ ⟦ σ ⟧ ,x₀:= F₀ ⟦ σ ⟧) • liftSub L₀ (liftSub L₁ (liftSub L₂ σ)) ∼ σ • (x₂:= F₂ ,x₁:= F₁ ,x₀:= F₀)
botSub-liftSub₃' x₀ = refl
botSub-liftSub₃' (↑ x₀) = refl
botSub-liftSub₃' (↑ (↑ x₀)) = refl
botSub-liftSub₃' (↑ (↑ (↑ x))) = botSub-upRep₃

botSub-liftSub₃ : ∀ {U V C K L₂ L₁ L₀} {E : Subexp (U , L₂ , L₁ , L₀) C K} {F₂ : VExpression U L₂} {F₁ : VExpression U L₁} {F₀ : VExpression U L₀} {σ : Sub U V} →
  E ⟦ liftSub L₀ (liftSub L₁ (liftSub L₂ σ)) ⟧ ⟦ x₂:= F₂ ⟦ σ ⟧ ,x₁:= F₁ ⟦ σ ⟧ ,x₀:= F₀ ⟦ σ ⟧ ⟧ ≡ E ⟦ x₂:= F₂ ,x₁:= F₁ ,x₀:= F₀ ⟧ ⟦ σ ⟧
botSub-liftSub₃ {L₂ = L₂} {L₁} {L₀} {E} {F₂} {F₁} {F₀} {σ} = let open ≡-Reasoning in 
  begin
    E ⟦ liftSub L₀ (liftSub L₁ (liftSub L₂ σ)) ⟧ ⟦ x₂:= F₂ ⟦ σ ⟧ ,x₁:= F₁ ⟦ σ ⟧ ,x₀:= F₀ ⟦ σ ⟧ ⟧
  ≡⟨⟨ sub-• E ⟩⟩
    E ⟦ (x₂:= F₂ ⟦ σ ⟧ ,x₁:= F₁ ⟦ σ ⟧ ,x₀:= F₀ ⟦ σ ⟧) • liftSub L₀ (liftSub L₁ (liftSub L₂ σ)) ⟧
  ≡⟨ sub-congr E botSub-liftSub₃' ⟩
    E ⟦ σ • (x₂:= F₂ ,x₁:= F₁ ,x₀:= F₀) ⟧
  ≡⟨ sub-• E ⟩
    E ⟦ x₂:= F₂ ,x₁:= F₁ ,x₀:= F₀ ⟧ ⟦ σ ⟧
  ∎

⇒-resp-sub : ∀ {U V} {M N : Term U} {σ : Sub U V} → M ⇒ N → M ⟦ σ ⟧ ⇒ N ⟦ σ ⟧
⇒-resp-sub {σ = σ} (βT {A = A} {M} {N}) = subst (λ x → appT (ΛT A (M ⟦ liftSub _ σ ⟧)) (N ⟦ σ ⟧) ⇒ x) (≡-sym (comp-botSub'' M)) βT
⇒-resp-sub (appTl E⇒F) = appTl (⇒-resp-sub E⇒F)
⇒-resp-sub (impl E⇒F) = impl (⇒-resp-sub E⇒F)
⇒-resp-sub (impr E⇒F) = impr (⇒-resp-sub E⇒F)

≃-resp-sub : ∀ {U V} {M N : Term U} {σ : Sub U V} → M ≃ N → M ⟦ σ ⟧ ≃ N ⟦ σ ⟧
≃-resp-sub = respects-RST₂ (λ _ _ → ⇒-resp-sub) _ _

soundness (varR x _) ⊧Sσ∶Γ = ⊧Sσ∶Γ x
soundness (appR Γ⊢M∶A⇛B Γ⊢M∶A) ⊧Sσ∶Γ = ⊧appT (soundness Γ⊢M∶A⇛B ⊧Sσ∶Γ) (soundness Γ⊢M∶A ⊧Sσ∶Γ)
soundness {U} {V} {σ = σ} (ΛR {A = A} {M = M} {B} Γ,A⊢M∶B) ⊧Sσ∶Γ W ρ N N' Q ⊧N∶A ⊧N'∶A ⊧Q∶N≡N' =
  let NN'Q : Sub (extend W pathDom) W
      NN'Q = x₂:= N ,x₁:= N' ,x₀:= Q in
  let σ↑ : Sub (U , -Term) (W , -Term)
      σ↑ = liftSub -Term (ρ •RS σ) in
  let σ↑N : Sub (U , -Term) W
      σ↑N = x₀:= N • σ↑ in
  let σ↑N' : Sub (U , -Term) W
      σ↑N' = x₀:= N' • σ↑ in
  let ⊧MσQ∶MN≡MN' : ⊧E M ⟦⟦ x₀::= Q ∶ x₀:= N ≡ x₀:= N' •PS σ↑ ∶ σ↑N ≡ σ↑N' ⟧⟧ ∶ M ⟦ σ↑N ⟧ ≡〈 B 〉 M ⟦ σ↑N' ⟧
      ⊧MσQ∶MN≡MN' = soundness-path Γ,A⊢M∶B (⊧extend (⊧RS ⊧Sσ∶Γ) ⊧Q∶N≡N') in
  let ⊧MrQ∶MN≡MN' : ⊧E M ⟦ σ↑ ⟧ ⟦⟦ liftPathSub refSub ∶ sub↖ (idSub W) ≡ sub↗ (idSub W) ⟧⟧ ⟦ NN'Q ⟧ ∶ M ⟦ σ↑N ⟧ ≡〈 B 〉 M ⟦ σ↑N' ⟧
      ⊧MrQ∶MN≡MN' = subst (λ x → ⊧E x ∶ M ⟦ σ↑N ⟧ ≡〈 B 〉 (M ⟦ σ↑N' ⟧)) (let open ≡-Reasoning in 
        begin
          M ⟦⟦ x₀::= Q ∶ x₀:= N ≡ x₀:= N' •PS σ↑ ∶ σ↑N ≡ σ↑N' ⟧⟧
        ≡⟨ pathSub-cong M (•PS-congl {ρ = liftSub -Term (ρ •RS σ)} (∼∼-sym botSub₃-liftRefSub) (sub-sym botSub₃-sub↖id) (sub-sym botSub₃-sub↗id)) 
           (•-congl (sub-sym botSub₃-sub↖id) (liftSub -Term (ρ •RS σ))) (•-congl (sub-sym botSub₃-sub↗id) (liftSub -Term (ρ •RS σ))) ⟩
          M ⟦⟦ NN'Q •SP liftPathSub refSub ∶ NN'Q • sub↖ (idSub W) ≡ NN'Q • sub↗ (idSub W) •PS σ↑ ∶ (NN'Q • sub↖ (idSub W)) • σ↑ ≡ (NN'Q • sub↗ (idSub W)) • σ↑ ⟧⟧
        ≡⟨ pathSub-•PS M ⟩
          M ⟦ σ↑ ⟧ ⟦⟦ NN'Q •SP liftPathSub refSub ∶ NN'Q • sub↖ (idSub W) ≡ NN'Q • sub↗ (idSub W) ⟧⟧
        ≡⟨ pathSub-•SP (M ⟦ σ↑ ⟧) ⟩
          M ⟦ σ↑ ⟧ ⟦⟦ liftPathSub refSub ∶ sub↖ (idSub W) ≡ sub↗ (idSub W) ⟧⟧ ⟦ x₂:= N ,x₁:= N' ,x₀:= Q ⟧
        ∎) 
        ⊧MσQ∶MN≡MN' in 
  expansionE (conversionE ⊧MrQ∶MN≡MN' 
    (let open EqReasoning (RSTCLOSE _⇒_) in 
    begin
      M ⟦ x₀:= N • liftSub -Term (ρ •RS σ) ⟧
    ≡⟨ sub-• M ⟩
      M ⟦ liftSub -Term (ρ •RS σ) ⟧ ⟦ x₀:= N ⟧
    ≡⟨ sub-congl (liftSub-•RS M) ⟩
      M ⟦ liftSub _ σ ⟧ 〈 liftRep _ ρ 〉 ⟦ x₀:= N ⟧
    ≈⟨⟨ inc βT ⟩⟩
      appT (ΛT A (M ⟦ liftSub _ σ ⟧ 〈 liftRep _ ρ 〉)) N
    ∎) 
    (let open EqReasoning (RSTCLOSE _⇒_) in 
    begin
      M ⟦ x₀:= N' • liftSub -Term (ρ •RS σ) ⟧
    ≡⟨ sub-• M ⟩
      M ⟦ liftSub -Term (ρ •RS σ) ⟧ ⟦ x₀:= N' ⟧
    ≡⟨ sub-congl (liftSub-•RS M) ⟩
      M ⟦ liftSub _ σ ⟧ 〈 liftRep _ ρ 〉 ⟦ x₀:= N' ⟧
    ≈⟨⟨ inc βT ⟩⟩
      appT (ΛT A (M ⟦ liftSub _ σ ⟧ 〈 liftRep _ ρ 〉)) N'
    ∎)) 
    (subst
       (λ x →
          app* N N'
          (λλλ A
           ((M ⟦ liftSub -Term σ ⟧) ⟦⟦ liftPathSub refSub ∶ sub↖ (idSub V) ≡
            sub↗ (idSub V) ⟧⟧)
           〈 ρ 〉)
          Q
          ⇒ x)
     (let open ≡-Reasoning in 
     begin
       M ⟦ liftSub -Term σ ⟧ ⟦⟦ liftPathSub refSub ∶ sub↖ (idSub V) ≡ sub↗ (idSub V) ⟧⟧ 〈 liftsRep pathDom ρ 〉 ⟦ x₂:= N ,x₁:= N' ,x₀:= Q ⟧
     ≡⟨⟨ sub-congl (pathSub-•RP (M ⟦ liftSub -Term σ ⟧)) ⟩⟩
       M ⟦ liftSub -Term σ ⟧ ⟦⟦ liftsRep pathDom ρ •RP liftPathSub refSub ∶ liftsRep pathDom ρ •RS sub↖ (idSub V) ≡ liftsRep pathDom ρ •RS sub↗ (idSub V) ⟧⟧ ⟦ x₂:= N ,x₁:= N' ,x₀:= Q ⟧
     ≡⟨ sub-congl (pathSub-cong (M ⟦ liftSub -Term σ ⟧) 
        liftsRep-liftRefSub 
        liftsRep-sub↖id 
        liftsRep-sub↗id) ⟩
       M ⟦ liftSub -Term σ ⟧ ⟦⟦ liftPathSub refSub •PR liftRep -Term ρ ∶ sub↖ (idSub W) •SR liftRep -Term ρ ≡ sub↗ (idSub W) •SR liftRep -Term ρ ⟧⟧ ⟦ x₂:= N ,x₁:= N' ,x₀:= Q ⟧
     ≡⟨⟨ sub-congl (pathSub-•PR (M ⟦ liftSub -Term σ ⟧)) ⟩⟩
       M ⟦ liftSub -Term σ ⟧ 〈 liftRep -Term ρ 〉 ⟦⟦ liftPathSub refSub ∶ sub↖ (idSub W) ≡ sub↗ (idSub W) ⟧⟧ ⟦ x₂:= N ,x₁:= N' ,x₀:= Q ⟧
     ≡⟨⟨ cong
          (λ x →
             (x ⟦⟦ liftPathSub refSub ∶ sub↖ (idSub W) ≡ sub↗ (idSub W) ⟧⟧) ⟦
             x₂:= N ,x₁:= N' ,x₀:= Q ⟧)
          (liftSub-•RS M) ⟩⟩
       M ⟦ liftSub -Term (ρ •RS σ) ⟧ ⟦⟦ liftPathSub refSub ∶ sub↖ (idSub W) ≡ sub↗ (idSub W) ⟧⟧ ⟦ x₂:= N ,x₁:= N' ,x₀:= Q ⟧
     ∎) 
    βE)
soundness (⊥R validΓ) ⊧Sσ∶Γ = ⊧canon' bot ref
soundness (⊃R Γ⊢φ∶Ω Γ⊢ψ∶Ω) ⊧Sσ∶Γ = ⊧imp (soundness Γ⊢φ∶Ω ⊧Sσ∶Γ) (soundness Γ⊢ψ∶Ω ⊧Sσ∶Γ)
soundness (appPR Γ⊢δ∶φ⊃ψ Γ⊢ε∶φ) ⊧Sσ∶Γ = ⊧P⊃E (soundness Γ⊢δ∶φ⊃ψ ⊧Sσ∶Γ) (soundness Γ⊢ε∶φ ⊧Sσ∶Γ)
soundness {U} {σ = σ} (ΛPR {δ = δ} {φ = φ} {ψ = ψ} Γ⊢φ∶Ω Γ⊢ψ∶Ω Γ,φ⊢δ∶ψ) ⊧Sσ∶Γ = ⊧P⊃I (soundness Γ⊢φ∶Ω ⊧Sσ∶Γ) (soundness Γ⊢ψ∶Ω ⊧Sσ∶Γ) 
  (λ W ρ ε ⊧ε∶φ →
    let σε : Sub (U , -Proof) W
        σε = extendSub (ρ •RS σ) ε in
    let ⊧δε∶ψ : ⊧P δ ⟦ σε ⟧ ∶ ψ ⇑ ⟦ σε ⟧
        ⊧δε∶ψ = soundness Γ,φ⊢δ∶ψ (⊧extendSub (⊧RS ⊧Sσ∶Γ) (⊧P-change-prop ⊧ε∶φ (≡-sym (sub-•RS φ)))) in
    let ⊧δε∶ψ₂ : ⊧P δ ⟦ liftSub _ σ ⟧ 〈 liftRep _ ρ 〉 ⟦ x₀:= ε ⟧ ∶ ψ ⟦ σ ⟧ 〈 ρ 〉
        ⊧δε∶ψ₂ = subst₂ ⊧P_∶_ 
          (let open ≡-Reasoning in 
          begin
            δ ⟦ extendSub (ρ •RS σ) ε ⟧
          ≡⟨ extendSub-decomp δ ⟩
            δ ⟦ liftSub _ (ρ •RS σ) ⟧ ⟦ x₀:= ε ⟧
          ≡⟨ sub-congl (liftSub-•RS δ) ⟩
            δ ⟦ liftSub _ σ ⟧ 〈 liftRep _ ρ 〉 ⟦ x₀:= ε ⟧
          ∎) 
          (let open ≡-Reasoning in
          begin
            ψ ⇑ ⟦ extendSub (ρ •RS σ) ε ⟧
          ≡⟨ extendSub-decomp (ψ ⇑) ⟩
            ψ ⇑ ⟦ liftSub _ (ρ •RS σ) ⟧ ⟦ x₀:= ε ⟧
          ≡⟨ sub-congl (liftSub-upRep ψ) ⟩
            ψ ⟦ ρ •RS σ ⟧ ⇑ ⟦ x₀:= ε ⟧
          ≡⟨ botSub-upRep (ψ ⟦ ρ •RS σ ⟧) ⟩
            ψ ⟦ ρ •RS σ ⟧
          ≡⟨ sub-•RS ψ ⟩
            ψ ⟦ σ ⟧ 〈 ρ 〉
          ∎) ⊧δε∶ψ in
    expansionP ⊧δε∶ψ₂ βP)
soundness (convR Γ⊢δ∶φ Γ⊢ψ∶Ω φ≃ψ) ⊧Sσ∶Γ = conversionP (soundness Γ⊢δ∶φ ⊧Sσ∶Γ) (≃-resp-sub φ≃ψ)
soundness (refR Γ⊢M∶A) ⊧Sσ∶Γ = ⊧ref (soundness Γ⊢M∶A ⊧Sσ∶Γ)
soundness (⊃*R Γ⊢P∶φ≡φ' Γ⊢Q∶ψ≡ψ') ⊧Sσ∶Γ = ⊧⊃* (soundness Γ⊢P∶φ≡φ' ⊧Sσ∶Γ) (soundness Γ⊢Q∶ψ≡ψ' ⊧Sσ∶Γ)
soundness (univR Γ⊢δ∶φ⊃ψ Γ⊢ε∶ψ⊃φ) ⊧Sσ∶Γ = ⊧univ (soundness Γ⊢δ∶φ⊃ψ ⊧Sσ∶Γ) (soundness Γ⊢ε∶ψ⊃φ ⊧Sσ∶Γ)
soundness (plusR Γ⊢P∶φ≡ψ) ⊧Sσ∶Γ = proj₁ (soundness Γ⊢P∶φ≡ψ ⊧Sσ∶Γ)
soundness (minusR Γ⊢P∶φ≡ψ) ⊧Sσ∶Γ = proj₂ (soundness Γ⊢P∶φ≡ψ ⊧Sσ∶Γ)
soundness {U} {σ = σ} (lllR {B = B} {M = F} {G} {P} ΓAAE⊢P∶Fx≡Gy) ⊧Sσ∶Γ W ρ N N' Q ⊧N∶A ⊧N'∶A ⊧Q∶N≡N' = 
  let σ' : Sub (extend U pathDom) W
      σ' = extendSub (extendSub (extendSub (ρ •RS σ) N) N') Q in
  let PQ∶FN≡GN' : ⊧E P ⟦ σ' ⟧ ∶ appT (F ⇑ ⇑ ⇑ ⟦ σ' ⟧) N ≡〈 B 〉 appT (G ⇑ ⇑ ⇑ ⟦ σ' ⟧) N'
      PQ∶FN≡GN' = soundness ΓAAE⊢P∶Fx≡Gy (⊧extendSub (⊧extendSub (⊧extendSub (⊧RS ⊧Sσ∶Γ) ⊧N∶A) ⊧N'∶A) ⊧Q∶N≡N') in
  let PQ∶FN≡GN'₂ : ⊧E P ⟦ liftsSub pathDom σ ⟧ 〈 liftsRep pathDom ρ 〉 ⟦ x₂:= N ,x₁:= N' ,x₀:= Q ⟧ ∶ appT (F ⟦ σ ⟧ 〈 ρ 〉) N ≡〈 B 〉 appT (G ⟦ σ ⟧ 〈 ρ 〉) N'
      PQ∶FN≡GN'₂ = subst₃ (λ x₃ y z → ⊧E x₃ ∶ y ≡〈 B 〉 z) 
        (let open ≡-Reasoning in 
        begin
          P ⟦ σ' ⟧
        ≡⟨ extendSub-decomp P ⟩
          P ⟦ liftSub _ (extendSub (extendSub (ρ •RS σ) N) N') ⟧ ⟦ x₀:= Q ⟧
        ≡⟨ sub-congl (sub-congr P (liftSub-cong {!extendSub-decomp'!})) ⟩
          P ⟦ liftSub _ (x₀:= N' • liftSub _ (extendSub (ρ •RS σ) N)) ⟧ ⟦ x₀:= Q ⟧
        ≡⟨ {!!} ⟩
          P ⟦ liftsSub pathDom σ ⟧ 〈 liftsRep pathDom ρ 〉 ⟦ x₂:= N ,x₁:= N' ,x₀:= Q ⟧
        ∎) 
        {!!} 
        {!!} 
        PQ∶FN≡GN' in
  expansionE PQ∶FN≡GN'₂ βE
soundness (app*R Γ⊢E∶T Γ⊢E∶T₁ Γ⊢E∶T₂ Γ⊢E∶T₃) ⊧Sσ∶Γ = {!!}
soundness (convER Γ⊢E∶T Γ⊢E∶T₁ Γ⊢E∶T₂ M≃M' N≃N') ⊧Sσ∶Γ = {!!}

soundness-path Γ⊢M∶A ⊧τ∶ρ≡σ = {!!}
