module PHOPL.Compute where
open import Data.Empty renaming (⊥ to Empty)
open import Data.Unit
open import Data.Product hiding (map) renaming (_,_ to _,p_)
open import Data.Sum hiding (map)
open import Prelims
open import PHOPL.Grammar
open import PHOPL.PathSub
open import PHOPL.Red
open import PHOPL.Canon
open import PHOPL.Neutral

⊧PC_∶_ : ∀ {V} → Proof V → CanonProp → Set
⊧PC_∶_ {V} δ bot = Σ[ ε ∈ NeutralP V ] δ ↠ decode-NeutralP ε
⊧PC δ ∶ imp φ ψ = ∀ ε (⊧ε∶φ : ⊧PC ε ∶ φ) → ⊧PC appP δ ε ∶ ψ

⊧P_∶_ : ∀ {V} → Proof V → Term V → Set
⊧P δ ∶ φ = Σ[ ψ ∈ CanonProp ] φ ↠ decode ψ × ⊧PC δ ∶ ψ

⊧T_∶_ : ∀ {V} → Term V → Type → Set
⊧E_∶_≡〈_〉_ : ∀ {V} → Path V → Term V → Type → Term V → Set

⊧T M ∶ A = ⊧E M ⟦⟦ refSub ∶ idSub _ ≡ idSub _ ⟧⟧ ∶ M ≡〈 A 〉 M
⊧E P ∶ φ ≡〈 Ω 〉 ψ = ⊧P plus P ∶ φ ⊃ ψ × ⊧P minus P ∶ ψ ⊃ φ
⊧E P ∶ M ≡〈 A ⇛ B 〉 M' = ∀ N N' Q → ⊧T N ∶ A → ⊧T N' ∶ A → ⊧E Q ∶ N ≡〈 A 〉 N' →
  ⊧E app* N N' P Q ∶ appT M N ≡〈 B 〉 appT M' N'

⊧_∶_ : ∀ {V K} → VExpression V K → Expression V (parent K) → Set
⊧_∶_ {K = -Proof} δ φ = ⊧P δ ∶ φ
⊧_∶_ {K = -Term} M (app (-ty A) []) = ⊧T M ∶ A
⊧_∶_ {K = -Path} P (app (-eq A) (M ∷ N ∷ [])) = ⊧E P ∶ M ≡〈 A 〉 N

conversionP : ∀ {V} {δ : Proof V} {φ ψ} → ⊧P δ ∶ φ → φ ≃ ψ → ⊧P δ ∶ ψ
conversionP (θ ,p φ↠θ ,p ⊧δ∶θ) φ≃ψ = θ ,p red-canon {θ = θ} φ↠θ φ≃ψ ,p ⊧δ∶θ

conversionE : ∀ {V} {P : Path V} {M M' N N' A} → ⊧E P ∶ M ≡〈 A 〉 N → M ≃ M' → N ≃ N' →
  ⊧E P ∶ M' ≡〈 A 〉 N'
conversionE {A = Ω} (⊧P+∶φ⊃ψ ,p ⊧P-∶ψ⊃φ) φ≃φ' ψ≃ψ' =
  conversionP ⊧P+∶φ⊃ψ (≃-imp φ≃φ' ψ≃ψ') ,p conversionP ⊧P-∶ψ⊃φ (≃-imp ψ≃ψ' φ≃φ')
conversionE {A = A ⇛ B} ⊧P∶M≡N M≃M' N≃N' L L' Q ⊧L∶A ⊧L'∶A ⊧Q∶L≡L' = 
  conversionE {A = B} (⊧P∶M≡N L L' Q ⊧L∶A ⊧L'∶A ⊧Q∶L≡L') (≃-appTl M≃M') (≃-appTl N≃N')

expansionPC : ∀ {V} {δ ε : Proof V} {θ} → ⊧PC ε ∶ θ → δ ⇒ ε → ⊧PC δ ∶ θ
expansionPC {θ = bot} (χ ,p ε↠χ) δ⇒ε = χ ,p (trans (inc δ⇒ε) ε↠χ)
expansionPC {θ = imp θ θ'} ⊧ε∶θ⊃θ' δ⇒ε χ ⊧χ∶θ = expansionPC (⊧ε∶θ⊃θ' χ ⊧χ∶θ) (appPl δ⇒ε)

expansionP : ∀ {V} {δ ε : Proof V} {φ} → ⊧P ε ∶ φ → δ ⇒ ε → ⊧P δ ∶ φ
expansionP (θ ,p φ↠θ ,p ⊧ε∶θ) δ⇒ε = θ ,p φ↠θ ,p expansionPC ⊧ε∶θ δ⇒ε

expansionT : ∀ {V} {M N : Term V} {A} → ⊧T N ∶ A → M ⇒ N → ⊧T M ∶ A
expansionE : ∀ {V} {P Q : Path V} {M A N} → ⊧E Q ∶ M ≡〈 A 〉 N → P ⇒ Q → ⊧E P ∶ M ≡〈 A 〉 N

expansionT ⊧N∶A M⇒N = conversionE (expansionE ⊧N∶A (⇒-resp-ps M⇒N)) (sym (inc M⇒N)) (sym (inc M⇒N))

expansionE {A = Ω} (⊧Q+∶φ⊃ψ ,p ⊧Q-∶ψ⊃φ) P⇒Q = 
  expansionP ⊧Q+∶φ⊃ψ (plusR P⇒Q) ,p expansionP ⊧Q-∶ψ⊃φ (minusR P⇒Q)
expansionE {A = A ⇛ B} ⊧Q∶M≡M' P⇒Q N N' R ⊧N∶A ⊧N'∶A ⊧R∶N≡N' = expansionE (⊧Q∶M≡M' N N' R ⊧N∶A ⊧N'∶A ⊧R∶N≡N') (app*l P⇒Q)

reductionPC : ∀ {V} {δ ε : Proof V} {θ} → ⊧PC δ ∶ θ → δ ⇒ ε → ⊧PC ε ∶ θ
reductionPC {V} {ε = ε} {θ = bot} (ν ,p δ↠ν) δ⇒ε = 
  let cr μ ε↠μ ν⇒?μ = diamond-R-RT (λ _ _ _ → diamond) _ _ _ (inc δ⇒ε) δ↠ν in 
  let μ' ,p μ≡μ' = neutralP-red ν⇒?μ in 
  μ' ,p subst (λ x → ε ↠ x) μ≡μ' ε↠μ
reductionPC {θ = imp θ θ'} ⊧δ∶θ⊃θ' δ⇒δ' ε ⊧ε∶θ = reductionPC (⊧δ∶θ⊃θ' ε ⊧ε∶θ) (appPl δ⇒δ')

reductionP : ∀ {V} {δ ε : Proof V} {φ} → ⊧P δ ∶ φ → δ ⇒ ε → ⊧P ε ∶ φ
reductionP (θ ,p φ↠θ ,p ⊧ε∶θ) δ⇒ε = θ ,p φ↠θ ,p reductionPC ⊧ε∶θ δ⇒ε

reductionT : ∀ {V} {M N : Term V} {A} → ⊧T M ∶ A → M ⇒ N → ⊧T N ∶ A
reductionE : ∀ {V} {P Q : Path V} {M A N} → ⊧E P ∶ M ≡〈 A 〉 N → P ⇒ Q → ⊧E Q ∶ M ≡〈 A 〉 N

reductionT ⊧N∶A M⇒N = conversionE (reductionE ⊧N∶A (⇒-resp-ps M⇒N)) (inc M⇒N) (inc M⇒N)

reductionE {A = Ω} (⊧Q+∶φ⊃ψ ,p ⊧Q-∶ψ⊃φ) P⇒Q = 
  reductionP ⊧Q+∶φ⊃ψ (plusR P⇒Q) ,p reductionP ⊧Q-∶ψ⊃φ (minusR P⇒Q)
reductionE {A = A ⇛ B} ⊧Q∶M≡M' P⇒Q N N' R ⊧N∶A ⊧N'∶A ⊧R∶N≡N' = reductionE (⊧Q∶M≡M' N N' R ⊧N∶A ⊧N'∶A ⊧R∶N≡N') (app*l P⇒Q)
--TODO Duplication

--A canonical object of type A
c : ∀ {V} → Type → Term V
c Ω = ⊥
c (A ⇛ B) = ΛT A (c B)

c-closed : ∀ {U V} A {σ : Sub U V} → c A ⟦ σ ⟧ ≡ c A
c-closed Ω = refl
c-closed (A ⇛ B) = cong (ΛT A) (c-closed B)

c-closedE : ∀ {U U' V W} A {ρ₁ ρ₂ ρ₁' ρ₂'} {τ' : PathSub U' W} {τ : PathSub U V} {σ : Sub V W} →
  c A ⟦⟦ τ ∶ ρ₁ ≡ ρ₂ ⟧⟧ ⟦ σ ⟧ ≡ c A ⟦⟦ τ' ∶ ρ₁' ≡ ρ₂' ⟧⟧
c-closedE Ω = refl
c-closedE (A ⇛ B) = cong (λλλ A) (c-closedE B)

⊧c : ∀ {V A} → ⊧T c {V} A ∶ A
⊧c {A = Ω} = (imp bot bot ,p ref ,p λ ε ⊧ε∶φ → expansionPC ⊧ε∶φ refplus) ,p imp bot bot ,p ref ,p λ ε ⊧ε∶φ → expansionPC ⊧ε∶φ refminus
⊧c {A = A ⇛ B} N N' Q ⊧N∶A ⊧N'∶A ⊧Q∶N≡N' = expansionE (conversionE 
  (subst₃ (λ x y z → ⊧E x ∶ y ≡〈 B 〉 z) 
    (≡-sym (c-closedE B)) (≡-sym (c-closed B)) (≡-sym (c-closed B)) 
    (⊧c {A = B})) 
  (sym (inc βT)) (sym (inc βT))) βE

APPl-rtΛ : ∀ {V P M N} {NN : snocList (Term V)} {A L} →
  ⊧E P ∶ APPl (appT M N) NN ≡〈 A 〉 L → Reduces-to-Λ M
APPl-rtΛ {A = Ω} ((bot ,p MNN⊃N↠⊥ ,p _) ,p _) = ⊥-elim (imp-not-red-bot MNN⊃N↠⊥)
APPl-rtΛ {M = M} {N} {NN = NN} {A = Ω} ((imp θ θ' ,p MNN⊃N↠θ⊃θ' ,p proj₂) ,p proj₃ ,p proj₄ ,p proj₅) = 
  APPl-red-canon {NN = NN} {θ = θ} (imp-red-inj₁ MNN⊃N↠θ⊃θ')
APPl-rtΛ {V} {P} {M} {N} {NN} {A ⇛ B} {L} ⊧P∶MNN≡N = APPl-rtΛ {V}
  {app* (c A) (c A) P (c A ⟦⟦ refSub ∶ idSub _ ≡ idSub _ ⟧⟧)} {M} {N}
  {NN snoc c A} {B} {appT L (c A)} 
  (⊧P∶MNN≡N (c A) (c A) (c A ⟦⟦ refSub ∶ idSub _ ≡ idSub _ ⟧⟧) ⊧c ⊧c ⊧c)

⊧E-rtΛ : ∀ {V} {P : Path V} {M N A B} → ⊧E P ∶ M ≡〈 A ⇛ B 〉 N → Reduces-to-Λ M
⊧E-rtΛ {V} {P} {M} {N} {A} {B} ⊧P∶M≡N = APPl-rtΛ {V}
                                             {app* (c A) (c A) P (c A ⟦⟦ refSub ∶ idSub _ ≡ idSub _ ⟧⟧)} {M}
                                             {c A} {[]} {B} {appT N (c A)} 
          (⊧P∶M≡N (c A) (c A) (c A ⟦⟦ refSub ∶ idSub _ ≡ idSub _ ⟧⟧) ⊧c ⊧c ⊧c)
--TODO Duplication

Lemma29 : ∀ {V} {M : Term V} {A B} → ⊧T M ∶ A ⇛ B → Reduces-to-Λ M
Lemma29 {V} {M} {A} {B} ⊧M∶A⇛B = ⊧E-rtΛ ⊧M∶A⇛B
