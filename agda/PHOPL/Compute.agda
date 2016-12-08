module PHOPL.Compute where
open import Data.Empty hiding (⊥)
open import Data.Unit
open import Data.Product renaming (_,_ to _,p_)
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

postulate Lemma29 : ∀ {V} {M : Term V} {A B} → ⊧T M ∶ A ⇛ B → Σ[ N ∈ Term (V , -Term) ] M ↠ ΛT A N
{- Prove this without using Lemma 28.
Sketch: We have M{}: M = M.  Let B = B1 -> ... -> Bn.  Then M{} ref(x) ref(y1) ... ref(yn) : M x y1 ... yn = M x y1 ... yn.
Therefore, M x y1 ... yn reduces to a canonical proposition.  Therefore M reduces to a lambda-term. -}

⊧refPC : ∀ {V} {φ : Term V} → ⊧T φ ∶ Ω → ⊧E reff φ ∶ φ ≡〈 Ω 〉 φ
⊧refPC ((bot ,p φ⊃φ↠θ ,p proj₂) ,p proj₃) = ⊥-elim (imp-not-red-bot φ⊃φ↠θ)
⊧refPC {V} {φ} ((imp θ θ₁ ,p φ⊃φ↠θ ,p proj₂) ,p proj₃) = {!!}
