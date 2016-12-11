module PHOML.Compute where
open import Data.Empty renaming (⊥ to Empty)
open import Data.Unit
open import Data.Bool
open import Data.List
open import Data.Product hiding (map) renaming (_,_ to _,p_)
open import Data.Sum hiding (map)
open import Prelims
open import Prelims.Closure.RST
open import PHOML.Grammar
open import PHOML.PathSub
open import PHOML.Red
open import PHOML.Canon
open import PHOML.Neutral

⊧PC_∶_ : ∀ {V} → Proof V → CanonProp → Set
⊧PC_∶_ {V} δ bot = Σ[ ε ∈ NeutralP V ] δ ↠ decode-NeutralP ε
⊧PC_∶_ {V} δ (imp φ ψ) = ∀ W (ρ : Rep V W) (ε : Proof W) (⊧ε∶φ : ⊧PC ε ∶ φ) → ⊧PC appP (δ 〈 ρ 〉) ε ∶ ψ

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

postulate conversionP : ∀ {V} {δ : Proof V} {φ ψ} → ⊧P δ ∶ φ → φ ≃ ψ → ⊧P δ ∶ ψ
--conversionP (θ ,p φ↠θ ,p ⊧δ∶θ) φ≃ψ = θ ,p red-canon {θ = θ} φ↠θ φ≃ψ ,p ⊧δ∶θ

postulate conversionE : ∀ {V} {P : Path V} {M M' N N' A} → ⊧E P ∶ M ≡〈 A 〉 N → M ≃ M' → N ≃ N' →
                      ⊧E P ∶ M' ≡〈 A 〉 N'
{- conversionE {A = Ω} (⊧P+∶φ⊃ψ ,p ⊧P-∶ψ⊃φ) φ≃φ' ψ≃ψ' =
  conversionP ⊧P+∶φ⊃ψ (≃-imp φ≃φ' ψ≃ψ') ,p conversionP ⊧P-∶ψ⊃φ (≃-imp ψ≃ψ' φ≃φ')
conversionE {A = A ⇛ B} ⊧P∶M≡N M≃M' N≃N' L L' Q ⊧L∶A ⊧L'∶A ⊧Q∶L≡L' = 
  conversionE {A = B} (⊧P∶M≡N L L' Q ⊧L∶A ⊧L'∶A ⊧Q∶L≡L') (≃-appTl M≃M') (≃-appTl N≃N') -}

postulate expansionPC : ∀ {V} {δ ε : Proof V} {θ} → ⊧PC ε ∶ θ → δ ⇒ ε → ⊧PC δ ∶ θ
{- expansionPC {θ = bot} (χ ,p ε↠χ) δ⇒ε = χ ,p (trans (inc δ⇒ε) ε↠χ)
expansionPC {θ = imp θ θ'} ⊧ε∶θ⊃θ' δ⇒ε W ρ χ ⊧χ∶θ = expansionPC (⊧ε∶θ⊃θ' W ρ χ ⊧χ∶θ) (appPl (⇒-resp-rep δ⇒ε)) -}

postulate expansionP : ∀ {V} {δ ε : Proof V} {φ} → ⊧P ε ∶ φ → δ ⇒ ε → ⊧P δ ∶ φ
--expansionP (θ ,p φ↠θ ,p ⊧ε∶θ) δ⇒ε = θ ,p φ↠θ ,p expansionPC ⊧ε∶θ δ⇒ε

postulate expansionT : ∀ {V} {M N : Term V} {A} → ⊧T N ∶ A → M ⇒ N → ⊧T M ∶ A
postulate expansionE : ∀ {V} {P Q : Path V} {M A N} → ⊧E Q ∶ M ≡〈 A 〉 N → P ⇒ Q → ⊧E P ∶ M ≡〈 A 〉 N

{- expansionT ⊧N∶A M⇒N = conversionE (expansionE ⊧N∶A (⇒-resp-ps M⇒N)) (sym (inc M⇒N)) (sym (inc M⇒N))

expansionE {A = Ω} (⊧Q+∶φ⊃ψ ,p ⊧Q-∶ψ⊃φ) P⇒Q = 
  expansionP ⊧Q+∶φ⊃ψ (plusR P⇒Q) ,p expansionP ⊧Q-∶ψ⊃φ (minusR P⇒Q)
expansionE {A = A ⇛ B} ⊧Q∶M≡M' P⇒Q N N' R ⊧N∶A ⊧N'∶A ⊧R∶N≡N' = expansionE (⊧Q∶M≡M' N N' R ⊧N∶A ⊧N'∶A ⊧R∶N≡N') (app*l P⇒Q) -}

postulate ↞PC : ∀ {V} {δ ε : Proof V} {θ} → ⊧PC ε ∶ θ → δ ↠ ε → ⊧PC δ ∶ θ
{- ↞PC ⊧ε∶θ (inc δ⇒ε) = expansionPC ⊧ε∶θ δ⇒ε
↞PC ⊧ε∶θ ref = ⊧ε∶θ
↞PC ⊧ε'∶θ (trans δ↠ε ε↠ε') = ↞PC (↞PC ⊧ε'∶θ ε↠ε') δ↠ε -}

postulate ↞E : ∀ {V} {P Q : Path V} {M A N} → ⊧E Q ∶ M ≡〈 A 〉 N → P ↠ Q → ⊧E P ∶ M ≡〈 A 〉 N
{- ↞E ⊧Q∶M≡N (inc P⇒Q) = expansionE ⊧Q∶M≡N P⇒Q
↞E ⊧Q∶M≡N ref = ⊧Q∶M≡N
↞E ⊧Q∶M≡N (trans P↠P' P'↠Q) = ↞E (↞E ⊧Q∶M≡N P'↠Q) P↠P' -}
--TODO Duplication

postulate reductionPC : ∀ {V} {δ ε : Proof V} {θ} → ⊧PC δ ∶ θ → δ ⇒ ε → ⊧PC ε ∶ θ
{- reductionPC {V} {ε = ε} {θ = bot} (ν ,p δ↠ν) δ⇒ε = 
  let cr μ ε↠μ ν⇒?μ = diamond-R-RT (λ _ _ _ → diamond) _ _ _ (inc δ⇒ε) δ↠ν in 
  let μ' ,p μ≡μ' = neutralP-red ν ν⇒?μ in 
  μ' ,p subst (λ x → ε ↠ x) μ≡μ' ε↠μ
reductionPC {θ = imp θ θ'} ⊧δ∶θ⊃θ' δ⇒δ' W ρ ε ⊧ε∶θ = reductionPC {θ = θ'} (⊧δ∶θ⊃θ' W ρ ε ⊧ε∶θ) (appPl (⇒-resp-rep δ⇒δ')) -}

postulate reductionP : ∀ {V} {δ ε : Proof V} {φ} → ⊧P δ ∶ φ → δ ⇒ ε → ⊧P ε ∶ φ
--reductionP (θ ,p φ↠θ ,p ⊧ε∶θ) δ⇒ε = θ ,p φ↠θ ,p reductionPC ⊧ε∶θ δ⇒ε

postulate reductionT : ∀ {V} {M N : Term V} {A} → ⊧T M ∶ A → M ⇒ N → ⊧T N ∶ A
postulate reductionE : ∀ {V} {P Q : Path V} {M A N} → ⊧E P ∶ M ≡〈 A 〉 N → P ⇒ Q → ⊧E Q ∶ M ≡〈 A 〉 N

{- reductionT ⊧N∶A M⇒N = conversionE (reductionE ⊧N∶A (⇒-resp-ps M⇒N)) (inc M⇒N) (inc M⇒N)

reductionE {A = Ω} (⊧Q+∶φ⊃ψ ,p ⊧Q-∶ψ⊃φ) P⇒Q = 
  reductionP ⊧Q+∶φ⊃ψ (plusR P⇒Q) ,p reductionP ⊧Q-∶ψ⊃φ (minusR P⇒Q)
reductionE {A = A ⇛ B} ⊧Q∶M≡M' P⇒Q N N' R ⊧N∶A ⊧N'∶A ⊧R∶N≡N' = reductionE (⊧Q∶M≡M' N N' R ⊧N∶A ⊧N'∶A ⊧R∶N≡N') (app*l P⇒Q) -}
--TODO Duplication

postulate ↠T : ∀ {V} {M N : Term V} {A} → ⊧T M ∶ A → M ↠ N → ⊧T N ∶ A
{- ↠T ⊧M∶A (inc M⇒N) = reductionT ⊧M∶A M⇒N
↠T ⊧M∶A ref = ⊧M∶A
↠T ⊧M∶A (trans M↠N N↠N') = ↠T (↠T ⊧M∶A M↠N) N↠N' -}

--A canonical object of type A
c : ∀ {V} → Type → Term V
c Ω = ⊥
c (A ⇛ B) = ΛT A (c B)

postulate c-closed : ∀ {U V} A {σ : Sub U V} → c A ⟦ σ ⟧ ≡ c A
--c-closed Ω = refl
--c-closed (A ⇛ B) = cong (ΛT A) (c-closed B)

postulate c-closedE : ∀ {U U' V W} A {ρ₁ ρ₂ ρ₁' ρ₂'} {τ' : PathSub U' W} {τ : PathSub U V} {σ : Sub V W} →
                    c A ⟦⟦ τ ∶ ρ₁ ≡ ρ₂ ⟧⟧ ⟦ σ ⟧ ≡ c A ⟦⟦ τ' ∶ ρ₁' ≡ ρ₂' ⟧⟧
--c-closedE Ω = refl
--c-closedE (A ⇛ B) = cong (λλλ A) (c-closedE B)

postulate ⊧c : ∀ {V A} → ⊧T c {V} A ∶ A
{- ⊧c {A = Ω} = (imp bot bot ,p ref ,p (λ {W ρ ε (ε' ,p ε↠ε') → ε' ,p (trans (inc refplus) ε↠ε')})) ,p imp bot bot ,p ref ,p 
  λ {W ρ ε (ε' ,p ε↠ε') → ε' ,p (trans (inc refminus) ε↠ε')}
⊧c {A = A ⇛ B} N N' Q ⊧N∶A ⊧N'∶A ⊧Q∶N≡N' = expansionE (conversionE 
  (subst₃ (λ x y z → ⊧E x ∶ y ≡〈 B 〉 z) 
    (≡-sym (c-closedE B)) (≡-sym (c-closed B)) (≡-sym (c-closed B)) 
    (⊧c {A = B})) 
  (sym (inc βT)) (sym (inc βT))) βE -}

postulate APPl-rtΛ : ∀ {V P M N} {NN : snocList (Term V)} {A L} →
                   ⊧E P ∶ APPl (appT M N) NN ≡〈 A 〉 L → Reduces-to-Λ M
{- APPl-rtΛ {A = Ω} ((bot ,p MNN⊃N↠⊥ ,p _) ,p _) = ⊥-elim (imp-not-red-bot MNN⊃N↠⊥)
APPl-rtΛ {M = M} {N} {NN = NN} {A = Ω} ((imp θ θ' ,p MNN⊃N↠θ⊃θ' ,p proj₂) ,p proj₃ ,p proj₄ ,p proj₅) = 
  APPl-red-canon {NN = NN} {θ = θ} (imp-red-inj₁ MNN⊃N↠θ⊃θ')
APPl-rtΛ {V} {P} {M} {N} {NN} {A ⇛ B} {L} ⊧P∶MNN≡N = APPl-rtΛ {V}
  {app* (c A) (c A) P (c A ⟦⟦ refSub ∶ idSub _ ≡ idSub _ ⟧⟧)} {M} {N}
  {NN snoc c A} {B} {appT L (c A)} 
  (⊧P∶MNN≡N (c A) (c A) (c A ⟦⟦ refSub ∶ idSub _ ≡ idSub _ ⟧⟧) ⊧c ⊧c ⊧c) -}

postulate ⊧E-rtΛ : ∀ {V} {P : Path V} {M N A B} → ⊧E P ∶ M ≡〈 A ⇛ B 〉 N → Reduces-to-Λ M
{- ⊧E-rtΛ {V} {P} {M} {N} {A} {B} ⊧P∶M≡N = APPl-rtΛ {V}
                                             {app* (c A) (c A) P (c A ⟦⟦ refSub ∶ idSub _ ≡ idSub _ ⟧⟧)} {M}
                                             {c A} {[]} {B} {appT N (c A)} 
          (⊧P∶M≡N (c A) (c A) (c A ⟦⟦ refSub ∶ idSub _ ≡ idSub _ ⟧⟧) ⊧c ⊧c ⊧c) -}
--TODO Duplication

postulate Lemma30 : ∀ {V} {M : Term V} {A B} → ⊧T M ∶ A ⇛ B → Reduces-to-Λ M
--Lemma30 {V} {M} {A} {B} ⊧M∶A⇛B = ⊧E-rtΛ ⊧M∶A⇛B

postulate ⊧refP : ∀ {V} {M φ : Term V} {θ} → φ ↠ decode θ → ⊧E reff M ∶ φ ≡〈 Ω 〉 φ
-- ⊧refP {V} {M} {φ} {θ} φ↠θ = (imp θ θ ,p ↠-imp φ↠θ φ↠θ ,p (λ W ρ ε ⊧ε∶θ → expansionPC ⊧ε∶θ refplus)) ,p imp θ θ ,p ↠-imp φ↠θ φ↠θ ,p (λ ε W ρ ⊧ε∶φ → expansionPC ⊧ε∶φ refminus)

postulate ⊧canon : ∀ {V} {φ : Term V} → ⊧T φ ∶ Ω → Σ[ θ ∈ CanonProp ] φ ↠ decode θ
--⊧canon ((bot ,p φ⊃φ↠⊥ ,p _) ,p _) = ⊥-elim (imp-not-red-bot φ⊃φ↠⊥)
--⊧canon ((imp θ θ' ,p φ⊃φ↠θ⊃θ' ,p _) ,p _) = θ ,p (imp-red-inj₁ φ⊃φ↠θ⊃θ')

postulate ⊧canon' : ∀ {V} {φ : Term V} {θ : CanonProp} → φ ↠ decode θ → ⊧T φ ∶ Ω
--⊧canon' {V} {φ} {θ} φ↠θ = (imp θ θ ,p (↠-imp φ↠θ φ↠θ) ,p (λ W ρ ε ⊧ε∶φ → ↞PC (expansionPC ⊧ε∶φ refplus) (↠-appP (↠-plus (↠-resp-rep (trans (↠-resp-ps φ↠θ) (θps-red-ref θ))))))) ,p 
--  imp θ θ ,p (↠-imp φ↠θ φ↠θ) ,p (λ W ρ ε ⊧ε∶φ → ↞PC (expansionPC ⊧ε∶φ refminus) (↠-appP (↠-minus (↠-resp-rep (trans (↠-resp-ps φ↠θ) (θps-red-ref θ))))))

postulate ⊧neutralPC : ∀ {V} (δ : NeutralP V) {θ : CanonProp} → ⊧PC decode-NeutralP δ ∶ θ
--⊧neutralPC δ {θ = bot} = δ ,p ref
--⊧neutralPC δ {θ = imp θ θ'} W ρ ε ⊧ε∶φ = subst (λ x → ⊧PC x ∶ θ') {appP (decode-NeutralP (nrepP ρ δ)) ε} (cong (λ x → appP x ε) (decode-nrepP {ρ = ρ} {δ})) (⊧neutralPC (app (nrepP ρ δ) ε))

postulate ⊧neutralP : ∀ {V} {δ : NeutralP V} {φ : Term V} {θ : CanonProp} →
                    φ ↠ decode θ → ⊧ decode-NeutralP δ ∶ φ
--⊧neutralP {δ = δ} {θ = θ} φ↠θ = θ ,p φ↠θ ,p ⊧neutralPC δ

postulate ⊧appT : ∀ {V A B} {M N : Term V} → ⊧T M ∶ A ⇛ B → ⊧T N ∶ A → ⊧T appT M N ∶ B
{- ⊧appT {A = A} {B} {M} {N} ⊧M∶A⇛B ⊧N∶A = subst (λ x → ⊧E x ∶ appT M N ≡〈 B 〉 appT M N) 
  (cong₂ (λ x y → app* x y (M ⟦⟦ refSub ∶ idSub _ ≡ idSub _ ⟧⟧) (N ⟦⟦ refSub ∶ idSub _ ≡ idSub _ ⟧⟧)) (≡-sym sub-idSub) (≡-sym sub-idSub))
  (⊧M∶A⇛B N N _ ⊧N∶A ⊧N∶A ⊧N∶A) -}

postulate ⊧neutralE : ∀ {V} {P : NeutralE V} {M A N} → ⊧T M ∶ A → ⊧T N ∶ A → ⊧E decode-NeutralE P ∶ M ≡〈 A 〉 N
{- ⊧neutralE {P = P} {A = Ω} ⊧M∶Ω ⊧N∶Ω =
  let θ ,p M↠θ = ⊧canon ⊧M∶Ω in 
  let θ' ,p N↠θ' = ⊧canon ⊧N∶Ω in (imp θ θ' ,p (↠-imp M↠θ N↠θ') ,p (λ W ρ ε ⊧ε∶φ → subst (λ x → ⊧PC x ∶ θ') (cong (λ x → appP (plus x) ε) decode-nrepE) (⊧neutralPC (app (plusN (nrepE ρ P)) ε)))) ,p (imp θ' θ) ,p (↠-imp N↠θ' M↠θ ,p (λ W ρ ε ⊧ε∶φ → subst (λ x → ⊧PC x ∶ θ) (cong (λ x → appP (minus x) ε) decode-nrepE) (⊧neutralPC (app (minusN (nrepE ρ P)) ε))))
{-  (imp θ θ' ,p ↠-imp M↠θ N↠θ' ,p λ ε ⊧ε∶φ → ⊧neutralPC (app (plusN P) ε)) ,p imp θ' θ ,p ↠-imp N↠θ' M↠θ ,p (λ ε ⊧ε∶φ → ⊧neutralPC (app (minusN P) ε)) -}
⊧neutralE {P = P} {A = A ⇛ B} ⊧M∶A⇛B ⊧N∶A⇛B L L' Q ⊧L∶A ⊧L'∶A ⊧Q∶L≡L' = 
  ⊧neutralE {P = app*N L L' P Q} (⊧appT ⊧M∶A⇛B ⊧L∶A) (⊧appT ⊧N∶A⇛B ⊧L'∶A) -}

postulate botSub₃-sub↖id : ∀ {V} {M N : Term V} {P} → (x₂:= M ,x₁:= N ,x₀:= P) • sub↖ (idSub V) ∼ x₀:= M
--botSub₃-sub↖id x₀ = refl
--botSub₃-sub↖id (↑ x) = refl

postulate botSub₃-sub↗id : ∀ {V} {M N : Term V} {P} → (x₂:= M ,x₁:= N ,x₀:= P) • sub↗ (idSub V) ∼ x₀:= N
--botSub₃-sub↗id x₀ = refl
--botSub₃-sub↗id (↑ x) = refl

postulate ⊧ref : ∀ {V} {M : Term V} {A} → ⊧T M ∶ A → ⊧E reff M ∶ M ≡〈 A 〉 M
{- ⊧ref {V} {M} {A = Ω} ⊧M∶Ω = let θ ,p M↠θ = ⊧canon ⊧M∶Ω in ⊧refP {θ = θ} M↠θ
⊧ref {V} {M} {A = A ⇛ B} ⊧M∶A⇛B L L' P ⊧L∶A ⊧L'∶A ⊧P∶L≡L' with Lemma30 ⊧M∶A⇛B
⊧ref {V} {M} {A = A ⇛ B} ⊧M∶A⇛B L L' P ⊧L∶A ⊧L'∶A ⊧P∶L≡L' | reduces-to-Λ {C} {N} M↠ΛCN = 
  let ⊧ΛCN∶A⇛B : ⊧T ΛT C N ∶ A ⇛ B
      ⊧ΛCN∶A⇛B = ↠T ⊧M∶A⇛B M↠ΛCN in
  let ⊧λλλNP : ⊧E app* L L' (λλλ C (N ⟦⟦ liftPathSub refSub ∶ sub↖ (idSub V) ≡ sub↗ (idSub V) ⟧⟧)) P ∶
             appT (ΛT C N) L ≡〈 B 〉 appT (ΛT C N) L'
      ⊧λλλNP = ⊧ΛCN∶A⇛B L L' P ⊧L∶A ⊧L'∶A ⊧P∶L≡L' in
  let ⊧N⟦⟦P⟧⟧ : ⊧E N ⟦⟦ x₀::= P ∶ x₀:= L ≡ x₀:= L' ⟧⟧ ∶ appT (ΛT C N) L ≡〈 B 〉 appT (ΛT C N) L'
      ⊧N⟦⟦P⟧⟧ = reductionE ⊧λλλNP 
        (subst
           (λ x →
              app* L L'
              (λλλ C
               (N ⟦⟦ liftPathSub refSub ∶ sub↖ (idSub V) ≡ sub↗ (idSub V) ⟧⟧))
              P
              ⇒ x)
        (let open ≡-Reasoning in 
        begin
          N ⟦⟦ liftPathSub refSub ∶ sub↖ (idSub V) ≡ sub↗ (idSub V) ⟧⟧ ⟦ x₂:= L ,x₁:= L' ,x₀:= P ⟧
        ≡⟨⟨ pathSub-•SP N ⟩⟩
          N ⟦⟦ (x₂:= L ,x₁:= L' ,x₀:= P) •SP liftPathSub refSub
            ∶ (x₂:= L ,x₁:= L' ,x₀:= P) • sub↖ (idSub V)
            ≡ (x₂:= L ,x₁:= L' ,x₀:= P) • sub↗ (idSub V) ⟧⟧
        ≡⟨ pathSub-cong N botSub₃-liftRefSub botSub₃-sub↖id botSub₃-sub↗id ⟩
          N ⟦⟦ x₀::= P ∶ x₀:= L ≡ x₀:= L' ⟧⟧
        ∎) 
        βE) in
  let ⊧refΛP : ⊧E app* L L' (reff (ΛT C N)) P ∶ appT (ΛT C N) L ≡〈 B 〉 appT (ΛT C N) L'
      ⊧refΛP = expansionE ⊧N⟦⟦P⟧⟧ βP in
  conversionE (↞E ⊧refΛP (↠-app*l (↠-reff M↠ΛCN))) (sym (sub-RT-RST (↠-appT M↠ΛCN))) 
    (sym (sub-RT-RST (↠-appT M↠ΛCN))) -}

⊧PCrep : ∀ {U V} {δ : Proof U} {ρ : Rep U V} {θ} → ⊧PC δ ∶ θ → ⊧PC δ 〈 ρ 〉 ∶ θ
⊧PCrep {δ = δ} {ρ = ρ} {θ = bot} (ν ,p δ↠ν) = nrepP ρ ν ,p subst (λ x → δ 〈 ρ 〉 ↠ x) (≡-sym (decode-nrepP {ρ = ρ} {ν})) (↠-resp-rep δ↠ν)
⊧PCrep {δ = δ} {ρ = ρ} {θ = imp θ θ'} ⊧δ∶θ⊃θ' W σ ε ⊧ε∶θ = subst (λ x → ⊧PC appP x ε ∶ θ') (rep-comp δ) (⊧δ∶θ⊃θ' W (σ •R ρ) ε ⊧ε∶θ)

Lemma35d : ∀ {V} {P : Path V} {pp θ d} → ⊧PC APPP (dir d P) (snocmap var pp) ∶ θ → Σ[ Q ∈ CanonE V ] P ↠ decode-CanonE Q
Lemma35d {pp = pp} {θ = bot} (δ ,p P+pp↠δ) = Lemma35c pp δ P+pp↠δ
Lemma35d {V} {P} {pp} {imp θ θ'} {d} ⊧P+pp∶θ⊃θ' =
  let Q ,p P↠Q = Lemma35d {V , -Proof} {P ⇑} {snocmap ↑ pp snoc x₀} {θ'} 
        (subst (λ x → ⊧PC x ∶ θ') 
        (cong (λ x → appP x (var x₀)) 
        (let open ≡-Reasoning in 
        begin
          APPP (dir d P) (snocmap var pp) ⇑
        ≡⟨ APPP-rep {εε = snocmap var pp} ⟩
          APPP (dir d (P ⇑)) (snocmap (λ E → E ⇑) (snocmap var pp))
        ≡⟨⟨ cong (APPP (dir d (P ⇑))) (snocmap-comp pp) ⟩⟩
          APPP (dir d (P ⇑)) (snocmap (λ x → var (↑ x)) pp)
        ≡⟨ cong (APPP (dir d (P ⇑))) (snocmap-comp pp) ⟩
          APPP (dir d (P ⇑)) (snocmap var (snocmap ↑ pp))
        ∎)) 
        (⊧P+pp∶θ⊃θ' (V , -Proof) upRep (var x₀) (⊧neutralPC (var x₀)))) in
  let Q' ,p P↠Q' ,p Q'≡Q = ↠-reflect-rep {E = P} {ρ = upRep} P↠Q refl in
  let Q₀ ,p Q₀≡Q' = reflect-canonE {P = Q'} {Q = Q} {ρ = upRep} Q'≡Q in
  Q₀ ,p subst (λ x → P ↠ x) Q₀≡Q' P↠Q'

Lemma35e : ∀ {V} {P : Path V} {φ d} → ⊧P dir d P ∶ φ → Σ[ Q ∈ CanonE V ] P ↠ decode-CanonE Q
Lemma35e (_ ,p _ ,p ⊧P+∶θ) = Lemma35d {pp = []} ⊧P+∶θ

⊧E-valid₁ : ∀ {V} {P : Path V} {φ ψ : Term V} → ⊧E P ∶ φ ≡〈 Ω 〉 ψ → ⊧ φ ∶ ty Ω
⊧E-valid₁ ((bot ,p φ⊃ψ↠⊥ ,p _) ,p _) = ⊥-elim (imp-not-red-bot φ⊃ψ↠⊥)
⊧E-valid₁ ((imp θ θ' ,p φ⊃ψ↠θ⊃θ' ,p _) ,p _) = ⊧canon' {θ = θ} (imp-red-inj₁ φ⊃ψ↠θ⊃θ')

⊧E-valid₂ : ∀ {V} {P : Path V} {φ ψ : Term V} → ⊧E P ∶ φ ≡〈 Ω 〉 ψ → ⊧ ψ ∶ ty Ω
⊧E-valid₂ ((bot ,p φ⊃ψ↠⊥ ,p _) ,p _) = ⊥-elim (imp-not-red-bot φ⊃ψ↠⊥)
⊧E-valid₂ ((imp θ θ' ,p φ⊃ψ↠θ⊃θ' ,p proj₂) ,p proj₄) = ⊧canon' {θ = θ'} (imp-red-inj₂ φ⊃ψ↠θ⊃θ')

⊧imp : ∀ {V} {φ ψ : Term V} → ⊧T φ ∶ Ω → ⊧T ψ ∶ Ω → ⊧T φ ⊃ ψ ∶ Ω
⊧imp ⊧Tφ ⊧Tψ = let θ ,p φ↠θ = ⊧canon ⊧Tφ in 
  let θ' ,p ψ↠θ' = ⊧canon ⊧Tψ in ⊧canon' {θ = imp θ θ'} (↠-imp φ↠θ ψ↠θ')

⊧⊃* : ∀ {V} {P : Path V} {φ φ' Q ψ ψ'} →
  ⊧E P ∶ φ ≡〈 Ω 〉 φ' → ⊧E Q ∶ ψ ≡〈 Ω 〉 ψ' → ⊧E P ⊃* Q ∶ φ ⊃ ψ ≡〈 Ω 〉 φ' ⊃ ψ'
⊧⊃* (⊧P+∶φ⊃φ' ,p ⊧P-∶φ'⊃φ) (⊧Q+∶ψ⊃ψ' ,p ⊧Q-∶ψ'⊃ψ) with Lemma35e ⊧P+∶φ⊃φ'
⊧⊃* (⊧P+∶φ⊃φ' ,p ⊧P-∶φ'⊃φ) (⊧Q+∶ψ⊃ψ' ,p ⊧Q-∶ψ'⊃ψ) | Pcanon ,p P↠Pcanon with Lemma35e ⊧Q+∶ψ⊃ψ'
⊧⊃* {Q = Q} (⊧P+∶φ⊃φ' ,p ⊧P-∶φ'⊃φ) (⊧Q+∶ψ⊃ψ' ,p ⊧Q-∶ψ'⊃ψ) | neutral Pcanon ,p P↠Pcanon | Qcanon ,p Q↠Qcanon = 
  ↞E (⊧neutralE {P = imp*l Pcanon Q} (⊧imp (⊧E-valid₁ (⊧P+∶φ⊃φ' ,p ⊧P-∶φ'⊃φ)) (⊧E-valid₁ (⊧Q+∶ψ⊃ψ' ,p ⊧Q-∶ψ'⊃ψ))) 
  (⊧imp (⊧E-valid₂ (⊧P+∶φ⊃φ' ,p ⊧P-∶φ'⊃φ)) (⊧E-valid₂ (⊧Q+∶ψ⊃ψ' ,p ⊧Q-∶ψ'⊃ψ)))) (↠-imp*l P↠Pcanon)
⊧⊃* {P = P} (⊧P+∶φ⊃φ' ,p ⊧P-∶φ'⊃φ) (⊧Q+∶ψ⊃ψ' ,p ⊧Q-∶ψ'⊃ψ) | Pcanon ,p P↠Pcanon | neutral Qcanon ,p Q↠Qcanon = 
  ↞E {!⊧neutralE {P = imp*r P Qcanon}!} {!!}
⊧⊃* (⊧P+∶φ⊃φ' ,p ⊧P-∶φ'⊃φ) (⊧Q+∶ψ⊃ψ' ,p ⊧Q-∶ψ'⊃ψ) | reffC M ,p P↠Pcanon | reffC x ,p Q↠Qcanon = {!!}
⊧⊃* (⊧P+∶φ⊃φ' ,p ⊧P-∶φ'⊃φ) (⊧Q+∶ψ⊃ψ' ,p ⊧Q-∶ψ'⊃ψ) | reffC M ,p P↠Pcanon | univC x x₁ x₂ x₃ ,p Q↠Qcanon = {!!}
⊧⊃* (⊧P+∶φ⊃φ' ,p ⊧P-∶φ'⊃φ) (⊧Q+∶ψ⊃ψ' ,p ⊧Q-∶ψ'⊃ψ) | univC x x₁ x₂ x₃ ,p P↠Pcanon | Qcanon ,p Q↠Qcanon = {!!}
