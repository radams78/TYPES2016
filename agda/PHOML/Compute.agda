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
open import PHOML.Compute.PC public
open import PHOML.Compute.Prop public
open import PHOML.Compute.TermPath public

⊧_∶_ : ∀ {V K} → VExpression V K → Expression V (parent K) → Set
⊧_∶_ {K = -Proof} δ φ = ⊧P δ ∶ φ
⊧_∶_ {K = -Term} M A = ⊧T M ∶ yt A
⊧_∶_ {K = -Path} P (app (-eq A) (M ∷ N ∷ [])) = ⊧E P ∶ M ≡〈 A 〉 N

⊧rep : ∀ {U V K} {E : VExpression U K} {T} {ρ : Rep U V} → ⊧ E ∶ T → ⊧ E 〈 ρ 〉 ∶ T 〈 ρ 〉
⊧rep {K = -Proof} = ⊧Prep
⊧rep {K = -Term} {T = app (-ty _) []} = ⊧Trep _
⊧rep {K = -Path} {T = app (-eq _) (_ ∷ _ ∷ [])} = ⊧Erep

⊧P⊃I : ∀ {V} {φ ψ : Term V} {δ} →
  ⊧T φ ∶ Ω → ⊧T ψ ∶ Ω →
  (∀ W (ρ : Rep V W) ε → ⊧P ε ∶ φ 〈 ρ 〉 → ⊧P appP (δ 〈 ρ 〉) ε ∶ ψ 〈 ρ 〉) →
  ⊧P δ ∶ φ ⊃ ψ
⊧P⊃I {φ = φ} {ψ} ⊧φ∶Ω ⊧ψ∶Ω hyp =
  let θ ,p φ↠θ = ⊧canon ⊧φ∶Ω in 
  let θ' ,p ψ↠θ' = ⊧canon ⊧ψ∶Ω in 
  imp θ θ' ,p ↠-imp φ↠θ ψ↠θ' ,p λ W ρ ε ⊧ε∶φ → 
    ⊧P-out (hyp W ρ ε (θ ,p rep-red-canon θ φ↠θ ,p ⊧ε∶φ)) (rep-red-canon θ' ψ↠θ')

⊧P⊃E : ∀ {V} {δ : Proof V} {φ ψ ε} → ⊧P δ ∶ φ ⊃ ψ → ⊧P ε ∶ φ → ⊧P appP δ ε ∶ ψ
⊧P⊃E (bot ,p φ⊃ψ↠⊥ ,p _) ⊧ε∶φ = ⊥-elim (imp-not-red-bot φ⊃ψ↠⊥)
⊧P⊃E {V} {ε = ε} (imp θ θ' ,p φ⊃ψ↠θ⊃θ' ,p ⊧δ∶θ⊃θ') ⊧ε∶φ = θ' ,p imp-red-inj₂ φ⊃ψ↠θ⊃θ' ,p 
  subst (λ x → ⊧PC appP x ε ∶ θ') rep-idRep (⊧δ∶θ⊃θ' V (idRep V) ε (⊧P-out ⊧ε∶φ (imp-red-inj₁ φ⊃ψ↠θ⊃θ')))

postulate ⊧neutralP : ∀ {V} {δ : NeutralP V} {φ : Term V} {θ : CanonProp} →
                    φ ↠ decode θ → ⊧ decode-NeutralP δ ∶ φ
--⊧neutralP {δ = δ} {θ = θ} φ↠θ = θ ,p φ↠θ ,p ⊧neutralPC δ

⊧neutralP' : ∀ {V} {δ : NeutralP V} {φ : Term V} → ⊧T φ ∶ Ω → ⊧P decode-NeutralP δ ∶ φ
⊧neutralP' {δ = δ} ⊧φ∶Ω = let θ ,p φ↠θ = ⊧canon ⊧φ∶Ω in ⊧neutralP {δ = δ} {θ = θ} φ↠θ

⊧appT : ∀ {V A B} {M N : Term V} → ⊧T M ∶ A ⇛ B → ⊧T N ∶ A → ⊧T appT M N ∶ B
⊧appT {A = A} {B} {M} {N} ⊧M∶A⇛B ⊧N∶A = subst (λ x → ⊧E x ∶ appT M N ≡〈 B 〉 appT M N) 
  (cong₂ (λ x y → app* x y (M ⟦⟦ refSub ∶ idSub _ ≡ idSub _ ⟧⟧) (N ⟦⟦ refSub ∶ idSub _ ≡ idSub _ ⟧⟧)) (≡-sym sub-idSub) (≡-sym sub-idSub))
  (⊧E⇛E ⊧M∶A⇛B ⊧N∶A ⊧N∶A ⊧N∶A)

⊧neutralE : ∀ {V} {P : NeutralE V} {M A N} → ⊧T M ∶ A → ⊧T N ∶ A → ⊧E decode-NeutralE P ∶ M ≡〈 A 〉 N
⊧neutralE {P = P} {A = Ω} ⊧M∶Ω ⊧N∶Ω =
  let θ ,p M↠θ = ⊧canon ⊧M∶Ω in 
  let θ' ,p N↠θ' = ⊧canon ⊧N∶Ω in (imp θ θ' ,p (↠-imp M↠θ N↠θ') ,p (λ W ρ ε ⊧ε∶φ → subst (λ x → ⊧PC x ∶ θ') (cong (λ x → appP (plus x) ε) (decode-nrepE P)) (⊧neutralPC (app (dirN -plus (nrepE ρ P)) ε)))) ,p (imp θ' θ) ,p (↠-imp N↠θ' M↠θ ,p (λ W ρ ε ⊧ε∶φ → subst (λ x → ⊧PC x ∶ θ) (cong (λ x → appP (minus x) ε) (decode-nrepE P)) (⊧neutralPC (app (dirN -minus (nrepE ρ P)) ε))))
⊧neutralE {P = P} {M} {A = A ⇛ B} {N} ⊧M∶A⇛B ⊧N∶A⇛B W ρ L L' Q ⊧L∶A ⊧L'∶A ⊧Q∶L≡L' = subst (λ x → ⊧E x ∶ appT (M 〈 ρ 〉) L ≡〈 B 〉 appT (N 〈 ρ 〉) L') (cong (λ x → app* L L' x Q) (decode-nrepE P)) 
  (⊧neutralE {P = app*N L L' (nrepE ρ P) Q} (⊧appT (⊧Trep M ⊧M∶A⇛B) ⊧L∶A) (⊧appT (⊧Trep N ⊧N∶A⇛B) ⊧L'∶A))
  --⊧neutralE {P = app*N L L' (nrepE ρ P) Q} ? ?

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

⊧E-valid₁ : ∀ {V} {P : Path V} {φ ψ : Term V} → ⊧E P ∶ φ ≡〈 Ω 〉 ψ → ⊧ φ ∶ ty Ω
⊧E-valid₁ ((bot ,p φ⊃ψ↠⊥ ,p _) ,p _) = ⊥-elim (imp-not-red-bot φ⊃ψ↠⊥)
⊧E-valid₁ ((imp θ θ' ,p φ⊃ψ↠θ⊃θ' ,p _) ,p _) = ⊧canon' θ (imp-red-inj₁ φ⊃ψ↠θ⊃θ')

⊧E-valid₂ : ∀ {V} {P : Path V} {φ ψ : Term V} → ⊧E P ∶ φ ≡〈 Ω 〉 ψ → ⊧ ψ ∶ ty Ω
⊧E-valid₂ ((bot ,p φ⊃ψ↠⊥ ,p _) ,p _) = ⊥-elim (imp-not-red-bot φ⊃ψ↠⊥)
⊧E-valid₂ ((imp θ θ' ,p φ⊃ψ↠θ⊃θ' ,p proj₂) ,p proj₄) = ⊧canon' θ' (imp-red-inj₂ φ⊃ψ↠θ⊃θ')

⊧imp : ∀ {V} {φ ψ : Term V} → ⊧T φ ∶ Ω → ⊧T ψ ∶ Ω → ⊧T φ ⊃ ψ ∶ Ω
⊧imp ⊧Tφ ⊧Tψ = let θ ,p φ↠θ = ⊧canon ⊧Tφ in 
  let θ' ,p ψ↠θ' = ⊧canon ⊧Tψ in ⊧canon' (imp θ θ') (↠-imp φ↠θ ψ↠θ')

app-wnl' : ∀ {V} {δ ε δ₁ δ₂ : Proof V} {χ : CanonP V} → δ ↠ ε → δ ≡ appP δ₁ δ₂ → ε ≡ decode-CanonP χ → Σ[ χ' ∈ CanonP V ] δ₁ ↠ decode-CanonP χ'
app-wnl' δ↠ε δ≡δ₁δ₂ ε≡χ with red-appPl δ↠ε δ≡δ₁δ₂
app-wnl' {δ₂ = δ₂} {χ} δ↠ε δ≡δ₁δ₂ ε≡χ | inj₁ (δ₁' ,p δ₁↠δ₁' ,p ε≡δ₁'δ₂) with app-canonl' {δ = δ₁'} {δ₂} {χ} (≡-trans (≡-sym ε≡δ₁'δ₂) ε≡χ)
app-wnl' {δ₁ = δ₁} δ↠ε δ≡δ₁δ₂ ε≡χ | inj₁ (δ₁' ,p δ₁↠δ₁' ,p ε≡δ₁'δ₂) | χ' ,p δ₁'≡χ' = χ' ,p (subst (λ x → δ₁ ↠ x) δ₁'≡χ' δ₁↠δ₁')
app-wnl' δ↠ε δ≡δ₁δ₂ ε≡χ | inj₂ (φ ,p δ₁' ,p δ₁↠Λφδ₁') = Λ φ δ₁' ,p δ₁↠Λφδ₁'

⊧PC-wn : ∀ {V} {δ : Proof V} {θ} → ⊧PC δ ∶ θ → Σ[ ε ∈ CanonP V ] δ ↠ decode-CanonP ε
⊧PC-wn {θ = bot} (ε ,p δ↠ε) = neutral ε ,p δ↠ε
⊧PC-wn {V} {δ} {θ = imp θ θ'} ⊧δ∶θ =
  let χ ,p δ⇑ε↠χ = ⊧PC-wn (⊧δ∶θ (V , -Proof) upRep (var x₀) (⊧neutralPC (var x₀))) in
  let χ' ,p δ⇑↠χ' = app-wnl' {χ = χ} δ⇑ε↠χ refl refl in
  let χ'' ,p δ↠χ'' ,p χ''⇑≡χ' = ↠-reflect-rep {E = δ} {ρ = upRep} δ⇑↠χ' refl in  
  let χ''' ,p χ'''⇑≡χ'' = reflect-CanonP {δ = χ''} {χ = χ'} χ''⇑≡χ' in
  χ''' ,p subst (λ x → δ ↠ x) χ'''⇑≡χ'' δ↠χ''

⊧univ : ∀ {V} {φ ψ : Term V} {δ ε} → ⊧P δ ∶ φ ⊃ ψ → ⊧P ε ∶ ψ ⊃ φ → ⊧E univ φ ψ δ ε ∶ φ ≡〈 Ω 〉 ψ
⊧univ ⊧δ∶φ⊃ψ ⊧ε∶ψ⊃φ = expansionP ⊧δ∶φ⊃ψ univplus ,p expansionP ⊧ε∶ψ⊃φ univminus

⊧P-wn : ∀ {V} {δ : Proof V} {φ} → ⊧P δ ∶ φ → Σ[ ε ∈ CanonP V ] δ ↠ decode-CanonP ε
⊧P-wn (_ ,p _ ,p ⊧PCδ∶θ) = ⊧PC-wn ⊧PCδ∶θ

not-λλλ-red-CanonΩ : ∀ {V A Q} {Qc : CanonΩ V} → λλλ A Q ↠ decode-CanonΩ Qc → Empty
not-λλλ-red-CanonΩ λQ↠Qc with λλλ-red-ref λQ↠Qc refl
not-λλλ-red-CanonΩ {V} {A} {Q} {neutral (var x)} λQ↠Qc | ()
not-λλλ-red-CanonΩ {V} {A} {Q} {neutral (app*N x x₁ x₂ x₃)} λQ↠Qc | ()
not-λλλ-red-CanonΩ {V} {A} {Q} {neutral (imp*l x x₁)} λQ↠Qc | ()
not-λλλ-red-CanonΩ {V} {A} {Q} {neutral (imp*r x x₁)} λQ↠Qc | ()
not-λλλ-red-CanonΩ {V} {A} {Q} {reffC x} λQ↠Qc | ()
not-λλλ-red-CanonΩ {V} {A} {Q} {univC x x₁ x₂ x₃} λQ↠Qc | ()

not-⊧Pλλλ : ∀ {V d A} {P : Path (extend V pathDom)} {φ} → ⊧P dir d (λλλ A P) ∶ φ → Empty
not-⊧Pλλλ {V} {d} {A} {P} ⊧λAP∶φ with Lemma35e ⊧λAP∶φ
not-⊧Pλλλ {V} {d} {A} {P} _ | δ ,p λP↠canon = not-λλλ-red-CanonΩ {V} {A} {P} {Qc = δ} λP↠canon
