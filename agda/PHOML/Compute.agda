module PHOML.Compute where
open import Data.Empty renaming (⊥ to Empty)
open import Data.Unit
open import Data.Bool
open import Data.List
open import Data.Product hiding (map) renaming (_,_ to _,p_)
open import Data.Sum hiding (map)
open import Prelims
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
