module PHOML.Meta.Gen where
open import Data.Product renaming (_,_ to _,p_)
open import Prelims
open import PHOML.Grammar
open import PHOML.Red.Conv
open import PHOML.Rules
open import PHOML.Meta.ConVal
open import PHOML.Meta.Gen.Term public
open import PHOML.Meta.Gen.Proof public
open import PHOML.Meta.Gen.Path public

generation-univ₄ : ∀ {V} {Γ : Context V} {φ ψ δ ε M A N} → Γ ⊢ univ φ ψ δ ε ∶ M ≡〈 A 〉 N → Γ ⊢ ε ∶ ψ ⊃ φ
generation-univ₄ (univR _ Γ⊢ε∶N⊃M) = Γ⊢ε∶N⊃M
generation-univ₄ (convER Γ⊢univδε∶M≡N _ _ _ _) = generation-univ₄ Γ⊢univδε∶M≡N

generation-app* : ∀ {V} {Γ : Context V} {P : Path V} {M N Q L B L'} →
  Γ ⊢ app* M N P Q ∶ L ≡〈 B 〉 L' →
  Σ[ A ∈ Type ] Σ[ F ∈ Term V ] Σ[ G ∈ Term V ] (Γ ⊢ P ∶ F ≡〈 A ⇛ B 〉 G × Γ ⊢ Q ∶ M ≡〈 A 〉 N × appT F M ≃ L × appT G N ≃ L')
generation-app* (appER {M = F} {M' = G} {A = A} Γ⊢N∶A Γ⊢N'∶A Γ⊢P∶F≡G Γ⊢Q∶N≡N') = A ,p F ,p G ,p Γ⊢P∶F≡G ,p Γ⊢Q∶N≡N' ,p ref ,p ref
generation-app* (convER Γ⊢PQ∶L≡L' _ _ L≃L₁ L'≃L₁') = 
  let A ,p F ,p G ,p Γ⊢P∶F≡G ,p Γ⊢Q∶M≡N ,p FM≃L ,p GN≃L' = generation-app* Γ⊢PQ∶L≡L' in
  A ,p F ,p G ,p Γ⊢P∶F≡G ,p Γ⊢Q∶M≡N ,p trans FM≃L L≃L₁ ,p trans GN≃L' L'≃L₁'

generation-λλλ : ∀ {V} {Γ : Context V} {A P M B N} →
  Γ ⊢ λλλ A P ∶ M ≡〈 B 〉 N → Σ[ C ∈ Type ] (addpath Γ A ⊢ P ∶ appT (M ⇑ ⇑ ⇑) (var x₂) ≡〈 C 〉 appT (N ⇑ ⇑ ⇑) (var x₁) × B ≡ A ⇛ C)
generation-λλλ (lllR {B = C} _ _ Γ⊢P∶Mx≡Ny) = C ,p Γ⊢P∶Mx≡Ny ,p refl
generation-λλλ {Γ = Γ} {A = A} (convER {M = M} {M' = M'} {N' = N'}  Γ⊢ΛP∶M≡N Γ⊢M'∶B Γ⊢N'∶B M≃M' N≃N') = 
  let C ,p Γ⊢P∶Mx≡Ny ,p B≡A⇛C = generation-λλλ Γ⊢ΛP∶M≡N in
  C ,p 
  let validΓ : valid Γ
      validΓ = context-validity Γ⊢ΛP∶M≡N in
  let validΓA : valid (Γ ,T A)
      validΓA = ctxTR validΓ in
  let ΓAAE⊢M'∶A⇛C : addpath Γ A ⊢ M' ⇑ ⇑ ⇑ ∶ ty (A ⇛ C)
      ΓAAE⊢M'∶A⇛C = weakening (weakening (weakening (change-type Γ⊢M'∶B (cong ty B≡A⇛C)) validΓA (upRep-typed (ty A))) (ctxTR validΓA) (upRep-typed (ty A))) (valid-addpath validΓ) (upRep-typed (var x₁ ≡〈 A 〉 var x₀)) in 
  let ΓAAE⊢N'∶A⇛C : addpath Γ A ⊢ N' ⇑ ⇑ ⇑ ∶ ty (A ⇛ C)
      ΓAAE⊢N'∶A⇛C = weakening (weakening (weakening (change-type Γ⊢N'∶B (cong ty B≡A⇛C)) validΓA (upRep-typed (ty A))) (ctxTR validΓA) (upRep-typed (ty A))) (valid-addpath validΓ) (upRep-typed (var x₁ ≡〈 A 〉 var x₀)) in 
  convER Γ⊢P∶Mx≡Ny (appTR ΓAAE⊢M'∶A⇛C (varR x₂ (valid-addpath validΓ))) (appTR ΓAAE⊢N'∶A⇛C (varR x₁ (valid-addpath validΓ))) 
  (≃-appTl (≃-resp-rep (≃-resp-rep (≃-resp-rep M≃M')))) 
  (≃-appTl (≃-resp-rep (≃-resp-rep (≃-resp-rep N≃N')))) ,p 
  B≡A⇛C

generation-⊃* : ∀ {V} {Γ} {P Q : Path V} {φ A φ'} → Γ ⊢ P ⊃* Q ∶ φ ≡〈 A 〉 φ' →
  Σ[ ψ ∈ Term V ] Σ[ ψ' ∈ Term V ] Σ[ χ ∈ Term V ] Σ[ χ' ∈ Term V ]
  (Γ ⊢ P ∶ ψ ≡〈 Ω 〉 ψ' × Γ ⊢ Q ∶ χ ≡〈 Ω 〉 χ' × φ ≃ ψ ⊃ χ × φ' ≃ ψ' ⊃ χ' × A ≡ Ω)
generation-⊃* (⊃*R {φ = ψ} {ψ'} {χ} {χ'} Γ⊢P∶ψ≡ψ' Γ⊢Q∶χ≡χ') = ψ ,p ψ' ,p χ ,p χ' ,p Γ⊢P∶ψ≡ψ' ,p Γ⊢Q∶χ≡χ' ,p ref ,p ref ,p refl
generation-⊃* (convER Γ⊢P⊃*Q∶φ≡φ' Γ⊢φ₁∶Ω Γ⊢φ₁'∶Ω φ≃φ₁ φ'≃φ₁') = 
  let ψ ,p ψ' ,p χ ,p χ' ,p Γ⊢P∶ψ≡ψ' ,p Γ⊢Q∶χ≡χ' ,p φ₁≃ψ⊃χ ,p φ₁'≃ψ'⊃χ' ,p A≡Ω = generation-⊃* Γ⊢P⊃*Q∶φ≡φ' in 
  ψ ,p ψ' ,p χ ,p χ' ,p Γ⊢P∶ψ≡ψ' ,p Γ⊢Q∶χ≡χ' ,p trans (sym φ≃φ₁) φ₁≃ψ⊃χ ,p (trans (sym φ'≃φ₁') φ₁'≃ψ'⊃χ') ,p A≡Ω
