module PHOPL.Red.Reflect where
open import Data.Product renaming (_,_ to _,p_)
open import Prelims
open import PHOPL.Grammar
open import PHOPL.PathSub
open import PHOPL.Red.Base

⇒-reflect-rep : ∀ {U V K} {E : VExpression U K} {ρ : Rep U V} {F} → E 〈 ρ 〉 ⇒ F → Σ[ F' ∈ VExpression U K ] E ⇒ F' × F ≡ F' 〈 ρ 〉
⇒-reflect-rep {E = var _} ()
⇒-reflect-rep {E = app -bot []} ()
⇒-reflect-rep {E = app -imp (φ ∷ ψ ∷ [])} {ρ} (impl φρ⇒φ'ρ) = 
  let φ' ,p φ⇒φ' ,p φ'ρ≡φ'ρ = ⇒-reflect-rep φρ⇒φ'ρ in 
  φ' ⊃ ψ ,p impl φ⇒φ' ,p cong (λ x → x ⊃ ψ 〈 ρ 〉) φ'ρ≡φ'ρ
⇒-reflect-rep {E = app -imp (φ ∷ ψ ∷ [])} {ρ} (impr ψρ⇒ψ'ρ) =
  let ψ' ,p ψ⇒ψ' ,p ψ'ρ≡ψ'ρ = ⇒-reflect-rep ψρ⇒ψ'ρ in 
  φ ⊃ ψ' ,p impr ψ⇒ψ' ,p cong (λ x → φ 〈 ρ 〉 ⊃ x) ψ'ρ≡ψ'ρ
⇒-reflect-rep {E = app (-lamTerm _) _} ()
⇒-reflect-rep {E = app -appTerm (var _ ∷ _ ∷ [])} (appTl ())
⇒-reflect-rep {E = app -appTerm (app -bot [] ∷ _ ∷ [])} (appTl ())
⇒-reflect-rep {E = app -appTerm (app -imp (φ ∷ ψ ∷ []) ∷ N ∷ [])} {ρ} (appTl Mρ⇒M'ρ) = 
  let M' ,p M⇒M' ,p M'ρ≡M'ρ = ⇒-reflect-rep Mρ⇒M'ρ in
  appT M' N ,p appTl M⇒M' ,p cong (λ x → appT x (N 〈 ρ 〉)) M'ρ≡M'ρ
⇒-reflect-rep {E = app -appTerm (app (-lamTerm A) (M ∷ []) ∷ N ∷ [])} βT = 
  M ⟦ x₀:= N ⟧ ,p βT ,p (≡-sym (compRS-botSub M))
⇒-reflect-rep {E = app -appTerm (app (-lamTerm A) (M ∷ []) ∷ N ∷ [])} (appTl ())
⇒-reflect-rep {E = app -appTerm (app -appTerm x₁ ∷ N ∷ [])} {ρ} (appTl Mρ⇒M'ρ) =
  let M' ,p M⇒M' ,p M'ρ≡M'ρ = ⇒-reflect-rep Mρ⇒M'ρ in
  appT M' N ,p appTl M⇒M' ,p cong (λ x → appT x (N 〈 ρ 〉)) M'ρ≡M'ρ
⇒-reflect-rep {E = app -lamProof _} ()
⇒-reflect-rep {E = app -appProof (var _ ∷ _ ∷ [])} (appPl ())
⇒-reflect-rep {E = app -appProof (app -lamProof δ ∷ ε ∷ [])} {ρ} (appPl ())
⇒-reflect-rep {E = app -appProof (app -appProof x₁ ∷ ε ∷ [])} {ρ} (appPl δρ⇒δ'ρ) =
  let δ' ,p δ⇒δ' ,p δ'ρ≡δ'ρ = ⇒-reflect-rep δρ⇒δ'ρ in
  appP δ' ε ,p appPl δ⇒δ' ,p cong (λ x → appP x (ε 〈 ρ 〉)) δ'ρ≡δ'ρ
⇒-reflect-rep {E = app -appProof (app (-dir _) (var x ∷ []) ∷ ε ∷ [])} (appPl (dirR ()))
⇒-reflect-rep {E = app -appProof (app (-dir _) (app -ref (M ∷ []) ∷ []) ∷ ε ∷ [])} {ρ} (appPl δρ⇒δ'ρ) =
  let δ' ,p δ⇒δ' ,p δ'ρ≡δ'ρ = ⇒-reflect-rep δρ⇒δ'ρ in
  appP δ' ε ,p appPl δ⇒δ' ,p cong (λ x → appP x (ε 〈 ρ 〉)) δ'ρ≡δ'ρ
⇒-reflect-rep {E = app -appProof (app (-dir _) (app -ref (M ∷ []) ∷ []) ∷ ε ∷ [])} refdir = ε ,p refdir ,p refl
⇒-reflect-rep {E = app -appProof (app (-dir _) (app -imp* x₁ ∷ []) ∷ ε ∷ [])} {ρ} (appPl δρ⇒δ'ρ) =
  let δ' ,p δ⇒δ' ,p δ'ρ≡δ'ρ = ⇒-reflect-rep δρ⇒δ'ρ in
  appP δ' ε ,p appPl δ⇒δ' ,p cong (λ x → appP x (ε 〈 ρ 〉)) δ'ρ≡δ'ρ
⇒-reflect-rep {E = app -appProof (app (-dir _) (app -univ x₁ ∷ []) ∷ ε ∷ [])} {ρ} (appPl δρ⇒δ'ρ) =
  let δ' ,p δ⇒δ' ,p δ'ρ≡δ'ρ = ⇒-reflect-rep δρ⇒δ'ρ in
  appP δ' ε ,p appPl δ⇒δ' ,p cong (λ x → appP x (ε 〈 ρ 〉)) δ'ρ≡δ'ρ
⇒-reflect-rep {E = app -appProof (app (-dir _) (app (-lll x) x₁ ∷ []) ∷ ε ∷ [])} {ρ} (appPl δρ⇒δ'ρ) =
  let δ' ,p δ⇒δ' ,p δ'ρ≡δ'ρ = ⇒-reflect-rep δρ⇒δ'ρ in
  appP δ' ε ,p appPl δ⇒δ' ,p cong (λ x → appP x (ε 〈 ρ 〉)) δ'ρ≡δ'ρ
⇒-reflect-rep {E = app -appProof (app (-dir _) (app -app* x₁ ∷ []) ∷ ε ∷ [])} {ρ} (appPl δρ⇒δ'ρ) =
  let δ' ,p δ⇒δ' ,p δ'ρ≡δ'ρ = ⇒-reflect-rep δρ⇒δ'ρ in
  appP δ' ε ,p appPl δ⇒δ' ,p cong (λ x → appP x (ε 〈 ρ 〉)) δ'ρ≡δ'ρ
⇒-reflect-rep {E = app (-dir d) (M ∷ [])} (dirR Mρ⇒M'ρ) =
  let M' ,p M⇒M' ,p M'ρ≡M'ρ = ⇒-reflect-rep Mρ⇒M'ρ in
  dir d M' ,p dirR M⇒M' ,p cong (dir d) M'ρ≡M'ρ
⇒-reflect-rep {E = app -ref (M ∷ [])} (reffR Mρ⇒M'ρ) =
  let M' ,p M⇒M' ,p M'ρ≡M'ρ = ⇒-reflect-rep Mρ⇒M'ρ in
  reff M' ,p reffR M⇒M' ,p cong reff M'ρ≡M'ρ
⇒-reflect-rep {E = app -imp* (var x ∷ Q ∷ [])} (imp*l ())
⇒-reflect-rep {E = app -imp* (var x ∷ Q ∷ [])} {ρ} (imp*r Qρ⇒Q'ρ) =
  let Q' ,p Q⇒Q' ,p Q'ρ≡Q'ρ = ⇒-reflect-rep Qρ⇒Q'ρ in
  var x ⊃* Q' ,p imp*r Q⇒Q' ,p cong (λ y → var (ρ _ x) ⊃* y) Q'ρ≡Q'ρ
⇒-reflect-rep {E = app -imp* (app -ref _ ∷ var x ∷ [])} {ρ} (imp*l Pρ⇒P'ρ) =
  let P' ,p P⇒P' ,p P'ρ≡P'ρ = ⇒-reflect-rep Pρ⇒P'ρ in
  P' ⊃* var x ,p imp*l P⇒P' ,p cong (λ y → y ⊃* var (ρ _ x)) P'ρ≡P'ρ
⇒-reflect-rep {E = app -imp* (app -ref _ ∷ var _ ∷ [])} (imp*r ())
⇒-reflect-rep {E = app -imp* (app -ref (M ∷ []) ∷ app -ref (N ∷ []) ∷ [])} ref⊃* = 
  reff (M ⊃ N) ,p ref⊃* ,p refl
⇒-reflect-rep {E = app -imp* (app -ref (M ∷ []) ∷ app -ref (N ∷ []) ∷ [])} {ρ} (imp*l Pρ⇒P'ρ) =
  let P' ,p P⇒P' ,p P'ρ≡P'ρ = ⇒-reflect-rep Pρ⇒P'ρ in
  P' ⊃* reff N ,p imp*l P⇒P' ,p cong (λ y → y ⊃* reff (N 〈 ρ 〉)) P'ρ≡P'ρ
⇒-reflect-rep {E = app -imp* (app -ref (M ∷ []) ∷ app -ref (N ∷ []) ∷ [])} {ρ} (imp*r Qρ⇒Q'ρ) =
  let Q' ,p Q⇒Q' ,p Q'ρ≡Q'ρ = ⇒-reflect-rep Qρ⇒Q'ρ in
  reff M ⊃* Q' ,p imp*r Q⇒Q' ,p cong (λ y → reff (M 〈 ρ 〉) ⊃* y) Q'ρ≡Q'ρ
⇒-reflect-rep {E = app -imp* (app -ref _ ∷ app -imp* (Q₁ ∷ Q₂ ∷ []) ∷ [])} {ρ} (imp*l Pρ⇒P'ρ) =
  let P' ,p P⇒P' ,p P'ρ≡P'ρ = ⇒-reflect-rep Pρ⇒P'ρ in
  P' ⊃* (Q₁ ⊃* Q₂) ,p imp*l P⇒P' ,p cong (λ y → y ⊃* (Q₁ 〈 ρ 〉 ⊃* Q₂ 〈 ρ 〉)) P'ρ≡P'ρ
⇒-reflect-rep {E = app -imp* (app -ref (M ∷ []) ∷ app -imp* x₂ ∷ [])} {ρ} (imp*r Qρ⇒Q'ρ) =
  let Q' ,p Q⇒Q' ,p Q'ρ≡Q'ρ = ⇒-reflect-rep Qρ⇒Q'ρ in
  reff M ⊃* Q' ,p imp*r Q⇒Q' ,p cong (λ y → reff (M 〈 ρ 〉) ⊃* y) Q'ρ≡Q'ρ
⇒-reflect-rep {E = app -imp* (app -ref _ ∷ app -univ (φ ∷ ψ ∷ δ ∷ ε ∷ []) ∷ [])} {ρ} (imp*l Pρ⇒P'ρ) =
  let P' ,p P⇒P' ,p P'ρ≡P'ρ = ⇒-reflect-rep Pρ⇒P'ρ in
  P' ⊃* univ φ ψ δ ε ,p imp*l P⇒P' ,p cong (λ y → y ⊃* univ (φ 〈 ρ 〉) (ψ 〈 ρ 〉) (δ 〈 ρ 〉) (ε 〈 ρ 〉)) P'ρ≡P'ρ
⇒-reflect-rep {E = app -imp* (app -ref (M ∷ []) ∷ app -univ x₂ ∷ [])} {ρ} (imp*r Qρ⇒Q'ρ) =
  let Q' ,p Q⇒Q' ,p Q'ρ≡Q'ρ = ⇒-reflect-rep Qρ⇒Q'ρ in
  reff M ⊃* Q' ,p imp*r Q⇒Q' ,p cong (λ y → reff (M 〈 ρ 〉) ⊃* y) Q'ρ≡Q'ρ
⇒-reflect-rep {E = app -imp* (app -ref _ ∷ app (-lll A) (Q ∷ []) ∷ [])} {ρ} (imp*l Pρ⇒P'ρ) =
  let P' ,p P⇒P' ,p P'ρ≡P'ρ = ⇒-reflect-rep Pρ⇒P'ρ in
  P' ⊃* λλλ A Q ,p imp*l P⇒P' ,p cong (λ y → y ⊃* (λλλ A Q) 〈 ρ 〉) P'ρ≡P'ρ
⇒-reflect-rep {E = app -imp* (app -ref (M ∷ []) ∷ app (-lll x) x₂ ∷ [])} {ρ} (imp*r Qρ⇒Q'ρ) =
  let Q' ,p Q⇒Q' ,p Q'ρ≡Q'ρ = ⇒-reflect-rep Qρ⇒Q'ρ in
  reff M ⊃* Q' ,p imp*r Q⇒Q' ,p cong (λ y → reff (M 〈 ρ 〉) ⊃* y) Q'ρ≡Q'ρ
⇒-reflect-rep {E = app -imp* (app -ref x₁ ∷ app -app* (M ∷ N ∷ Q₁ ∷ Q₂ ∷ []) ∷ [])} {ρ} (imp*l Pρ⇒P'ρ) =
  let P' ,p P⇒P' ,p P'ρ≡P'ρ = ⇒-reflect-rep Pρ⇒P'ρ in
  P' ⊃* app* M N Q₁ Q₂ ,p imp*l P⇒P' ,p cong (λ y → y ⊃* (app* M N Q₁ Q₂) 〈 ρ 〉) P'ρ≡P'ρ
⇒-reflect-rep {E = app -imp* (app -ref (M ∷ []) ∷ app -app* _ ∷ [])} {ρ} (imp*r Qρ⇒Q'ρ) =
  let Q' ,p Q⇒Q' ,p Q'ρ≡Q'ρ = ⇒-reflect-rep Qρ⇒Q'ρ in
  reff M ⊃* Q' ,p imp*r Q⇒Q' ,p cong (λ y → reff (M 〈 ρ 〉) ⊃* y) Q'ρ≡Q'ρ
⇒-reflect-rep {E = app -imp* (app -imp* _ ∷ Q ∷ [])} {ρ} (imp*l Pρ⇒P'ρ) =
  let P' ,p P⇒P' ,p P'ρ≡P'ρ = ⇒-reflect-rep Pρ⇒P'ρ in
  P' ⊃* Q ,p imp*l P⇒P' ,p cong (λ y → y ⊃* Q 〈 ρ 〉) P'ρ≡P'ρ
⇒-reflect-rep {E = app -imp* (app -imp* (P₁ ∷ P₂ ∷ []) ∷ Q ∷ [])} {ρ} (imp*r Qρ⇒Q'ρ) =
  let Q' ,p Q⇒Q' ,p Q'ρ≡Q'ρ = ⇒-reflect-rep Qρ⇒Q'ρ in
  (P₁ ⊃* P₂) ⊃* Q' ,p imp*r Q⇒Q' ,p cong (λ y → (P₁ ⊃* P₂) 〈 ρ 〉 ⊃* y) Q'ρ≡Q'ρ
⇒-reflect-rep {E = app -imp* (app -univ _ ∷ Q ∷ [])} {ρ} (imp*l Pρ⇒P'ρ) =
  let P' ,p P⇒P' ,p P'ρ≡P'ρ = ⇒-reflect-rep Pρ⇒P'ρ in
  P' ⊃* Q ,p imp*l P⇒P' ,p cong (λ y → y ⊃* Q 〈 ρ 〉) P'ρ≡P'ρ
⇒-reflect-rep {E = app -imp* (app -univ (φ ∷ ψ ∷ δ ∷ ε ∷ []) ∷ Q ∷ [])} {ρ} (imp*r Qρ⇒Q'ρ) =
  let Q' ,p Q⇒Q' ,p Q'ρ≡Q'ρ = ⇒-reflect-rep Qρ⇒Q'ρ in
  (univ φ ψ δ ε) ⊃* Q' ,p imp*r Q⇒Q' ,p cong (λ y → (univ φ ψ δ ε) 〈 ρ 〉 ⊃* y) Q'ρ≡Q'ρ
⇒-reflect-rep {E = app -imp* (app (-lll x) x₁ ∷ Q ∷ [])} {ρ} (imp*l Pρ⇒P'ρ) =
  let P' ,p P⇒P' ,p P'ρ≡P'ρ = ⇒-reflect-rep Pρ⇒P'ρ in
  P' ⊃* Q ,p imp*l P⇒P' ,p cong (λ y → y ⊃* Q 〈 ρ 〉) P'ρ≡P'ρ
⇒-reflect-rep {E = app -imp* (app (-lll A) (P ∷ []) ∷ Q ∷ [])} {ρ} (imp*r Qρ⇒Q'ρ) =
  let Q' ,p Q⇒Q' ,p Q'ρ≡Q'ρ = ⇒-reflect-rep Qρ⇒Q'ρ in
  λλλ A P ⊃* Q' ,p imp*r Q⇒Q' ,p cong (λ y → (λλλ A P) 〈 ρ 〉 ⊃* y) Q'ρ≡Q'ρ
⇒-reflect-rep {E = app -imp* (app -app* x₁ ∷ Q ∷ [])} {ρ} (imp*l Pρ⇒P'ρ) =
  let P' ,p P⇒P' ,p P'ρ≡P'ρ = ⇒-reflect-rep Pρ⇒P'ρ in
  P' ⊃* Q ,p imp*l P⇒P' ,p cong (λ y → y ⊃* Q 〈 ρ 〉) P'ρ≡P'ρ
⇒-reflect-rep {E = app -imp* (app -app* (M ∷ N ∷ P ∷ P' ∷ []) ∷ Q ∷ [])}  {ρ} (imp*r Qρ⇒Q'ρ) =
  let Q' ,p Q⇒Q' ,p Q'ρ≡Q'ρ = ⇒-reflect-rep Qρ⇒Q'ρ in
  app* M N P P' ⊃* Q' ,p imp*r Q⇒Q' ,p cong (λ y → (app* M N P P') 〈 ρ 〉 ⊃* y) Q'ρ≡Q'ρ
⇒-reflect-rep {E = app -univ _} ()
⇒-reflect-rep {E = app (-lll _) _} ()
⇒-reflect-rep {E = app -app* (M ∷ N ∷ var x ∷ Q ∷ [])} (app*l ())
⇒-reflect-rep {E = app -app* (M ∷ M' ∷ app -ref (var x ∷ []) ∷ Q ∷ [])} {ρ} (app*l (reffR ()))
⇒-reflect-rep {E = app -app* (M ∷ M' ∷ app -ref (app -bot x₁ ∷ []) ∷ Q ∷ [])}  {ρ} (app*l Pρ⇒P'ρ) =
  let P' ,p P⇒P' ,p P'ρ≡P'ρ = ⇒-reflect-rep Pρ⇒P'ρ in
  app* M M' P' Q ,p app*l P⇒P' ,p cong (λ x → app* (M 〈 ρ 〉) (M' 〈 ρ 〉) x (Q 〈 ρ 〉)) P'ρ≡P'ρ
⇒-reflect-rep {E = app -app* (M ∷ M' ∷ app -ref (app -imp x₁ ∷ []) ∷ Q ∷ [])}  {ρ} (app*l Pρ⇒P'ρ) =
  let P' ,p P⇒P' ,p P'ρ≡P'ρ = ⇒-reflect-rep Pρ⇒P'ρ in
  app* M M' P' Q ,p app*l P⇒P' ,p cong (λ x → app* (M 〈 ρ 〉) (M' 〈 ρ 〉) x (Q 〈 ρ 〉)) P'ρ≡P'ρ
⇒-reflect-rep {E = app -app* (M ∷ M' ∷ app -ref (app (-lamTerm A) (N ∷ []) ∷ []) ∷ Q ∷ [])} {ρ} βP = 
  N ⟦⟦ (x₀::= Q) ∶ (x₀:= M) ≡ x₀:= M' ⟧⟧ ,p βP ,p (let open ≡-Reasoning in 
  begin
    N 〈 liftRep -Term ρ 〉 ⟦⟦ x₀::= (Q 〈 ρ 〉) ∶ x₀:= M 〈 ρ 〉 ≡ x₀:= M' 〈 ρ 〉 ⟧⟧
  ≡⟨ pathSub-•PR N ⟩
    N ⟦⟦ x₀::= (Q 〈 ρ 〉) •PR liftRep -Term ρ ∶ x₀:= M 〈 ρ 〉 •SR liftRep -Term ρ ≡ x₀:= M' 〈 ρ 〉 •SR liftRep -Term ρ ⟧⟧
  ≡⟨⟨ pathSub-cong N botPathSub-liftRep compRS-botSub' compRS-botSub' ⟩⟩
    N ⟦⟦ ρ •RP x₀::= Q ∶ ρ •RS x₀:= M ≡ ρ •RS x₀:= M' ⟧⟧
  ≡⟨ pathSub-•RP N ⟩
    N ⟦⟦ x₀::= Q ∶ x₀:= M ≡ x₀:= M' ⟧⟧ 〈 ρ 〉
  ∎)
⇒-reflect-rep {E = app -app* (M ∷ M' ∷ app -ref (app (-lamTerm A) (N ∷ []) ∷ []) ∷ Q ∷ [])}  {ρ} (app*l Pρ⇒P'ρ) =
  let P' ,p P⇒P' ,p P'ρ≡P'ρ = ⇒-reflect-rep Pρ⇒P'ρ in
  app* M M' P' Q ,p app*l P⇒P' ,p cong (λ x → app* (M 〈 ρ 〉) (M' 〈 ρ 〉) x (Q 〈 ρ 〉)) P'ρ≡P'ρ
⇒-reflect-rep {E = app -app* (M ∷ M' ∷ app -ref (app -appTerm x₁ ∷ []) ∷ Q ∷ [])}  {ρ} (app*l Pρ⇒P'ρ) =
  let P' ,p P⇒P' ,p P'ρ≡P'ρ = ⇒-reflect-rep Pρ⇒P'ρ in
  app* M M' P' Q ,p app*l P⇒P' ,p cong (λ x → app* (M 〈 ρ 〉) (M' 〈 ρ 〉) x (Q 〈 ρ 〉)) P'ρ≡P'ρ
⇒-reflect-rep {E = app -app* (M ∷ N ∷ app -imp* x₁ ∷ Q ∷ [])} {ρ} (app*l Pρ⇒P'ρ) =
  let P' ,p P⇒P' ,p P'ρ≡P'ρ = ⇒-reflect-rep Pρ⇒P'ρ in
  app* M N P' Q ,p app*l P⇒P' ,p cong (λ x → app* (M 〈 ρ 〉) (N 〈 ρ 〉) x (Q 〈 ρ 〉)) P'ρ≡P'ρ
⇒-reflect-rep {E = app -app* (M ∷ N ∷ app -univ x₁ ∷ Q ∷ [])} {ρ} (app*l Pρ⇒P'ρ) =
  let P' ,p P⇒P' ,p P'ρ≡P'ρ = ⇒-reflect-rep Pρ⇒P'ρ in
  app* M N P' Q ,p app*l P⇒P' ,p cong (λ x → app* (M 〈 ρ 〉) (N 〈 ρ 〉) x (Q 〈 ρ 〉)) P'ρ≡P'ρ
⇒-reflect-rep {E = app -app* (M ∷ N ∷ app (-lll A) (P ∷ []) ∷ Q ∷ [])} βE = 
  (P ⟦ x₂:= M ,x₁:= N ,x₀:= Q ⟧) ,p βE ,p (botSub₃-liftRep₃ P)
⇒-reflect-rep {E = app -app* (M ∷ N ∷ app (-lll A) (P ∷ []) ∷ Q ∷ [])} {ρ} (app*l Pρ⇒P'ρ) =
  let P' ,p P⇒P' ,p P'ρ≡P'ρ = ⇒-reflect-rep Pρ⇒P'ρ in
  app* M N P' Q ,p app*l P⇒P' ,p cong (λ x → app* (M 〈 ρ 〉) (N 〈 ρ 〉) x (Q 〈 ρ 〉)) P'ρ≡P'ρ
⇒-reflect-rep {E = app -app* (M ∷ N ∷ app -app* x₁ ∷ Q ∷ [])} {ρ} (app*l Pρ⇒P'ρ) =
  let P' ,p P⇒P' ,p P'ρ≡P'ρ = ⇒-reflect-rep Pρ⇒P'ρ in
  app* M N P' Q ,p app*l P⇒P' ,p cong (λ x → app* (M 〈 ρ 〉) (N 〈 ρ 〉) x (Q 〈 ρ 〉)) P'ρ≡P'ρ
