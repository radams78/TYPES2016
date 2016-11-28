--TODO Module parameters
module PHOPL.PathSub where
open import Prelims
open import PHOPL.Grammar

PathSub : Alphabet → Alphabet → Set
PathSub U V = Var U -Term → Path V
--TODO Is this like an OpFamily?

_∼∼_ : ∀ {U} {V} → PathSub U V → PathSub U V → Set
τ ∼∼ τ' = ∀ x → τ x ≡ τ' x

∼∼-refl : ∀ {U} {V} {τ : PathSub U V} → τ ∼∼ τ
∼∼-refl _ = refl

liftPathSub : ∀ {U} {V} → PathSub U V → PathSub (U , -Term) (V , -Term , -Term , -Path)
liftPathSub τ x₀ = var x₀
liftPathSub τ (↑ x) = τ x ⇑ ⇑ ⇑

liftPathSub-cong : ∀ {U} {V} {τ τ' : PathSub U V} → τ ∼∼ τ' → liftPathSub τ ∼∼ liftPathSub τ'
liftPathSub-cong _ x₀ = refl
liftPathSub-cong τ∼∼τ' (↑ x) = rep-congl (rep-congl (rep-congl (τ∼∼τ' x)))

infix 70 _⟦⟦_∶_∼_⟧⟧

_⟦⟦_∶_∼_⟧⟧ : ∀ {U} {V} → Term U → PathSub U V → 
  Sub U V → Sub U V → Path V
var x ⟦⟦ τ ∶ _ ∼ _ ⟧⟧ = τ x
app -bot [] ⟦⟦ τ ∶ _ ∼ _ ⟧⟧ = reff ⊥
app -imp (φ ∷ ψ ∷ []) ⟦⟦ τ ∶ ρ ∼ σ ⟧⟧ = φ ⟦⟦ τ ∶ ρ ∼ σ ⟧⟧ ⊃* ψ ⟦⟦ τ ∶ ρ ∼ σ ⟧⟧
app -appTerm (M ∷ N ∷ []) ⟦⟦ τ ∶ ρ ∼ σ ⟧⟧ = app* (N ⟦ ρ ⟧) (N ⟦ σ ⟧) (M ⟦⟦ τ ∶ ρ ∼ σ ⟧⟧) (N ⟦⟦ τ ∶ ρ ∼ σ ⟧⟧)
app (-lamTerm A) (M ∷ []) ⟦⟦ τ ∶ ρ ∼ σ ⟧⟧ = λλλ A (M ⟦⟦ liftPathSub τ ∶ sub↖ ρ ∼ sub↗ σ ⟧⟧)

pathSub-cong : ∀ {U} {V} M {τ τ' : PathSub U V} {ρ} {ρ'} {σ} {σ'} →
               τ ∼∼ τ' → ρ ∼ ρ' → σ ∼ σ' → M ⟦⟦ τ ∶ ρ ∼ σ ⟧⟧ ≡ M ⟦⟦ τ' ∶ ρ' ∼ σ' ⟧⟧
pathSub-cong (var x) τ∼∼τ' _ _ = τ∼∼τ' x
pathSub-cong (app -bot []) _ _ _ = refl
pathSub-cong (app -imp (φ ∷ ψ ∷ [])) τ∼∼τ' ρ∼ρ' σ∼σ' = 
  cong₂ _⊃*_ (pathSub-cong φ τ∼∼τ' ρ∼ρ' σ∼σ') 
             (pathSub-cong ψ τ∼∼τ' ρ∼ρ' σ∼σ')
pathSub-cong (app -appTerm (M ∷ N ∷ [])) τ∼∼τ' ρ∼ρ' σ∼σ' = 
  cong₄ app* (sub-congr N ρ∼ρ') (sub-congr N σ∼σ')
             (pathSub-cong M τ∼∼τ' ρ∼ρ' σ∼σ') 
             (pathSub-cong N τ∼∼τ' ρ∼ρ' σ∼σ')
pathSub-cong (app (-lamTerm A) (M ∷ [])) τ∼∼τ' ρ∼ρ' σ∼σ' = 
  cong (λλλ A) (pathSub-cong M (liftPathSub-cong τ∼∼τ') 
               (sub↖-cong ρ∼ρ') (sub↗-cong σ∼σ'))

x₀::= : ∀ {V} → Path V → PathSub (V , -Term) V
(x₀::= P) x₀ = P
(x₀::= P) (↑ x) = reff (var x)

_⋆[_∶_∼_] : ∀ {V} → Term V → Path V → Term V → Term V → Path V
M ⋆[ P ∶ N ∼ N' ] = app* N N' (reff M) P

refSub : ∀ {V} → PathSub V V
refSub x = reff (var x)

_•PR_ : ∀ {U V W} → PathSub V W → Rep U V → PathSub U W
(τ •PR ρ) x = τ (ρ -Term x)

liftPathSub-•PR : ∀ {U V W} {τ : PathSub V W} {ρ : Rep U V} →
  liftPathSub (τ •PR ρ) ∼∼ (liftPathSub τ •PR liftRep _ ρ)
liftPathSub-•PR x₀ = refl
liftPathSub-•PR (↑ x) = refl

pathSub-•PR : ∀ {U V W} M {ρ : Rep U V} {τ : PathSub V W} {σ σ'} →
  M 〈 ρ 〉 ⟦⟦ τ ∶ σ ∼ σ' ⟧⟧ ≡ M ⟦⟦ τ •PR ρ ∶ σ •SR ρ ∼ σ' •SR ρ ⟧⟧
pathSub-•PR (var x) = refl
pathSub-•PR (app -bot []) = refl
pathSub-•PR (app -imp (φ ∷ ψ ∷ [])) = cong₂ _⊃*_ (pathSub-•PR φ) (pathSub-•PR ψ)
pathSub-•PR (app (-lamTerm A) (M ∷ [])) {ρ} {τ} {σ} {σ'} = 
  cong (λλλ A) (let open ≡-Reasoning in
    M 〈 liftRep _ ρ 〉 ⟦⟦ liftPathSub τ ∶ sub↖ σ ∼ sub↗ σ' ⟧⟧
  ≡⟨ pathSub-•PR M ⟩
    M ⟦⟦ liftPathSub τ •PR liftRep _ ρ ∶ sub↖ σ •SR liftRep _ ρ ∼ sub↗ σ' •SR liftRep _ ρ ⟧⟧
  ≡⟨⟨ pathSub-cong M liftPathSub-•PR sub↖-•SR sub↗-•SR ⟩⟩
    M ⟦⟦ liftPathSub (τ •PR ρ) ∶ sub↖ (σ •SR ρ) ∼ sub↗ (σ' •SR ρ) ⟧⟧
  ∎)
pathSub-•PR (app -appTerm (M ∷ N ∷ [])) = cong₄ app* (sym (sub-•SR N)) (sym (sub-•SR N)) (pathSub-•PR M) (pathSub-•PR N)

_∶_≡_•PS_ : ∀ {U V W} → PathSub V W → Sub V W → Sub V W → Sub U V → PathSub U W
(τ ∶ σ ≡ σ' •PS ρ) x = ρ _ x ⟦⟦ τ ∶ σ ∼ σ' ⟧⟧

infixr 75 _•RP_
_•RP_ : ∀ {U} {V} {W} → Rep V W → PathSub U V → PathSub U W
(ρ •RP τ) x = τ x 〈 ρ 〉

postulate pathSub-•RP : ∀ {U} {V} {W} M {ρ : Rep V W} {τ : PathSub U V} {σ σ' : Sub U V} →
                         M ⟦⟦ ρ •RP τ ∶ ρ •RS σ ∼ ρ •RS σ' ⟧⟧ ≡ M ⟦⟦ τ ∶ σ ∼ σ' ⟧⟧ 〈 ρ 〉

liftPathSub-PS : ∀ {U V W} {τ : PathSub V W} {ρ ρ' : Sub V W} {σ : Sub U V} →
  liftPathSub (τ ∶ ρ ≡ ρ' •PS σ) ∼∼ (liftPathSub τ ∶ sub↖ ρ ≡ sub↗ ρ' •PS liftSub _ σ)
liftPathSub-PS x₀ = refl
liftPathSub-PS {τ = τ} {ρ} {ρ'} {σ} (↑ x) = let open ≡-Reasoning in
  begin
    σ _ x ⟦⟦ τ ∶ ρ ∼ ρ' ⟧⟧ ⇑ ⇑ ⇑
  ≡⟨⟨ rep-congl (rep-congl (pathSub-•RP (σ _ x))) ⟩⟩
    σ _ x ⟦⟦ upRep •RP τ ∶ upRep •RS ρ ∼ upRep •RS ρ' ⟧⟧ ⇑ ⇑
  ≡⟨⟨ rep-congl (pathSub-•RP (σ _ x)) ⟩⟩
    σ _ x ⟦⟦ upRep •RP (upRep •RP τ) ∶ upRep •RS (upRep •RS ρ) ∼ upRep •RS (upRep •RS ρ') ⟧⟧ ⇑
  ≡⟨⟨ pathSub-•RP (σ _ x) ⟩⟩
    σ _ x ⟦⟦ upRep •RP (upRep •RP (upRep •RP τ)) ∶ upRep •RS (upRep •RS (upRep •RS ρ)) ∼ upRep •RS (upRep •RS (upRep •RS ρ')) ⟧⟧
  ≡⟨⟩
    σ _ x ⟦⟦ liftPathSub τ •PR upRep ∶ sub↖ ρ •SR upRep ∼ sub↗ ρ' •SR upRep ⟧⟧
  ≡⟨⟨ pathSub-•PR (σ _ x) ⟩⟩
    σ _ x ⇑ ⟦⟦ liftPathSub τ ∶ sub↖ ρ ∼ sub↗ ρ' ⟧⟧
  ∎

pathsub-sub : ∀ {U V W} M {σ : Sub U V} {τ : PathSub V W} {ρ ρ'} →
  M ⟦ σ ⟧ ⟦⟦ τ ∶ ρ ∼ ρ' ⟧⟧ ≡ M ⟦⟦ τ ∶ ρ ≡ ρ' •PS σ ∶ ρ • σ ∼ ρ' • σ ⟧⟧
pathsub-sub (var x) = refl
pathsub-sub (app -bot []) = refl
pathsub-sub (app -imp (φ ∷ ψ ∷ [])) = cong₂ _⊃*_ (pathsub-sub φ) (pathsub-sub ψ)
pathsub-sub (app (-lamTerm A) (M ∷ [])) {σ} {τ} {ρ} {ρ'} = cong (λλλ A) (let open ≡-Reasoning in
  begin
    M ⟦ liftSub _ σ ⟧ ⟦⟦ liftPathSub τ ∶ sub↖ ρ ∼ sub↗ ρ' ⟧⟧
  ≡⟨ pathsub-sub M ⟩
    M ⟦⟦ liftPathSub τ ∶ sub↖ ρ ≡ sub↗ ρ' •PS liftSub _ σ ∶ sub↖ ρ • liftSub _ σ ∼ sub↗ ρ' • liftSub _ σ ⟧⟧
  ≡⟨⟨ pathSub-cong M liftPathSub-PS sub↖-• sub↗-• ⟩⟩
    M ⟦⟦ liftPathSub (τ ∶ ρ ≡ ρ' •PS σ) ∶ sub↖ (ρ • σ) ∼ sub↗ (ρ' • σ) ⟧⟧
  ∎)
pathsub-sub (app -appTerm (M ∷ N ∷ [])) = cong₄ app* (sym (sub-comp N)) (sym (sub-comp N)) (pathsub-sub M) (pathsub-sub N)

extendPS : ∀ {U} {V} → PathSub U V → Path V → PathSub (U , -Term) V
extendPS τ P x₀ = P
extendPS τ P (↑ x) = τ x

•PS-botsub : ∀ {U V} {τ : PathSub U V} {ρ σ N} → (τ ∶ ρ ≡ σ •PS (x₀:= N)) ∼∼ extendPS τ (N ⟦⟦ τ ∶ ρ ∼ σ ⟧⟧)
•PS-botsub x₀ = refl
•PS-botsub (↑ _) = refl
