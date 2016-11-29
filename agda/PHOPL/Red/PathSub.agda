module PHOPL.Red.PathSub where
open import Data.Product
open import Prelims
open import Prelims.Closure
open import PHOPL.Grammar
open import PHOPL.PathSub
open import PHOPL.Red.Base
open import PHOPL.Red.Meta

_↠p_ : ∀ {U V} → PathSub U V → PathSub U V → Set
τ ↠p τ' = ∀ x → τ x ↠ τ' x

postulate liftPathSub-red : ∀ {U V} {τ τ' : PathSub U V} → τ ↠p τ' → liftPathSub τ ↠p liftPathSub τ'

red-pathsub : ∀ {U V} (M : Term U) {ρ σ : Sub U V} {τ τ' : PathSub U V} →
            τ ↠p τ' → M ⟦⟦ τ ∶ ρ ∼ σ ⟧⟧ ↠ M ⟦⟦ τ' ∶ ρ ∼ σ ⟧⟧
red-pathsub (var x) τ↠pτ' = τ↠pτ' x
red-pathsub (app -bot []) τ↠pτ' = ref
red-pathsub (app -imp (φ ∷ ψ ∷ [])) τ↠pτ' = ⊃*-red (red-pathsub φ τ↠pτ') (red-pathsub ψ τ↠pτ')
red-pathsub (app (-lamTerm A) (M ∷ [])) τ↠pτ' = λλλ-red (red-pathsub M (liftPathSub-red τ↠pτ'))
red-pathsub (app -appTerm (M ∷ N ∷ [])) τ↠pτ' = app*-red ref ref (red-pathsub M τ↠pτ') (red-pathsub N τ↠pτ')

postulate red-pathsub-endl : ∀ {U V} (M : Term U) {ρ ρ' σ : Sub U V} {τ : PathSub U V} →
                      ρ ↠s ρ' → M ⟦⟦ τ ∶ ρ ∼ σ ⟧⟧ ↠ M ⟦⟦ τ ∶ ρ' ∼ σ ⟧⟧

postulate red-pathsub-endr : ∀ {U V} (M : Term U) {ρ σ σ' : Sub U V} {τ : PathSub U V} →
                      σ ↠s σ' → M ⟦⟦ τ ∶ ρ ∼ σ ⟧⟧ ↠ M ⟦⟦ τ ∶ ρ ∼ σ' ⟧⟧
