module PHOML.PathSub.BotPathSub where
open import Relation.Binary.PropositionalEquality
open import PHOML.Grammar
open import PHOML.PathSub.Base
open import PHOML.PathSub.RP
open import PHOML.PathSub.PR

x₀::= : ∀ {V} → Path V → PathSub (V , -Term) V
(x₀::= P) x₀ = P
(x₀::= P) (↑ x) = reff (var x)

botPathSub-liftRep : ∀ {U V} {ρ : Rep U V} {P : Path U} →
  (ρ •RP x₀::= P) ∼∼ (x₀::= (P 〈 ρ 〉) •PR liftRep -Term ρ)
botPathSub-liftRep x₀ = refl
botPathSub-liftRep (↑ x) = refl

