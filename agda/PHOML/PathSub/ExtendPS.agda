module PHOML.PathSub.ExtendPS where
open import PHOML.Grammar
open import PHOML.PathSub.Base

extendPS : ∀ {U} {V} → PathSub U V → Path V → PathSub (U , -Term) V
extendPS τ P x₀ = P
extendPS τ P (↑ x) = τ x

