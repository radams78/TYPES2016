module PHOPL.Red.Confluent where
open import Data.Empty renaming (⊥ to Empty)
open import Data.Sum
open import Data.Product renaming (_,_ to _,p_)
open import Prelims
open import Prelims.Closure
open import PHOPL.Grammar
open import PHOPL.Red
open import Reduction PHOPL β

postulate β-confluent : ∀ {V C K} {E F G : Subexp V C K} → E ↠ F → E ↠ G → Σ[ H ∈ Subexp V C K ] F ↠ H × G ↠ H