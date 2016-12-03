module PHOPL.Neutral where

open import Data.Empty renaming (⊥ to Empty)
open import PHOPL.Grammar
open import PHOPL.Canon

data NeutralT : Alphabet → Set where

data NeutralP : Alphabet → Set where

data NeutralE : Alphabet → Set where

decode-NeutralT : ∀ {V} → NeutralT V → Term V
decode-NeutralT ()

decode-NeutralP : ∀ {V} → NeutralP V → Proof V
decode-NeutralP ()

decode-NeutralE : ∀ {V} → NeutralE V → Path V
decode-NeutralE ()

data NfT : Alphabet → Set where
  neutral : ∀ {V} → NeutralT V → NfT V
  canon   : ∀ {V} → CanonProp → NfT V
  Λ       : ∀ {V} → Type → Term (V , -Term) → NfT V

decode-NfT : ∀ {V} → NfT V → Term V
decode-NfT (neutral M) = decode-NeutralT M
decode-NfT (canon θ) = decode θ
decode-NfT (Λ A M) = ΛT A M
