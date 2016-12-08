module PHOPL.Neutral where

open import Data.Product renaming (_,_ to _,p_)
open import Prelims
open import PHOPL.Grammar
open import PHOPL.Canon
open import PHOPL.Red

data NeutralT : Alphabet → Set where

data NeutralP : Alphabet → Set where

data NeutralE : Alphabet → Set where

decode-NeutralT : ∀ {V} → NeutralT V → Term V
decode-NeutralT ()

decode-NeutralP : ∀ {V} → NeutralP V → Proof V
decode-NeutralP ()

decode-NeutralE : ∀ {V} → NeutralE V → Path V
decode-NeutralE ()

neutralP-red : ∀ {V} {δ : NeutralP V} {ε} → RClose _⇒_ (decode-NeutralP δ) ε →
  Σ[ ε' ∈ NeutralP V ] ε ≡ decode-NeutralP ε'
neutralP-red {δ = ()}

data NfT : Alphabet → Set where
  neutral : ∀ {V} → NeutralT V → NfT V
  canon   : ∀ {V} → CanonProp → NfT V
  Λ       : ∀ {V} → Type → Term (V , -Term) → NfT V

decode-NfT : ∀ {V} → NfT V → Term V
decode-NfT (neutral M) = decode-NeutralT M
decode-NfT (canon θ) = decode θ
decode-NfT (Λ A M) = ΛT A M

data NfP : Alphabet → Set where
  neutral : ∀ {V} → NeutralP V → NfP V

decode-NfP : ∀ {V} → NfP V → Proof V
decode-NfP (neutral δ) = decode-NeutralP δ
