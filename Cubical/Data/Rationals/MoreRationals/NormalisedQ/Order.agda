
module Cubical.Data.Rationals.MoreRationals.NormalisedQ.Order where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Transport
open import Cubical.Relation.Nullary
open import Cubical.Relation.Binary
open BinaryRelation
open import Cubical.Data.Nat as ℕ using (ℕ)
open import Cubical.Data.Nat.GCD
open import Cubical.Data.Nat.Coprime
open import Cubical.Data.Nat.Mod
open import Cubical.Data.Nat.Order as ℕ hiding (_≤ᵇ_; _≤_; _<_; _≥_; _>_; ≤Dec)

open import Cubical.Data.Bool using (Bool; false; true; if_then_else_)
open import Cubical.Data.Empty as ⊥ using (⊥)
open import Cubical.Data.Sigma
open import Cubical.Data.Int as ℤ renaming
  (_+_ to _ℤ+_; _-_ to _ℤ-_; -_ to -ℤ_; _·_ to _ℤ·_)
open import Cubical.Data.Int.Order as ℤ using ()

open import Cubical.Data.NatPlusOne
open import Cubical.Data.Int.MoreInts.QuoInt using () renaming
  (abs to abs'; ℤ→Int to Int→ℤ; Int→ℤ to ℤ→Int; ℤ→Int→ℤ to Int→ℤ→Int)
open import Cubical.Data.Rationals.MoreRationals.SigmaQ using (Quoℚ≡Sigmaℚ)
  renaming (ℚ to Sigmaℚ; isSetℚ to isSetSigmaℚ)
open import Cubical.Data.Rationals.MoreRationals.QuoQ using () renaming
  (ℚ to Quoℚ; discreteℚ to discreteQuoℚ; [_] to Quo[_]; Quoℚ≡ℚ to Quoℚ≡Rationalsℚ)
open import Cubical.Data.Rationals as Rationals
  using (_∼_; isEquivRel∼; path∼; isProp∼; ℕ₊₁→ℤ)
  renaming (ℚ to Rationalsℚ; [_] to Rationals[_])

open import Cubical.Data.Rationals.MoreRationals.NormalisedQ.Base
open import Cubical.Data.Rationals.MoreRationals.NormalisedQ.Properties

------------------------------------------
-- Essentials


-- put LEQ etc here...

---------------------------------------------
-- Rounding functions

∣_∣ :  (p : ℚ) → ℚ
∣ p@((pos n , d-1) , c) ∣ = p
∣ ((negsuc n , d-1) , c) ∣ = ((pos (ℕ.suc n)) , d-1) , c

-- Floor (round towards -∞)
floor : ℚ → ℤ
floor ((pos n , d-1) , c) = pos (quotient n / (ℕ.suc d-1))
floor ((negsuc n , d-1) , c) = negsuc (quotient n / ℕ.suc d-1)

-- Ceiling (round towards +∞)
ceiling : ℚ → ℤ
ceiling p = -ℤ floor (- p)

-- Truncate  (round towards 0)
truncate : ℚ → ℤ
truncate p with (≤Dec p 0ℚ)
... | yes p' = ceiling p
... | no ¬p = floor p

-- Round (to nearest integer)
round : ℚ → ℤ
round p with (≤Dec p 0ℚ)
... | yes p' = ceiling (p - ½)
... | no ¬p = floor (p + ½)

-- Extra notations  ⌊ ⌋ floor,  ⌈ ⌉ ceiling,  [ ] truncate
syntax floor p = ⌊ p ⌋
syntax ceiling p = ⌈ p ⌉
syntax truncate p = ⌊ p ⌉
