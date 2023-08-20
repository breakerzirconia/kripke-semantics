module Classical where

open import Data.Empty using (⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Nullary.Negation using (¬_)
open import Level using (Level)

private
  variable
    ℓ : Level

postulate
  DNE : (a : Set ℓ) → ¬ ¬ a → a

LEM : (a : Set ℓ) → a ⊎ ¬ a
LEM a = DNE (a ⊎ ¬ a) λ n → n (inj₂ λ x → n (inj₁ x))

Peirce : (a b : Set ℓ) → ((a → b) → a) → a
Peirce a b aba = DNE a λ na → na (aba λ x → ⊥-elim (na x))

