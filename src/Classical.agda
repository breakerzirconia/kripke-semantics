module Classical where

open import Data.Empty using (⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Nullary.Negation using (¬_; contraposition)
open import Level using (Level)

open import Extras

private
  variable
    ℓ : Level

postulate
  DNE : (a : Set ℓ) → ¬ ¬ a → a

LEM : (a : Set ℓ) → a ⊎ ¬ a
LEM a = DNE (a ⊎ ¬ a) λ n → n (inj₂ λ x → n (inj₁ x))

Peirce : (a b : Set ℓ) → ((a → b) → a) → a
Peirce a b aba = DNE a λ na → na (aba λ x → ⊥-elim (na x))

Reductio : (a b : Set ℓ) → (¬ b → ¬ a) → (a → b)
Reductio a b ¬b→¬a x = DNE _ (contraposition ¬b→¬a (⊥-intro x))
