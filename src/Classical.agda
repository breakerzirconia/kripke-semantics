module Classical where

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product using (_×_; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Nullary.Negation using (¬_; contraposition)
open import Level using (Level)

open import Extras

private
  variable
    ℓ : Level

-----------------------------------------------------------------------
-- The enablers of classical logic

postulate
  DNE : (a : Set ℓ) → ¬ ¬ a → a

LEM : (a : Set ℓ) → a ⊎ ¬ a
LEM a = DNE (a ⊎ ¬ a) λ n → n (inj₂ λ x → n (inj₁ x))

Peirce : (a b : Set ℓ) → ((a → b) → a) → a
Peirce a b aba = DNE a λ na → na (aba λ x → ⊥-elim (na x))

-----------------------------------------------------------------------
-- Properties

classical-→ : {a b : Set ℓ} → (a → b) → ¬ a ⊎ b
classical-→ {a = a} {b = b} f with LEM a
classical-→ f | inj₁ a = inj₂ (f a)
classical-→ f | inj₂ ¬a = inj₁ ¬a

classical-demorgan-¬× : {a b : Set ℓ} → ¬ (a × b) → ¬ a ⊎ ¬ b
classical-demorgan-¬× {a = a} {b = b} f with LEM a
classical-demorgan-¬× f | inj₁ a = inj₂ λ b → f (a , b)
classical-demorgan-¬× f | inj₂ ¬a = inj₁ ¬a

classical-¬→ : {a b : Set ℓ} → ¬ (a → b) → a × ¬ b
classical-¬→ {a = a} {b = b} f with LEM a | LEM b
classical-¬→ f | inj₁ a | inj₁ b = a , λ b → f (λ _ → b)
classical-¬→ f | inj₁ a | inj₂ ¬b = a , ¬b
classical-¬→ f | inj₂ ¬a | inj₁ b = ⊥-elim (f (λ _ → b)) , λ b → f (λ _ → b)
--                                  ⊥-elim (f (λ a → ⊥-elim (¬a a)))
classical-¬→ f | inj₂ ¬a | inj₂ ¬b = ⊥-elim (f (λ a → ⊥-elim (¬a a))) , ¬b

classical-by-contradiction : {a b : Set ℓ} → (¬ b → ¬ a) → (a → b)
classical-by-contradiction f a = DNE _ (contraposition f (⊥-intro a))
