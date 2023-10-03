module Extras where

open import Data.Empty using (⊥-elim)
open import Data.Product using (_×_; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Level using (Level)
open import Relation.Nullary.Negation using (¬_)

private
  variable
    ℓ : Level

infixr 1 _↔_

------------------------------------------------------------------------
-- Iff

_↔_ : Set ℓ → Set ℓ → Set ℓ
a ↔ b = (a → b) × (b → a)

------------------------------------------------------------------------
-- 3 out of 4 De Morgan laws are provable in constructive logic

¬⊎¬→¬× : {a b : Set ℓ} → ¬ a ⊎ ¬ b → ¬ (a × b)
¬⊎¬→¬× (inj₁ ¬a) (a , b) = ¬a a
¬⊎¬→¬× (inj₂ ¬b) (a , b) = ¬b b

¬⊎→¬×¬ : {a b : Set ℓ} → ¬ (a ⊎ b) → ¬ a × ¬ b
¬⊎→¬×¬ f = (λ a → f (inj₁ a)) , (λ b → f (inj₂ b))

¬×¬→¬⊎ : {a b : Set ℓ} → ¬ a × ¬ b → ¬ (a ⊎ b)
¬×¬→¬⊎ (¬a , ¬b) (inj₁ a) = ¬a a
¬×¬→¬⊎ (¬a , ¬b) (inj₂ b) = ¬b b

-----------------------------------------------------------------------
-- ⊥-introduction

DNI : (a : Set ℓ) → a → ¬ ¬ a
DNI a x ¬x = ¬x x
