module Function.Extra where

open import Agda.Primitive using (_⊔_)
open import Data.Product using (_×_)

record Iff {a b} (A : Set a) (B : Set b) : Set (a ⊔ b) where
  field
    to : A → B
    from : B → A

infix 1 _↔_
_↔_ : ∀ {a b} → Set a → Set b → Set (a ⊔ b)
A ↔ B = Iff A B
