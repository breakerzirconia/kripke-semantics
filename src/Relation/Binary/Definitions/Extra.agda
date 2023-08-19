module Relation.Binary.Definitions.Extra where

open import Agda.Builtin.Equality
open import Data.Product
open import Level
open import Relation.Binary.Core
open import Relation.Binary.Definitions

private
  variable
    a ℓ : Level
    A : Set a

Serial : Rel A ℓ → Set _
Serial _R_ = ∀ x → ∃[ y ] x R y

Euclidean : Rel A ℓ → Set _
Euclidean _R_ = ∀ {x y z} → x R y → x R z → y R z

Dense : Rel A ℓ → Set _
Dense _R_ = ∀ {x z} → x R z → ∃[ y ] (x R y) × (y R z)

Discrete : Rel A ℓ → Set _
Discrete _R_ = ∀ {x y} → x R y → x ≡ y

Partial : Rel A ℓ → Set _
Partial _R_ = ∀ {x y z} → x R y → x R z → y ≡ z
