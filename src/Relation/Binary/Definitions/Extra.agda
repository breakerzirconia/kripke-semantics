module Relation.Binary.Definitions.Extra where

open import Agda.Builtin.Equality using (_≡_)
open import Data.Product using (_×_; ∃-syntax)
open import Data.Sum using (_⊎_)
open import Level using (Level)
open import Relation.Binary.Core using (Rel)
open import Relation.Binary.Definitions using (Reflexive)
open import Relation.Nullary.Negation using (¬_)

private
  variable
    a ℓ : Level
    A : Set a

Dense : Rel A ℓ → Set _
Dense _R_ = ∀ {x z} → x R z → ∃[ y ] (x R y) × (y R z)

Serial : Rel A ℓ → Set _
Serial _R_ = ∀ x → ∃[ y ] x R y

Euclidean : Rel A ℓ → Set _
Euclidean _R_ = ∀ {x y z} → x R y → x R z → y R z

-- This property is given a name 'Weaklidean' as in 'weakened euclidean', since we don′t have
-- concrete information on the direction of the relation between both endpoints.

Weaklidean : Rel A ℓ → Set _
Weaklidean _R_ = ∀ {x y z} → x R y → x R z → (y R z) ⊎ (z R y)

Convergent : Rel A ℓ → Set _
Convergent _R_ = ∀ {x y z} → x R y → x R z → ∃[ w ] (y R w) × (z R w)

Discrete : Rel A ℓ → Set _
Discrete _R_ = ∀ {x y} → x R y → x ≡ y

Partial : Rel A ℓ → Set _
Partial _R_ = ∀ {x y z} → x R y → x R z → y ≡ z

Function : Rel A ℓ → Set _
Function _R_ = Serial _R_ × Partial _R_

Empty : Rel A ℓ → Set _
Empty _R_ = ∀ x y → ¬ (x R y)

-- This property is given a name 'Skeletal' in reference to skeletal categories.
-- Name subject to change.

Skeletal : Rel A ℓ → Set _
Skeletal _R_ = Reflexive _R_ × Discrete _R_
