module Modal.Core where

open import Data.Bool.Base renaming (_∧_ to _&&_; _∨_ to _||_)
open import Data.List using (List)
open import Data.Product using (_×_; _,_; ∃-syntax)
open import Data.Sum using (_⊎_)
open import Relation.Binary.Core hiding (_⇒_; _⇔_)
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary.Negation using (¬_)

infix 7 `¬_ □_ ◇_
infixr 6 _∧_
infixr 5 _∨_
infixr 4 _⇒_
infixr 3 _⇔_

data modal (a : Set) : Set where
  atom : a → modal a
  `¬_   : modal a → modal a
  _∧_  : modal a → modal a → modal a
  _∨_  : modal a → modal a → modal a
  _⇒_  : modal a → modal a → modal a
  _⇔_  : modal a → modal a → modal a
  □_   : modal a → modal a
  ◇_   : modal a → modal a

_ : modal Bool
_ = `¬ □ ◇ (atom true ∧ atom false)

record KripkeFrame (W : Set) : Set₁ where
  constructor mkKF
  field
    accesses : Rel W _

record KripkeModel (W : Set) (F : Set) : Set₁ where
  constructor mkKM
  field
    accesses : Rel W _
    valuation : W → F → Bool

infix 2 _,_⊩_

_,_⊩_ : {W F : Set} → KripkeModel W F → W → modal F → Set
𝔐 , w ⊩ atom x = KripkeModel.valuation 𝔐 w x ≡ true
𝔐 , w ⊩ `¬ f = ¬ (𝔐 , w ⊩ f)
𝔐 , w ⊩ f ∧ g = (𝔐 , w ⊩ f) × (𝔐 , w ⊩ g)
𝔐 , w ⊩ f ∨ g = (𝔐 , w ⊩ f) ⊎ (𝔐 , w ⊩ g)
𝔐 , w ⊩ f ⇒ g = (𝔐 , w ⊩ f) → (𝔐 , w ⊩ g)
𝔐 , w ⊩ f ⇔ g = ((𝔐 , w ⊩ f) → (𝔐 , w ⊩ g)) × ((𝔐 , w ⊩ g) → (𝔐 , w ⊩ f))
𝔐 , w ⊩ □ f = ∀ v → KripkeModel.accesses 𝔐 w v → 𝔐 , v ⊩ f
𝔐 , w ⊩ ◇ f = ∃[ v ] (KripkeModel.accesses 𝔐 w v) × (𝔐 , v ⊩ f)

