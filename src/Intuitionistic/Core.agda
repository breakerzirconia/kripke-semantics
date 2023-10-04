module Intuitionistic.Core where

open import Agda.Builtin.Equality using (_≡_)
open import Data.Bool.Base renaming (_∧_ to _&&_; _∨_ to _||_)
open import Data.Product using (_×_)
open import Data.Sum using (_⊎_)
open import Relation.Nullary.Negation using (¬_)

open import Kripke.Semantics

-----------------------------------------------------------------------
-- The 'intuitionistic' datatype

infix 7 `¬_
infixr 6 _∧_
infixr 5 _∨_
infixr 4 _⇒_
infixr 3 _⇔_

data intuitionistic (a : Set) : Set where
  atom : a → intuitionistic a
  _∧_  : intuitionistic a → intuitionistic a → intuitionistic a
  _∨_  : intuitionistic a → intuitionistic a → intuitionistic a
  _⇒_  : intuitionistic a → intuitionistic a → intuitionistic a
  `¬_  : intuitionistic a → intuitionistic a

_⇔_ : {a : Set} → intuitionistic a → intuitionistic a → intuitionistic a
a ⇔ b = (a ⇒ b) ∧ (b ⇒ a)

-----------------------------------------------------------------------
-- Kripke semantics for intuitionistic logic

infix 2 _,_⊩_

_,_⊩_ : {W F : Set} → KripkePreorder W F → W → intuitionistic F → Set
𝔐 , w ⊩ atom x    = KripkePreorder.valuation 𝔐 w x ≡ true
𝔐 , w ⊩ lhs ∧ rhs = (𝔐 , w ⊩ lhs) × (𝔐 , w ⊩ rhs)
𝔐 , w ⊩ lhs ∨ rhs = (𝔐 , w ⊩ lhs) ⊎ (𝔐 , w ⊩ rhs)
𝔐 , w ⊩ lhs ⇒ rhs = ∀ v → KripkePreorder.accesses 𝔐 w v → (𝔐 , v ⊩ lhs) → (𝔐 , v ⊩ rhs)
𝔐 , w ⊩ `¬ p      = ∀ v → KripkePreorder.accesses 𝔐 w v → ¬ (𝔐 , v ⊩ p)

postulate
  monotone : {W F : Set} → {𝔐 : KripkePreorder W F} →
             {w v : W} → {a : intuitionistic F} →
             KripkePreorder.accesses 𝔐 w v → (𝔐 , w ⊩ a) → (𝔐 , v ⊩ a)
