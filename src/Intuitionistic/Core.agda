module Intuitionistic.Core where

open import Agda.Builtin.Equality using (_≡_)
open import Data.Bool.Base renaming (_∧_ to _&&_; _∨_ to _||_)
open import Data.Product using (_×_; ∃-syntax; ∃₂)
open import Data.Sum using (_⊎_)
open import Relation.Nullary.Negation using (¬_)

open import Function.Extra
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

interleaved mutual

  infix 2 _,_⊩_

  _,_⊩_ : {W F : Set} → KripkePreorder W F → W → intuitionistic F → Set

  infix 2 _,_⊮_

  _,_⊮_ : {W F : Set} → KripkePreorder W F → W → intuitionistic F → Set

  -----------------------------------------------------------------------
  -- Kripke semantics for intuitionistic logic

  𝔐 , w ⊩ atom x    = KripkePreorder.valuation 𝔐 w x ≡ true
  𝔐 , w ⊩ lhs ∧ rhs = (𝔐 , w ⊩ lhs) × (𝔐 , w ⊩ rhs)
  𝔐 , w ⊩ lhs ∨ rhs = (𝔐 , w ⊩ lhs) ⊎ (𝔐 , w ⊩ rhs)
  𝔐 , w ⊩ lhs ⇒ rhs = ∀ v → KripkePreorder.accesses 𝔐 w v → (𝔐 , v ⊩ lhs) → (𝔐 , v ⊩ rhs)
  𝔐 , w ⊩ `¬ p      = ∀ v → KripkePreorder.accesses 𝔐 w v → (𝔐 , v ⊮ p)

  -----------------------------------------------------------------------
  -- Definition of "doesn't force"

  𝔐 , w ⊮ atom x    = KripkePreorder.valuation 𝔐 w x ≡ false
  𝔐 , w ⊮ lhs ∧ rhs = (𝔐 , w ⊮ lhs) ⊎ (𝔐 , w ⊮ rhs)
  𝔐 , w ⊮ lhs ∨ rhs = (𝔐 , w ⊮ lhs) × (𝔐 , w ⊮ rhs)
  𝔐 , w ⊮ lhs ⇒ rhs = ∃[ v ] KripkePreorder.accesses 𝔐 w v × (𝔐 , v ⊩ lhs) × (𝔐 , v ⊮ rhs)
  𝔐 , w ⊮ `¬ p      = ∃[ v ] KripkePreorder.accesses 𝔐 w v × (𝔐 , v ⊩ p)

postulate
  monotoneAtom : {W F : Set} → {𝔐 : KripkePreorder W F} → {w v : W} → {a : F} →
                 KripkePreorder.accesses 𝔐 w v → (𝔐 , w ⊩ atom a) → (𝔐 , v ⊩ atom a)

  ¬⊩ : {W F : Set} → {𝔐 : KripkePreorder W F} → {w : W} → {a : intuitionistic F} →
        ¬ (𝔐 , w ⊩ a) ↔ (𝔐 , w ⊮ a)

-----------------------------------------------------------------------
-- A Kripke model forces a propositional formula iff it is forced in every world

infix 2 _,⊩_

_,⊩_ : {W F : Set} → KripkePreorder W F → intuitionistic F → Set _
𝔐 ,⊩ p = ∀ w → 𝔐 , w ⊩ p

-----------------------------------------------------------------------
-- A propositional formula is a tautology iff every Kripke model forces it

infix 2 ⊨_

⊨_ : {F : Set} → intuitionistic F → Set _
⊨_ {F = F} p = ∀ {W : Set} (𝔐 : KripkePreorder W F) → 𝔐 ,⊩ p

-----------------------------------------------------------------------
-- A Kripke model doesn't force a propositional formula iff there exists a world that doesn't force it

infix 2 _,⊮_

_,⊮_ : {W F : Set} → KripkePreorder W F → intuitionistic F → Set _
𝔐 ,⊮ p = ∃[ w ] (𝔐 , w ⊮ p)

-----------------------------------------------------------------------
-- A propositional formula is not a tautology iff there exists a Kripke model that doesn't force it

infix 2 ⊭_

⊭_ : {F : Set} → intuitionistic F → Set _
⊭_ {F = F} p = ∃₂ λ (W : Set) (𝔐 : KripkePreorder W F) → (𝔐 ,⊮ p)
