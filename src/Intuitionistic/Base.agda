module Intuitionistic.Base where

open import Data.Product using (_×_; _,_; ∃-syntax; ∃₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Nullary.Negation using (¬_; ¬∃⟶∀¬)

open import Data.Bool.Properties.Extra
open import Kripke.Semantics

-----------------------------------------------------------------------
-- Re-exporting the core definitions

open import Intuitionistic.Core public

-----------------------------------------------------------------------
-- The monotone property holds for arbitrary intuitionistic propositions.

monotone : {W F : Set} → {𝔐 : KripkePreorder W F} →
           {w v : W} → {a : intuitionistic F} →
           KripkePreorder.accesses 𝔐 w v → (𝔐 , w ⊩ a) → (𝔐 , v ⊩ a)
monotone {𝔐 = 𝔐} {a = atom x} w↝v w⊩atom = monotoneAtom {𝔐 = 𝔐} w↝v w⊩atom
monotone {a = lhs ∧ rhs} w↝v (w⊩lhs , w⊩rhs) =
  (monotone w↝v w⊩lhs) , (monotone w↝v w⊩rhs)
monotone {a = lhs ∨ rhs} w↝v (inj₁ w⊩lhs) = inj₁ (monotone w↝v w⊩lhs)
monotone {a = lhs ∨ rhs} w↝v (inj₂ w⊩rhs) = inj₂ (monotone w↝v w⊩rhs)
monotone {𝔐 = 𝔐} {a = lhs ⇒ rhs} w↝v w⊩⇒ u v↝u u⊩lhs =
  w⊩⇒ u (KripkePreorder.transitive 𝔐 w↝v v↝u) u⊩lhs
monotone {𝔐 = 𝔐} {a = `¬ a} w↝v w⊩¬ u v↝u = w⊩¬ u (KripkePreorder.transitive 𝔐 w↝v v↝u)
