module Kripke.Semantics where

open import Data.Bool.Base using (Bool)
open import Relation.Binary.Core
open import Relation.Binary.Definitions

-----------------------------------------------------------------------
-- Kripke frame and Kripke model

record KripkeFrame (W : Set) : Set₁ where
  constructor mkKF
  field
    accesses : Rel W _

record KripkeModel (W : Set) (F : Set) : Set₁ where
  constructor mkKM
  field
    accesses : Rel W _
    valuation : W → F → Bool

record KripkePreorder (W : Set) (F : Set) : Set₁ where
  constructor mkKP
  field
    accesses : Rel W _
    valuation : W → F → Bool
    reflexive : Reflexive accesses
    transitive : Transitive accesses
