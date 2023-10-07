module Intuitionistic.Properties where

open import Agda.Builtin.Unit
open import Data.Bool.Base renaming (_∧_ to _&&_; _∨_ to _||_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product using (_×_; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Function.Base using (id; _∘₂_)
open import Relation.Binary.Definitions
open import Relation.Nullary.Negation using (¬_; ¬∃⟶∀¬)

open import Classical
open import Extras
open import Function.Extra
open import Intuitionistic.Base
open import Kripke.Semantics
open import Relation.Binary.Definitions.Extra

variable
  W F : Set
  𝔐 : KripkePreorder W F
  w : W

-----------------------------------------------------------------------
-- Axioms of intuitionistic logic

⊩K : {a b : intuitionistic F} → 𝔐 , w ⊩ a ⇒ b ⇒ a
⊩K v w↝v v⊩a u v↝u u⊩b = monotone v↝u v⊩a

⊩S : {a b c : intuitionistic F} → 𝔐 , w ⊩ (a ⇒ b ⇒ c) ⇒ (a ⇒ b) ⇒ (a ⇒ c)
⊩S {𝔐 = 𝔐} v w↝v v⊩a⇒b⇒c u v↝u u⊩a⇒b x u↝x x⊩a =
  v⊩a⇒b⇒c x (KripkePreorder.transitive 𝔐 v↝u u↝x) x⊩a x (KripkePreorder.reflexive 𝔐) (u⊩a⇒b x u↝x x⊩a)

⊩∧-intro : {a b : intuitionistic F} → 𝔐 , w ⊩ a ⇒ b ⇒ a ∧ b
⊩∧-intro v w↝v v⊩a u v↝u u⊩b = (monotone v↝u v⊩a) , u⊩b

⊩∧-elimˡ : {a b : intuitionistic F} → 𝔐 , w ⊩ a ∧ b ⇒ a
⊩∧-elimˡ v w↝v (v⊩a , v⊩b) = v⊩a

⊩∧-elimʳ : {a b : intuitionistic F} → 𝔐 , w ⊩ a ∧ b ⇒ b
⊩∧-elimʳ v w↝v (v⊩a , v⊩b) = v⊩b

⊩∨-introˡ : {a b : intuitionistic F} → 𝔐 , w ⊩ a ⇒ a ∨ b
⊩∨-introˡ v w↝v v⊩a = inj₁ v⊩a

⊩∨-introʳ : {a b : intuitionistic F} → 𝔐 , w ⊩ b ⇒ a ∨ b
⊩∨-introʳ v w↝v v⊩b = inj₂ v⊩b

⊩∨-elim : {a b c : intuitionistic F} → 𝔐 , w ⊩ (a ⇒ c) ⇒ (b ⇒ c) ⇒ (a ∨ b ⇒ c)
⊩∨-elim {𝔐 = 𝔐} v w↝v v⊩a⇒c u v↝u u⊩b⇒c x u↝x (inj₁ x⊩a) =
  v⊩a⇒c x (KripkePreorder.transitive 𝔐 v↝u u↝x) x⊩a
⊩∨-elim {𝔐 = 𝔐} v w↝v v⊩a⇒c u v↝u u⊩b⇒c x u↝x (inj₂ x⊩b) =
  u⊩b⇒c x u↝x x⊩b

⊩¬-intro : {a b c : intuitionistic F} → 𝔐 , w ⊩ (a ⇒ b) ⇒ (a ⇒ `¬ b) ⇒ `¬ a
⊩¬-intro {𝔐 = 𝔐} v w↝v v⊩a⇒b u v↝u u⊩a⇒¬b x u↝x {- x⊩a -} = Iff.to ¬⊩
  λ x⊩a → Iff.from ¬⊩ (u⊩a⇒¬b x u↝x x⊩a x (KripkePreorder.reflexive 𝔐)) (v⊩a⇒b x (KripkePreorder.transitive 𝔐 v↝u u↝x) x⊩a)

⊩¬-elim : {a b : intuitionistic F} → 𝔐 , w ⊩ a ⇒ `¬ a ⇒ b
⊩¬-elim {𝔐 = 𝔐} v w↝v v⊩a u v↝u u⊩¬a =
  ⊥-elim (Iff.from ¬⊩ (u⊩¬a u (KripkePreorder.reflexive 𝔐)) (monotone v↝u v⊩a))

-----------------------------------------------------------------------
-- Axioms from the BCKW system, but without K

⊩flip : {a b c : intuitionistic F} → 𝔐 , w ⊩ (a ⇒ b ⇒ c) ⇒ (b ⇒ a ⇒ c)
⊩flip {𝔐 = 𝔐} v w↝v v⊩a⇒b⇒c u v↝u u⊩b x u↝x x⊩a =
  v⊩a⇒b⇒c x (KripkePreorder.transitive 𝔐 v↝u u↝x) x⊩a x (KripkePreorder.reflexive 𝔐) (monotone u↝x u⊩b)

⊩∘ : {a b c : intuitionistic F} → 𝔐 , w ⊩ (b ⇒ c) ⇒ (a ⇒ b) ⇒ (a ⇒ c)
⊩∘ {𝔐 = 𝔐} v w↝v v⊩b⇒c u v↝u u⊩a⇒b x u↝x x⊩a =
  v⊩b⇒c x (KripkePreorder.transitive 𝔐 v↝u u↝x) (u⊩a⇒b x u↝x x⊩a)

⊩join : {a b : intuitionistic F} → 𝔐 , w ⊩ (a ⇒ a ⇒ b) ⇒ (a ⇒ b)
⊩join {𝔐 = 𝔐} v w↝v v⊩a⇒a⇒b u v↝u u⊩a =
  v⊩a⇒a⇒b u v↝u u⊩a u (KripkePreorder.reflexive 𝔐) u⊩a

-----------------------------------------------------------------------
-- DNE is not a tautology

⊭DNE : {x : F} → ⊭ `¬ `¬ (atom x) ⇒ atom x
⊭DNE = Two , 𝔪 , A , (B , tt , {!   !} , {!   !})
  where
    data Two : Set where A B : Two

    𝔪 : KripkePreorder Two F
    𝔪 = mkKP (λ{ A A → ⊤
                ; A B → ⊤
                ; B A → ⊥
                ; B B → ⊤ })
              (λ{ A f → false
                ; B f → {!   !}})
              (λ{ {A} → tt
                ; {B} → tt })
              (λ{ {A} {A} {A} p q → tt
                ; {A} {A} {B} p q → tt
                ; {A} {B} {B} p q → tt
                ; {B} {B} {B} p q → tt })
