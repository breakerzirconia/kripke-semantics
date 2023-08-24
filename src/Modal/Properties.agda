module Modal.Properties where

open import Data.Empty using (⊥-elim)
open import Data.Product using (_×_; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.Definitions
open import Relation.Nullary.Negation using (¬_)

open import Classical
open import Extras
open import Modal.Core
open import Relation.Binary.Definitions.Extra

variable
  W F : Set
  𝔐 : KripkeModel W F
  w : W

------------------------------------------------------------------------
-- Axioms of the CN-logic

ax-K : {a b : modal F} → 𝔐 , w ⊩ a ⇒ b ⇒ a
ax-K ⊩a ⊩b = ⊩a

ax-S : {a b c : modal F} → 𝔐 , w ⊩ (a ⇒ b ⇒ c) ⇒ (a ⇒ b) ⇒ (a ⇒ c)
ax-S f g ⊩a = f ⊩a (g ⊩a)

ax-reductio : {a b : modal F} → 𝔐 , w ⊩ (`¬ b ⇒ `¬ a) ⇒ (a ⇒ b)
ax-reductio = Reductio _ _

------------------------------------------------------------------------
-- Axioms of constructive logic

ax-∧-intro : {a b : modal F} → 𝔐 , w ⊩ a ⇒ b ⇒ a ∧ b
ax-∧-intro ⊩a ⊩b f = f ⊩a ⊩b

ax-∧-elimˡ : {a b : modal F} → 𝔐 , w ⊩ a ∧ b ⇒ a
ax-∧-elimˡ f = DNE _ λ ⊩¬a → f λ ⊩a ⊩b → ⊩¬a ⊩a

ax-∧-elimʳ : {a b : modal F} → 𝔐 , w ⊩ a ∧ b ⇒ b
ax-∧-elimʳ f = DNE _ λ ⊩¬b → f λ ⊩a ⊩b → ⊩¬b ⊩b

ax-∨-introˡ : {a b : modal F} → 𝔐 , w ⊩ a ⇒ a ∨ b
ax-∨-introˡ ⊩a ⊩¬a = ⊥-elim (⊩¬a ⊩a)

ax-∨-introʳ : {a b : modal F} → 𝔐 , w ⊩ b ⇒ a ∨ b
ax-∨-introʳ ⊩b ⊩¬a = ⊩b

ax-∨-elim : {a b c : modal F} → 𝔐 , w ⊩ (a ⇒ c) ⇒ (b ⇒ c) ⇒ (a ∨ b ⇒ c)
ax-∨-elim {𝔐 = 𝔐} {w = w} {a = a} f g ¬a→b with LEM (𝔐 , w ⊩ a)
... | inj₁ ⊩a = f ⊩a
... | inj₂ ⊩¬a = g (¬a→b ⊩¬a)

ax-¬-intro : {a b c : modal F} → 𝔐 , w ⊩ (a ⇒ b) ⇒ (a ⇒ `¬ b) ⇒ `¬ a
ax-¬-intro f fn ⊩a = fn ⊩a (f ⊩a)

ax-¬-elim : {a b : modal F} → 𝔐 , w ⊩ a ⇒ `¬ a ⇒ b
ax-¬-elim ⊩a ⊩¬a = ⊥-elim (⊩¬a ⊩a)

------------------------------------------------------------------------
-- Classical axioms

ax-LEM : {a : modal F} → 𝔐 , w ⊩ a ∨ `¬ a
ax-LEM ⊩¬a = ⊩¬a

ax-DNE : {a : modal F} → 𝔐 , w ⊩ `¬ `¬ a ⇒ a
ax-DNE = DNE _

------------------------------------------------------------------------
-- Axioms from the BCKW system, but without K

ax-flip : {a b c : modal F} → 𝔐 , w ⊩ (a ⇒ b ⇒ c) ⇒ (b ⇒ a ⇒ c)
ax-flip f ⊩b ⊩a = f ⊩a ⊩b

ax-composition : {a b c : modal F} → 𝔐 , w ⊩ (b ⇒ c) ⇒ (a ⇒ b) ⇒ (a ⇒ c)
ax-composition g f ⊩a = g (f ⊩a)

ax-join : {a b : modal F} → 𝔐 , w ⊩ (a ⇒ a ⇒ b) ⇒ (a ⇒ b)
ax-join f ⊩a = f ⊩a ⊩a

------------------------------------------------------------------------
-- Properties of the necessity and possibility modalities.

□⇔¬◇¬ : {a : modal F} → 𝔐 , w ⊩ □ a ⇔ `¬ ◇ `¬ a
□⇔¬◇¬ = => , <=
  where
    => : {a : modal F} → 𝔐 , w ⊩ □ a ⇒ `¬ ◇ `¬ a
    => □a (v , w↝v , ⊩¬a) = ⊩¬a (□a v w↝v)
    <= : {a : modal F} → 𝔐 , w ⊩ `¬ ◇ `¬ a ⇒ □ a
    <= nx v w↝v = {!!} -- Properties from classical logic are needed here.

◇⇔¬□¬ : {a : modal F} → 𝔐 , w ⊩ ◇ a ⇔ `¬ □ `¬ a
◇⇔¬□¬ = => , <=
  where
    => : {a : modal F} → 𝔐 , w ⊩ ◇ a ⇒ `¬ □ `¬ a
    => (v , w↝v , ⊩a) f = f v w↝v ⊩a
    <= : {a : modal F} → 𝔐 , w ⊩ `¬ □ `¬ a ⇒ ◇ a
    <= f = {!!} -- Properties from classical logic are needed here.

¬□⇔◇¬ : {a : modal F} → 𝔐 , w ⊩ `¬ □ a ⇔ ◇ `¬ a
¬□⇔◇¬ = => , <=
  where
    => : {a : modal F} → 𝔐 , w ⊩ `¬ □ a ⇒ ◇ `¬ a
    => f = {!!} -- Properties from classical logic are needed here.
    <= : {a : modal F} → 𝔐 , w ⊩ ◇ `¬ a ⇒ `¬ □ a
    <= (v , w↝v , ⊩¬a) f = ⊩¬a (f v w↝v)

¬◇⇔□¬ : {a : modal F} → 𝔐 , w ⊩ `¬ ◇ a ⇔ □ `¬ a
¬◇⇔□¬ = => , <=
  where
    => : {a : modal F} → 𝔐 , w ⊩ `¬ ◇ a ⇒ □ `¬ a
    => = {!!} -- Properties from classical logic are needed here.
    <= : {a : modal F} → 𝔐 , w ⊩ □ `¬ a ⇒ `¬ ◇ a
    <= f (v , w↝v , ⊩a) = f v w↝v ⊩a

------------------------------------------------------------------------
-- Other properties w/o modalities

non-contradiction : {a : modal F} → 𝔐 , w ⊩ `¬ (a ∧ `¬ a)
non-contradiction = ⊥-intro λ ⊩a ⊩¬a → ⊩¬a ⊩a

contraposition : {a b : modal F} → 𝔐 , w ⊩ (a ⇒ b) ⇒ (`¬ b ⇒ `¬ a)
contraposition ⊩a→b ⊩¬b ⊩a = ⊩¬b (⊩a→b ⊩a)

-----------------------------------------------------------------------
-- Other properties w/ modalities

◇⇒◇◇ : (Reflexive (KripkeModel.accesses 𝔐) ⊎ Dense (KripkeModel.accesses 𝔐)) → {w : W} → {a : modal F} →
      𝔐 , w ⊩ ◇ a ⇒ ◇ ◇ a
◇⇒◇◇ (inj₁ rfl) {w = w} (v , w↝v , ⊩a) = w , rfl , v , w↝v , ⊩a
-- huh (inj₁ rfl) {w = w} (v , w↝v , ⊩a) = v , w↝v , v , rfl , ⊩a
◇⇒◇◇ (inj₂ dense) {w = w} (v , w↝v , ⊩a) with dense w↝v
... | (u , w↝u , u↝v) = u , w↝u , v , u↝v , ⊩a

◇◇⇒◇ : (Transitive (KripkeModel.accesses 𝔐) ⊎
        Discrete (KripkeModel.accesses 𝔐) × Reflexive (KripkeModel.accesses 𝔐)) → {w : W} → {a : modal F} →
       𝔐 , w ⊩ ◇ ◇ a ⇒ ◇ a
◇◇⇒◇ (inj₁ trans) (v , w↝v , u , v↝u , ⊩a) = u , trans w↝v v↝u , ⊩a
◇◇⇒◇ (inj₂ (discrete , rfl)) (v , w↝v , u , v↝u , ⊩a) rewrite discrete w↝v | discrete v↝u = u , rfl , ⊩a

