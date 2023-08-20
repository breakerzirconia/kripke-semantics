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
-- Axioms of constructive logic

ax-K : {a b : modal F} → 𝔐 , w ⊩ a ⇒ b ⇒ a
ax-K ⊩a ⊩b = ⊩a

ax-S : {a b c : modal F} → 𝔐 , w ⊩ (a ⇒ b ⇒ c) ⇒ (a ⇒ b) ⇒ (a ⇒ c)
ax-S f g ⊩a = f ⊩a (g ⊩a)

ax-∧-intro : {a b : modal F} → 𝔐 , w ⊩ a ⇒ b ⇒ a ∧ b
ax-∧-intro ⊩a ⊩b = ⊩a , ⊩b

ax-∧-elimˡ : {a b : modal F} → 𝔐 , w ⊩ a ∧ b ⇒ a
ax-∧-elimˡ (⊩a , ⊩b) = ⊩a

ax-∧-elimʳ : {a b : modal F} → 𝔐 , w ⊩ a ∧ b ⇒ b
ax-∧-elimʳ (⊩a , ⊩b) = ⊩b

ax-∨-introˡ : {a b : modal F} → 𝔐 , w ⊩ a ⇒ a ∨ b
ax-∨-introˡ a = inj₁ a

ax-∨-introʳ : {a b : modal F} → 𝔐 , w ⊩ b ⇒ a ∨ b
ax-∨-introʳ a = inj₂ a

ax-∨-elim : {a b c : modal F} → 𝔐 , w ⊩ (a ⇒ c) ⇒ (b ⇒ c) ⇒ (a ∨ b ⇒ c)
ax-∨-elim f g (inj₁ ⊩a) = f ⊩a
ax-∨-elim f g (inj₂ ⊩b) = g ⊩b

ax-¬-intro : {a b c : modal F} → 𝔐 , w ⊩ (a ⇒ b) ⇒ (a ⇒ `¬ b) ⇒ `¬ a
ax-¬-intro f fn ⊩a = fn ⊩a (f ⊩a)

ax-¬-elim : {a b : modal F} → 𝔐 , w ⊩ a ⇒ `¬ a ⇒ b
ax-¬-elim ⊩a ⊩¬a = ⊥-elim (⊩¬a ⊩a)

------------------------------------------------------------------------
-- Double negation elimination

ax-DNE : {a : modal F} → 𝔐 , w ⊩ `¬ `¬ a ⇒ a
ax-DNE ⊩¬¬a = DNE _ ⊩¬¬a

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
non-contradiction (⊩a , ⊩¬a) = ⊩¬a ⊩a

ax-LEM : {a : modal F} → 𝔐 , w ⊩ a ∨ `¬ a
ax-LEM = LEM _

contraposition : {a b : modal F} → 𝔐 , w ⊩ (a ⇒ b) ⇒ (`¬ b ⇒ `¬ a)
contraposition ⊩a→b ⊩¬b ⊩a = ⊩¬b (⊩a→b ⊩a)

by-contradiction : {a b : modal F} → 𝔐 , w ⊩ (`¬ b ⇒ `¬ a) ⇒ (a ⇒ b)
by-contradiction {a = a} {b = b} f ⊩a with contraposition {_} {_} {_} {_} {`¬ b} {`¬ a} f
... | ~f = DNE _ (~f (⊥-intro ⊩a))

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

-- ¬⇒⇔∧¬ : {W F : Set} → {𝔐 : KripkeModel W F} → {w : W} → {f g : modal F} → 𝔐 , w ⊩ `¬ (f ⇒ g) ⇔ f ∧ `¬ g
-- ¬⇒⇔∧¬ {W} {F} {𝔐} {w} {f} {g} = => , <=
--  where
--    => : ¬ (𝔐 , w ⊩ f → 𝔐 , w ⊩ g) → (𝔐 , w ⊩ f) × ¬ (𝔐 , w ⊩ g)
--    => ¬f→g with LEM (𝔐 , w ⊩ f)
--    ... | inj₁ yes = yes , (λ ⊩g → ¬f→g λ _ → ⊩g)
--    ... | inj₂ no = {!!}
--    <= : (𝔐 , w ⊩ f) × ¬ (𝔐 , w ⊩ g) → ¬ (𝔐 , w ⊩ f → 𝔐 , w ⊩ g)
--    <= (⊩f , ¬⊩g) f→g = ¬⊩g (f→g ⊩f)
