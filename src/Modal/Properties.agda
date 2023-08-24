module Modal.Properties where

open import Data.Empty using (⊥-elim)
open import Data.Product using (_×_; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Function.Base using (id)
open import Relation.Binary.Definitions
open import Relation.Nullary.Negation using (¬_; ¬∃⟶∀¬)

open import Classical
open import Extras
open import Modal.Base
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

MP : {w : W} → {a b : modal F} →
     𝔐 , w ⊩ a ⇒ b → 𝔐 , w ⊩ a → 𝔐 , w ⊩ b
MP ⊩a→b ⊩a = ⊩a→b ⊩a

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
-- Duality of necessity and possibility.

□⇔¬◇¬ : {a : modal F} → 𝔐 , w ⊩ □ a ⇔ `¬ ◇ `¬ a
□⇔¬◇¬ {𝔐 = 𝔐} {a = a} = ⊩⇔← 𝔐 (□ a) (`¬ ◇ `¬ a)
  ( (λ f → DNI _ λ v w↝v → DNI _ (f v w↝v))
  , (λ f v w↝v → DNE _ (DNE _ f v w↝v))
  )

◇⇔¬□¬ : {a : modal F} → 𝔐 , w ⊩ ◇ a ⇔ `¬ □ `¬ a
◇⇔¬□¬ {𝔐 = 𝔐} {a = a} = ⊩⇔← 𝔐 (◇ a) (`¬ □ `¬ a)
  ( id
  , id
  )

¬□⇔◇¬ : {a : modal F} → 𝔐 , w ⊩ `¬ □ a ⇔ ◇ `¬ a
¬□⇔◇¬ {𝔐 = 𝔐} {a = a} = ⊩⇔← 𝔐 (`¬ □ a) (◇ `¬ a)
  ( (λ f f¬¬ → f λ v w↝v → DNE _ (f¬¬ v w↝v))
  , λ ¬f¬¬ f → ¬f¬¬ λ v w↝v → DNI _ (f v w↝v)
  )

¬◇⇔□¬ : {a : modal F} → 𝔐 , w ⊩ `¬ ◇ a ⇔ □ `¬ a
¬◇⇔□¬ {𝔐 = 𝔐} {a = a} = ⊩⇔← 𝔐 (`¬ ◇ a) (□ `¬ a)
  ( DNE _
  , DNI _
  )

------------------------------------------------------------------------
-- Other properties w/o modalities

non-contradiction : {a : modal F} → 𝔐 , w ⊩ `¬ (a ∧ `¬ a)
non-contradiction = DNI _ λ ⊩a ⊩¬a → ⊩¬a ⊩a

contraposition : {a b : modal F} → 𝔐 , w ⊩ (a ⇒ b) ⇒ (`¬ b ⇒ `¬ a)
contraposition ⊩a→b ⊩¬b ⊩a = ⊩¬b (⊩a→b ⊩a)

-----------------------------------------------------------------------
-- Other properties w/ modalities

◇⇒◇◇ : (Reflexive (KripkeModel.accesses 𝔐) ⊎ Dense (KripkeModel.accesses 𝔐)) → {w : W} → {a : modal F} →
      𝔐 , w ⊩ ◇ a ⇒ ◇ ◇ a
◇⇒◇◇ {𝔐 = 𝔐} (inj₁ rfl) {w = w} {a = a} d with ⊩◇→ 𝔐 a d
... | v , w↝v , ⊩a = ⊩◇← 𝔐 (◇ a) (w , rfl , ⊩◇← 𝔐 a (v , w↝v , ⊩a))
-- ◇⇒◇◇ {𝔐 = 𝔐} (inj₁ rfl) {a = a} d with ⊩◇→ 𝔐 a d
-- ... | v , w↝v , ⊩a = ⊩◇← 𝔐 (◇ a) (v , w↝v , ⊩◇← 𝔐 a (v , rfl , ⊩a))
◇⇒◇◇ {𝔐 = 𝔐} (inj₂ dense) {w = w} {a = a} d with ⊩◇→ 𝔐 a d
... | v , w↝v , ⊩a with dense w↝v
... | (u , w↝u , u↝v) = ⊩◇← 𝔐 (◇ a) (u , w↝u , ⊩◇← 𝔐 a (v , u↝v , ⊩a))

◇◇⇒◇ : (Transitive (KripkeModel.accesses 𝔐) ⊎
        Discrete (KripkeModel.accesses 𝔐) × Reflexive (KripkeModel.accesses 𝔐)) → {w : W} → {a : modal F} →
       𝔐 , w ⊩ ◇ ◇ a ⇒ ◇ a
◇◇⇒◇ {𝔐 = 𝔐} (inj₁ trans) {a = a} dd with ⊩◇→ 𝔐 (◇ a) dd
... | v , w↝v , d with ⊩◇→ 𝔐 a d
... | u , v↝u , ⊩a = ⊩◇← 𝔐 a (u , trans w↝v v↝u , ⊩a)
◇◇⇒◇ {𝔐 = 𝔐} (inj₂ (discrete , rfl)) {a = a} dd with ⊩◇→ 𝔐 (◇ a) dd
... | v , w↝v , d with ⊩◇→ 𝔐 a d
... | u , v↝u , ⊩a rewrite discrete w↝v | discrete v↝u = ⊩◇← 𝔐 a (u , rfl , ⊩a)

quasi-regular : Skeletal (KripkeModel.accesses 𝔐) → {w : W} → {a b : modal F} →
                𝔐 , w ⊩ a ⇒ b → 𝔐 , w ⊩ □ a ⇒ □ b
quasi-regular (rfl , discrete) a→b □a v w↝v rewrite discrete w↝v = a→b (□a v rfl)

◇⇒ : Discrete (KripkeModel.accesses 𝔐) → {w : W} → {a : modal F} →
     𝔐 , w ⊩ ◇ a ⇒ a
◇⇒ {𝔐 = 𝔐} discrete {a = a} d with ⊩◇→ 𝔐 a d
... | v , w↝v , ⊩a rewrite discrete w↝v = ⊩a

⇒◇ : Reflexive (KripkeModel.accesses 𝔐) → {w : W} → {a : modal F} →
     𝔐 , w ⊩ a ⇒ ◇ a
⇒◇ {𝔐 = 𝔪} rfl {w = w} {a = a} ⊩a = ⊩◇← 𝔪 a (w , rfl , ⊩a)
