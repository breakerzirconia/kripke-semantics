module Modal.Properties where

open import Data.Empty using (⊥-elim)
open import Data.Product using (_×_; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Function.Base using (id; _∘₂_)
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

⊩K : {a b : modal F} → 𝔐 , w ⊩ a ⇒ b ⇒ a
⊩K ⊩a ⊩b = ⊩a

⊩S : {a b c : modal F} → 𝔐 , w ⊩ (a ⇒ b ⇒ c) ⇒ (a ⇒ b) ⇒ (a ⇒ c)
⊩S f g ⊩a = f ⊩a (g ⊩a)

⊩reductio : {a b : modal F} → 𝔐 , w ⊩ (`¬ b ⇒ `¬ a) ⇒ (a ⇒ b)
⊩reductio = Reductio _ _

MP : {w : W} → {a b : modal F} →
     𝔐 , w ⊩ a ⇒ b → 𝔐 , w ⊩ a → 𝔐 , w ⊩ b
MP ⊩a→b ⊩a = ⊩a→b ⊩a

------------------------------------------------------------------------
-- Axioms of constructive logic

⊩∧-intro : {a b : modal F} → 𝔐 , w ⊩ a ⇒ b ⇒ a ∧ b
⊩∧-intro ⊩a ⊩b f = f ⊩a ⊩b

⊩∧-elimˡ : {a b : modal F} → 𝔐 , w ⊩ a ∧ b ⇒ a
⊩∧-elimˡ f = DNE _ λ ⊩¬a → f λ ⊩a ⊩b → ⊩¬a ⊩a

⊩∧-elimʳ : {a b : modal F} → 𝔐 , w ⊩ a ∧ b ⇒ b
⊩∧-elimʳ f = DNE _ λ ⊩¬b → f λ ⊩a ⊩b → ⊩¬b ⊩b

⊩∨-introˡ : {a b : modal F} → 𝔐 , w ⊩ a ⇒ a ∨ b
⊩∨-introˡ ⊩a ⊩¬a = ⊥-elim (⊩¬a ⊩a)

⊩∨-introʳ : {a b : modal F} → 𝔐 , w ⊩ b ⇒ a ∨ b
⊩∨-introʳ ⊩b ⊩¬a = ⊩b

⊩∨-elim : {a b c : modal F} → 𝔐 , w ⊩ (a ⇒ c) ⇒ (b ⇒ c) ⇒ (a ∨ b ⇒ c)
⊩∨-elim {𝔐 = 𝔐} {w = w} {a = a} f g ¬a→b with LEM (𝔐 , w ⊩ a)
... | inj₁ ⊩a = f ⊩a
... | inj₂ ⊩¬a = g (¬a→b ⊩¬a)

⊩¬-intro : {a b c : modal F} → 𝔐 , w ⊩ (a ⇒ b) ⇒ (a ⇒ `¬ b) ⇒ `¬ a
⊩¬-intro f fn ⊩a = fn ⊩a (f ⊩a)

⊩¬-elim : {a b : modal F} → 𝔐 , w ⊩ a ⇒ `¬ a ⇒ b
⊩¬-elim ⊩a ⊩¬a = ⊥-elim (⊩¬a ⊩a)

------------------------------------------------------------------------
-- Classical axioms

⊩LEM : {a : modal F} → 𝔐 , w ⊩ a ∨ `¬ a
⊩LEM ⊩¬a = ⊩¬a

⊩DNE : {a : modal F} → 𝔐 , w ⊩ `¬ `¬ a ⇒ a
⊩DNE = DNE _

⊩Peirce : {a b : modal F} → 𝔐 , w ⊩ ((a ⇒ b) ⇒ a) ⇒ a
⊩Peirce = Peirce _ _

------------------------------------------------------------------------
-- Axioms from the BCKW system, but without K

⊩flip : {a b c : modal F} → 𝔐 , w ⊩ (a ⇒ b ⇒ c) ⇒ (b ⇒ a ⇒ c)
⊩flip f ⊩b ⊩a = f ⊩a ⊩b

infixr 9 _⊩∘_
_⊩∘_ : {a b c : modal F} → 𝔐 , w ⊩ (b ⇒ c) ⇒ (a ⇒ b) ⇒ (a ⇒ c)
_⊩∘_ g f ⊩a = g (f ⊩a)

⊩join : {a b : modal F} → 𝔐 , w ⊩ (a ⇒ a ⇒ b) ⇒ (a ⇒ b)
⊩join f ⊩a = f ⊩a ⊩a

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

-----------------------------------------------------------------------
-- Distribution of necessity over conjunction.

□-distrib-∧⃗ : {w : W} → {a b : modal F} →
               𝔐 , w ⊩ □ (a ∧ b) ⇒ □ a ∧ □ b
□-distrib-∧⃗ {𝔐 = 𝔐} {a = a} {b = b} □∧ = ⊩∧← 𝔐 (□ a) (□ b) (⊩∧-elimˡ ∘₂ □∧ , ⊩∧-elimʳ ∘₂ □∧)

□-distrib-∧⃖ : {w : W} → {a b : modal F} →
               𝔐 , w ⊩ □ a ∧ □ b ⇒ □ (a ∧ b)
□-distrib-∧⃖ {𝔐 = 𝔐} {w} {a} {b} □∧□ v w↝v with ⊩∧→ 𝔐 (□ a) (□ b) □∧□
... | □a , □b = ⊩∧← 𝔐 a b ((□a v w↝v) , (□b v w↝v))

□-distrib-∧ : {w : W} → {a b : modal F} →
              𝔐 , w ⊩ □ (a ∧ b) ⇔ □ a ∧ □ b
□-distrib-∧ {𝔐 = 𝔐} {a = a} {b = b} = ⊩⇔← 𝔐 (□ (a ∧ b)) (□ a ∧ □ b) (□-distrib-∧⃗ , □-distrib-∧⃖)

------------------------------------------------------------------------
-- Distribution of possibility over disjunction.

◇-distrib-∨⃗ : {w : W} → {a b : modal F} →
               𝔐 , w ⊩ ◇ (a ∨ b) ⇒ ◇ a ∨ ◇ b
◇-distrib-∨⃗ {𝔐 = 𝔐} {a = a} {b = b} ◇∨ with ⊩◇→ 𝔐 (a ∨ b) ◇∨
... | v , w↝v , ⊩a∨b with ⊩∨→ 𝔐 a b ⊩a∨b
... | inj₁ ⊩a = ⊩∨← 𝔐 (◇ a) (◇ b) (inj₁ (⊩◇← 𝔐 a (v , w↝v , ⊩a)))
... | inj₂ ⊩b = ⊩∨← 𝔐 (◇ a) (◇ b) (inj₂ (⊩◇← 𝔐 b (v , w↝v , ⊩b)))

◇-distrib-∨⃖ : {w : W} → {a b : modal F} →
               𝔐 , w ⊩ ◇ a ∨ ◇ b ⇒ ◇ (a ∨ b)
◇-distrib-∨⃖ {𝔐 = 𝔐} {a = a} {b = b} ◇∨◇ with ⊩∨→ 𝔐 (◇ a) (◇ b) ◇∨◇
◇-distrib-∨⃖ {𝔐 = 𝔐} {a = a} {b = b} ◇∨◇ | inj₁ ◇a with ⊩◇→ 𝔐 a ◇a
... | v , w↝v , ⊩a = ⊩◇← 𝔐 (a ∨ b) (v , w↝v , ⊩∨← 𝔐 a b (inj₁ ⊩a))
◇-distrib-∨⃖ {𝔐 = 𝔐} {a = a} {b = b} ◇∨◇ | inj₂ ◇b with ⊩◇→ 𝔐 b ◇b
... | v , w↝v , ⊩b = ⊩◇← 𝔐 (a ∨ b) (v , w↝v , ⊩∨← 𝔐 a b (inj₂ ⊩b))

◇-distrib-∨ : {w : W} → {a b : modal F} →
              𝔐 , w ⊩ ◇ (a ∨ b) ⇔ ◇ a ∨ ◇ b
◇-distrib-∨ {𝔐 = 𝔐} {a = a} {b = b} = ⊩⇔← 𝔐 (◇ (a ∨ b)) (◇ a ∨ ◇ b) (◇-distrib-∨⃗ , ◇-distrib-∨⃖)

------------------------------------------------------------------------
-- Distributing necessity over implication can flip the modality.

□-flip-→ : {w : W} → {a b : modal F} →
           𝔐 , w ⊩ □ (a ⇒ b) ⇒ (◇ a ⇒ ◇ b)
□-flip-→ {𝔐 = 𝔐} {a = a} {b = b} ⊩□a⇒b ⊩◇a with ⊩◇→ 𝔐 a ⊩◇a
... | v , w↝v , ⊩a = ⊩◇← 𝔐 b (v , w↝v , ⊩□a⇒b v w↝v ⊩a)

------------------------------------------------------------------------
-- Other properties w/o modalities

non-contradiction : {a : modal F} → 𝔐 , w ⊩ `¬ (a ∧ `¬ a)
non-contradiction = DNI _ λ ⊩a ⊩¬a → ⊩¬a ⊩a

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

quasi-regular-□ : Skeletal (KripkeModel.accesses 𝔐) → {w : W} → {a b : modal F} →
                  𝔐 , w ⊩ a ⇒ b → 𝔐 , w ⊩ □ a ⇒ □ b
quasi-regular-□ (rfl , discrete) ⊩a⇒b □a v w↝v rewrite discrete w↝v = ⊩a⇒b (□a v rfl)

quasi-regular-◇ : Skeletal (KripkeModel.accesses 𝔐) → {w : W} → {a b : modal F} →
                  𝔐 , w ⊩ a ⇒ b → 𝔐 , w ⊩ ◇ a ⇒ ◇ b
quasi-regular-◇ {𝔐 = 𝔐} (rfl , discrete) {a = a} {b = b} ⊩a⇒b ◇a with ⊩◇→ 𝔐 a ◇a
... | v , w↝v , ⊩a rewrite discrete w↝v = ⊩◇← 𝔐 b (v , rfl , ⊩a⇒b ⊩a)

◇⇒ : Discrete (KripkeModel.accesses 𝔐) → {w : W} → {a : modal F} →
     𝔐 , w ⊩ ◇ a ⇒ a
◇⇒ {𝔐 = 𝔐} discrete {a = a} d with ⊩◇→ 𝔐 a d
... | v , w↝v , ⊩a rewrite discrete w↝v = ⊩a

⇒◇ : Reflexive (KripkeModel.accesses 𝔐) → {w : W} → {a : modal F} →
     𝔐 , w ⊩ a ⇒ ◇ a
⇒◇ {𝔐 = 𝔐} rfl {w = w} {a = a} ⊩a = ⊩◇← 𝔐 a (w , rfl , ⊩a)
