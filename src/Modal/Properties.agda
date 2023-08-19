module Modal.Properties where

open import Data.Empty using (⊥-elim)
open import Data.Product using (_,_)
open import Data.Sum using (inj₁; inj₂)
open import Relation.Nullary.Negation using (¬_)

open import Classical
open import Modal.Core

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
-- Other properties

non-contradiction : {a : modal F} → 𝔐 , w ⊩ `¬ (a ∧ `¬ a)
non-contradiction = λ{ (⊩a , ⊩¬a) → ⊩¬a ⊩a }

ax-LEM : {a : modal F} → 𝔐 , w ⊩ a ∨ `¬ a
ax-LEM = LEM _

-- ¬⇒⇔∧¬ : {W F : Set} → {𝔐 : KripkeModel W F} → {w : W} → {f g : modal F} → 𝔐 , w ⊩ `¬ (f ⇒ g) ⇔ f ∧ `¬ g
-- ¬⇒⇔∧¬ {W} {F} {𝔐} {w} {f} {g} = => , <=
--  where
--    => : ¬ (𝔐 , w ⊩ f → 𝔐 , w ⊩ g) → (𝔐 , w ⊩ f) × ¬ (𝔐 , w ⊩ g)
--    => ¬f→g with LEM (𝔐 , w ⊩ f)
--    ... | inj₁ yes = yes , (λ ⊩g → ¬f→g λ _ → ⊩g)
--    ... | inj₂ no = {!!}
--    <= : (𝔐 , w ⊩ f) × ¬ (𝔐 , w ⊩ g) → ¬ (𝔐 , w ⊩ f → 𝔐 , w ⊩ g)
--    <= (⊩f , ¬⊩g) f→g = ¬⊩g (f→g ⊩f)
