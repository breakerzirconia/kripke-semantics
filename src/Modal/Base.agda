module Modal.Base where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Unit using (⊤)
open import Data.Bool.Base hiding (_∧_; _∨_)
open import Data.Empty using (⊥-elim)
open import Data.Product using (_×_; _,_; ∃-syntax)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.Core hiding (_⇒_; _⇔_)
open import Relation.Nullary.Negation using (¬_)

open import Classical
open import Classical.Properties
open import Extras
open import Kripke.Semantics

-----------------------------------------------------------------------
-- Re-exporting the core definitions

open import Modal.Core public

-----------------------------------------------------------------------
-- Equivalent statements for conjunction

⊩∧→ : {W F : Set} → (𝔐 : KripkeModel W F) → {w : W} → (a b : modal F) →
     (𝔐 , w ⊩ a ∧ b) → (𝔐 , w ⊩ a) × (𝔐 , w ⊩ b)
⊩∧→ 𝔐 a b f with classical-¬→ f
... | ⊩a , ⊩¬¬b = ⊩a , DNE _ ⊩¬¬b

⊩∧← : {W F : Set} → (𝔐 : KripkeModel W F) → {w : W} → (a b : modal F) →
      (𝔐 , w ⊩ a) × (𝔐 , w ⊩ b) → (𝔐 , w ⊩ a ∧ b)
⊩∧← 𝔐 a b (⊩a , ⊩b) f = f ⊩a ⊩b

⊩∧ : {W F : Set} → (𝔐 : KripkeModel W F) → {w : W} → (a b : modal F) →
     (𝔐 , w ⊩ a ∧ b) ↔ (𝔐 , w ⊩ a) × (𝔐 , w ⊩ b)
⊩∧ 𝔐 a b = ⊩∧→ 𝔐 a b , ⊩∧← 𝔐 a b

-----------------------------------------------------------------------
-- Equivalent statements for disjunction

⊩∨→ : {W F : Set} → (𝔐 : KripkeModel W F) → {w : W} → (a b : modal F) →
     (𝔐 , w ⊩ a ∨ b) → (𝔐 , w ⊩ a) ⊎ (𝔐 , w ⊩ b)
⊩∨→ 𝔐 a b f = Data.Sum.map₁ (DNE _) (classical-→ f)

⊩∨← : {W F : Set} → (𝔐 : KripkeModel W F) → {w : W} → (a b : modal F) →
     (𝔐 , w ⊩ a) ⊎ (𝔐 , w ⊩ b) → (𝔐 , w ⊩ a ∨ b)
⊩∨← 𝔐 a b (inj₁ ⊩a) ⊩¬a = ⊥-elim (⊩¬a ⊩a)
⊩∨← 𝔐 a b (inj₂ ⊩b) ⊩¬a = ⊩b

⊩∨ : {W F : Set} → (𝔐 : KripkeModel W F) → {w : W} → (a b : modal F) →
     (𝔐 , w ⊩ a ∨ b) ↔ (𝔐 , w ⊩ a) ⊎ (𝔐 , w ⊩ b)
⊩∨ 𝔐 a b = ⊩∨→ 𝔐 a b , ⊩∨← 𝔐 a b

-----------------------------------------------------------------------
-- Equivalent statements for the biconditional

⊩⇔→ : {W F : Set} → (𝔐 : KripkeModel W F) → {w : W} → (a b : modal F) →
     (𝔐 , w ⊩ a ⇔ b) → ((𝔐 , w ⊩ a) ↔ (𝔐 , w ⊩ b))
⊩⇔→ 𝔐 a b ⊩a↔b = ⊩∧→ 𝔐 (a ⇒ b) (b ⇒ a) ⊩a↔b

⊩⇔← : {W F : Set} → (𝔐 : KripkeModel W F) → {w : W} → (a b : modal F) →
      ((𝔐 , w ⊩ a) ↔ (𝔐 , w ⊩ b)) → (𝔐 , w ⊩ a ⇔ b)
⊩⇔← 𝔐 a b ⊩a↔⊩b = ⊩∧← 𝔐 (a ⇒ b) (b ⇒ a) ⊩a↔⊩b

⊩⇔ : {W F : Set} → (𝔐 : KripkeModel W F) → {w : W} → (a b : modal F) →
     (𝔐 , w ⊩ a ⇔ b) ↔ ((𝔐 , w ⊩ a) ↔ (𝔐 , w ⊩ b))
⊩⇔ 𝔐 a b = ⊩⇔→ 𝔐 a b , ⊩⇔← 𝔐 a b

-----------------------------------------------------------------------
-- Equivalent statements for the possibility modality

⊩◇→ : {W F : Set} → (𝔐 : KripkeModel W F) → {w : W} → (a : modal F) →
      (𝔐 , w ⊩ ◇ a) → ∃[ v ] (KripkeModel.accesses 𝔐 w v) × (𝔐 , v ⊩ a)
⊩◇→ 𝔐 a f with ¬∀⟶∃¬ f
... | (v , g) with ¬∀⟶∃¬ g
... | (w↝v , ⊩¬¬a) = v , w↝v , DNE _ ⊩¬¬a

⊩◇← : {W F : Set} → (𝔐 : KripkeModel W F) → {w : W} → (a : modal F) →
      (∃[ v ] (KripkeModel.accesses 𝔐 w v) × (𝔐 , v ⊩ a)) → 𝔐 , w ⊩ ◇ a
⊩◇← 𝔐 a (v , w↝v , ⊩a) f = f v w↝v ⊩a

⊩◇ : {W F : Set} → (𝔐 : KripkeModel W F) → {w : W} → (a : modal F) →
     (𝔐 , w ⊩ ◇ a) ↔ ∃[ v ] (KripkeModel.accesses 𝔐 w v) × (𝔐 , v ⊩ a)
⊩◇ 𝔐 a = ⊩◇→ 𝔐 a , ⊩◇← 𝔐 a

-----------------------------------------------------------------------
-- The simple Kripke model from a given accessibility relation

simple : {W : Set} → Rel W _ → KripkeModel W Bool
simple rel = mkKM rel λ w b → b
