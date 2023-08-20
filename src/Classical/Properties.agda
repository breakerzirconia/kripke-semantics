module Classical.Properties where

open import Data.Empty using (⊥-elim)
open import Data.Product using (_×_; _,_; ∃; ∃-syntax)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Level using (Level)
open import Relation.Nullary.Negation using (¬_; contraposition)
open import Relation.Unary

open import Classical
open import Extras

private
  variable
    ℓ 𝓂 p : Level
    A : Set 𝓂
    P : Set p

-----------------------------------------------------------------------
-- Material implication

classical-→ : {a b : Set ℓ} → (a → b) → ¬ a ⊎ b
classical-→ {a = a} {b = b} f with LEM a
classical-→ f | inj₁ a = inj₂ (f a)
classical-→ f | inj₂ ¬a = inj₁ ¬a

-----------------------------------------------------------------------
-- 1 out of 4 De Morgan laws does not hold in constructive logic

classical-¬×⇒¬⊎¬ : {a b : Set ℓ} → ¬ (a × b) → ¬ a ⊎ ¬ b
classical-¬×⇒¬⊎¬ {a = a} {b = b} f with LEM a
classical-¬×⇒¬⊎¬ f | inj₁ a = inj₂ λ b → f (a , b)
classical-¬×⇒¬⊎¬ f | inj₂ ¬a = inj₁ ¬a

-----------------------------------------------------------------------
-- Negation of material implication

classical-¬→ : {a b : Set ℓ} → ¬ (a → b) → a × ¬ b
classical-¬→ {a = a} {b = b} f with LEM a | LEM b
classical-¬→ f | inj₁ a | inj₁ b = a , λ b → f (λ _ → b)
classical-¬→ f | inj₁ a | inj₂ ¬b = a , ¬b
classical-¬→ f | inj₂ ¬a | inj₁ b = ⊥-elim (f (λ _ → b)) , λ b → f (λ _ → b)
-- classical-¬→ f | inj₂ ¬a | inj₁ b = ⊥-elim (f (λ a → ⊥-elim (¬a a))) , λ b → f (λ _ → b)
classical-¬→ f | inj₂ ¬a | inj₂ ¬b = ⊥-elim (f (λ a → ⊥-elim (¬a a))) , ¬b

-----------------------------------------------------------------------
-- Proof by contradiction

classical-by-contradiction : {a b : Set ℓ} → (¬ b → ¬ a) → (a → b)
classical-by-contradiction f a = DNE _ (contraposition f (⊥-intro a))

-----------------------------------------------------------------------
-- Quantifier juggling
--
-- (  ∃ x .   P x) → (¬ ∀ x . ¬ P x) : constructive
-- (¬ ∀ x . ¬ P x) → (  ∃ x .   P x) : classical
-- (¬ ∃ x .   P x) → (  ∀ x . ¬ P x) : constructive
-- (  ∀ x . ¬ P x) → (¬ ∃ x .   P x) : constructive
-- (  ∃ x . ¬ P x) → (¬ ∀ x .   P x) : constructive
-- (¬ ∀ x .   P x) → (  ∃ x . ¬ P x) : classical    [NOT PROVEN YET]
-- (¬ ∃ x . ¬ P x) → (  ∀ x .   P x) : classical
-- (  ∀ x .   P x) → (¬ ∃ x . ¬ P x) : constructive

module _ {P : Pred A p} where

  ¬∀¬⟶∃ : ¬ (∀ x → ¬ P x) → ∃ P
  ¬∀¬⟶∃ ¬∀¬ = DNE _ λ ¬∃ → ¬∀¬ λ x Px → ¬∃ (x , Px)

  ¬∀⟶∃¬ : ¬ (∀ x → P x) → ∃ λ x → ¬ P x
  ¬∀⟶∃¬ ¬∀ = DNE _ λ ¬∃¬ → {!!}

  ¬∃¬⟶∀ : ¬ ∃ (λ x → ¬ P x) → ∀ x → P x
  ¬∃¬⟶∀ ¬∃¬ x = DNE _ λ ¬Px → ¬∃¬ (x , ¬Px)
