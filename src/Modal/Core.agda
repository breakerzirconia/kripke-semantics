module Modal.Core where

open import Level using (Level)
open import Data.Bool.Base renaming (_∧_ to _&&_; _∨_ to _||_)
open import Data.Empty using (⊥-elim)
open import Data.List using (List)
open import Data.Product using (_×_; _,_; ∃-syntax)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.Core hiding (_⇒_; _⇔_)
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary.Negation using (¬_)

infix 7 `¬_ □_ ◇_
infixr 6 _∧_
infixr 5 _∨_
infixr 4 _⇒_
infixr 3 _⇔_

private
  variable
    ℓ : Level

postulate
  DNE : (a : Set ℓ) → ¬ ¬ a → a

LEM : (a : Set ℓ) → a ⊎ ¬ a
LEM a = DNE (a ⊎ ¬ a) λ n → n (inj₂ λ x → n (inj₁ x))

Peirce : (a b : Set ℓ) → ((a → b) → a) → a
Peirce a b aba = DNE a λ na → na (aba λ x → ⊥-elim (na x))

data modal (a : Set) : Set where
  atom : a → modal a
  `¬_   : modal a → modal a
  _∧_  : modal a → modal a → modal a
  _∨_  : modal a → modal a → modal a
  _⇒_  : modal a → modal a → modal a
  _⇔_  : modal a → modal a → modal a
  □_   : modal a → modal a
  ◇_   : modal a → modal a

_ : modal Bool
_ = `¬ □ ◇ (atom true ∧ atom false)

record KripkeFrame (W : Set) : Set₁ where
  constructor mkKF
  field
    accesses : Rel W _

record KripkeModel (W : Set) (F : Set) : Set₁ where
  constructor mkKM
  field
    accesses : Rel W _
    valuation : W → F → Bool

infix 2 _,_⊩_

_,_⊩_ : {W F : Set} → KripkeModel W F → W → modal F → Set
𝔐 , w ⊩ atom x = KripkeModel.valuation 𝔐 w x ≡ true
𝔐 , w ⊩ `¬ f = ¬ (𝔐 , w ⊩ f)
𝔐 , w ⊩ f ∧ g = (𝔐 , w ⊩ f) × (𝔐 , w ⊩ g)
𝔐 , w ⊩ f ∨ g = (𝔐 , w ⊩ f) ⊎ (𝔐 , w ⊩ g)
𝔐 , w ⊩ f ⇒ g = (𝔐 , w ⊩ f) → (𝔐 , w ⊩ g)
𝔐 , w ⊩ f ⇔ g = ((𝔐 , w ⊩ f) → (𝔐 , w ⊩ g)) × ((𝔐 , w ⊩ g) → (𝔐 , w ⊩ f))
𝔐 , w ⊩ □ f = ∀ v → KripkeModel.accesses 𝔐 w v → 𝔐 , v ⊩ f
𝔐 , w ⊩ ◇ f = ∃[ v ] (KripkeModel.accesses 𝔐 w v) × (𝔐 , v ⊩ f)

non-contra : {W F : Set} → {𝔐 : KripkeModel W F} → {w : W} → {f : modal F} → 𝔐 , w ⊩ `¬ (f ∧ `¬ f)
non-contra = λ{ (f , ¬f) → ¬f f }

-- ¬⇒⇔∧¬ : {W F : Set} → {𝔐 : KripkeModel W F} → {w : W} → {f g : modal F} → 𝔐 , w ⊩ `¬ (f ⇒ g) ⇔ f ∧ `¬ g
-- ¬⇒⇔∧¬ {W} {F} {𝔐} {w} {f} {g} = => , <=
--  where
--    => : ¬ (𝔐 , w ⊩ f → 𝔐 , w ⊩ g) → (𝔐 , w ⊩ f) × ¬ (𝔐 , w ⊩ g)
--    => ¬f→g with LEM (𝔐 , w ⊩ f)
--    ... | inj₁ yes = yes , (λ ⊩g → ¬f→g λ _ → ⊩g)
--    ... | inj₂ no = {!!}
--    <= : (𝔐 , w ⊩ f) × ¬ (𝔐 , w ⊩ g) → ¬ (𝔐 , w ⊩ f → 𝔐 , w ⊩ g)
--    <= (⊩f , ¬⊩g) f→g = ¬⊩g (f→g ⊩f)

