module Modal.Axioms where

open import Data.Bool hiding (T)
open import Data.Empty using (⊥-elim)
open import Data.Product using (_×_; _,_; ∃-syntax)
open import Relation.Binary.Definitions

open import Modal.Core
open import Relation.Binary.Definitions.Extra

K : {W F : Set} → {𝔐 : KripkeModel W F} → {w : W} → {a b : modal F} →
    𝔐 , w ⊩ □ (a ⇒ b) ⇒ (□ a ⇒ □ b)
K a⇒b a v w↝v = a⇒b v w↝v (a v w↝v)

T : {W F : Set} → {𝔐 : KripkeModel W F} → Reflexive (KripkeModel.accesses 𝔐) → {w : W} → {a : modal F} →
    𝔐 , w ⊩ □ a ⇒ a
T rfl {w = w} □a = □a w rfl

-- This axiom is given a name 'Q' in reference to the density of the set of rational numbers.

Q : {W F : Set} → {𝔐 : KripkeModel W F} → Dense (KripkeModel.accesses 𝔐) → {w : W} → {a : modal F} →
     𝔐 , w ⊩ □ □ a ⇒ □ a
Q dense □□a v w↝v with dense w↝v
... | u , (w↝u , u↝v) = □□a u w↝u v u↝v

Four : {W F : Set} → {𝔐 : KripkeModel W F} → Transitive (KripkeModel.accesses 𝔐) → {w : W} → {a : modal F} →
       𝔐 , w ⊩ □ a ⇒ □ □ a
Four trans □a v w↝v u v↝u = □a u (trans w↝v v↝u)

D : {W F : Set} → {𝔐 : KripkeModel W F} → Serial (KripkeModel.accesses 𝔐) → {w : W} → {a : modal F} →
    𝔐 , w ⊩ □ a ⇒ ◇ a
D serial {w = w} □a with serial w
... | v , w↝v = v , w↝v , (□a v w↝v)

-- D⊤ : {W : Set} → {𝔐 : KripkeModel W Bool} → {serial : Serial (KripkeModel.accesses 𝔐)} → {w : W} → {a : modal Bool} →
--     𝔐 , w ⊩ ◇ (atom true)
-- D⊤ = {!!}

B□◇ : {W F : Set} → {𝔐 : KripkeModel W F} → Symmetric (KripkeModel.accesses 𝔐) → {w : W} → {a : modal F} →
      𝔐 , w ⊩ a ⇒ □ ◇ a
B□◇ sym {w = w} a v w↝v = w , sym w↝v , a

B◇□ : {W F : Set} → {𝔐 : KripkeModel W F} → Symmetric (KripkeModel.accesses 𝔐) → {w : W} → {a : modal F} →
      𝔐 , w ⊩ ◇ □ a ⇒ a
B◇□ sym {w = w} (v , w↝v , □a) = □a w (sym w↝v)

Five : {W F : Set} → {𝔐 : KripkeModel W F} → Euclidean (KripkeModel.accesses 𝔐) → {w : W} → {a : modal F} →
       𝔐 , w ⊩ ◇ a ⇒ □ ◇ a
Five euc (u , w↝u , a) v w↝v = u , euc w↝v w↝u , a

G : {W F : Set} → {𝔐 : KripkeModel W F} → Convergent (KripkeModel.accesses 𝔐) → {w : W} → {a : modal F} →
       𝔐 , w ⊩ ◇ □ a ⇒ □ ◇ a
G con (u , w↝u , □a) v w↝v with con w↝v w↝u
... | t , v↝t , u↝t = t , v↝t , □a t u↝t

-- This axiom is given a name 'N' in reference to null graphs, i.e. graphs that don't contain edges.
-- The name is subject to change, since null graphs are simple graphs and do not contain loops, whereas
-- discrete categories are codomains of diagrams of shapes of disconnected graphs containing loops only.

N : {W F : Set} → {𝔐 : KripkeModel W F} → Discrete (KripkeModel.accesses 𝔐) → {w : W} → {a : modal F} →
    𝔐 , w ⊩ a ⇒ □ a
N disc a v w↝v rewrite disc w↝v = a

-- This axiom is given a name 'P' in reference to partial functions.

P : {W F : Set} → {𝔐 : KripkeModel W F} → Partial (KripkeModel.accesses 𝔐) → {w : W} → {a : modal F} →
    𝔐 , w ⊩ ◇ a ⇒ □ a
P part (u , w↝u , a) v w↝v rewrite part w↝v w↝u = a

-- This axiom is given a name 'F' in reference to total functions.

F : {W F : Set} → {𝔐 : KripkeModel W F} → Function (KripkeModel.accesses 𝔐) → {w : W} → {a : modal F} →
    𝔐 , w ⊩ □ a ⇔ ◇ a
F (serial , part) = D serial , P part

-- This axiom is given a name 'Zero' in reference to the emptiness to the accessibility relation.

Zero : {W F : Set} → {𝔐 : KripkeModel W F} → Empty (KripkeModel.accesses 𝔐) → {w : W} → {a : modal F} →
       𝔐 , w ⊩ □ a
Zero empty {w = w} v w↝v = ⊥-elim (empty w v w↝v)
