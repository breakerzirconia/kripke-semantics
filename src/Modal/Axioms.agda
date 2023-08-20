module Modal.Axioms where

open import Agda.Builtin.Equality
open import Data.Bool hiding (T)
open import Data.Bool.Properties using (not-¬)
open import Data.Empty using (⊥-elim)
open import Data.Product using (_,_; ∃-syntax)
open import Relation.Binary.Core hiding (_⇒_; _⇔_)
open import Relation.Binary.Definitions

open import Modal.Core
open import Relation.Binary.Definitions.Extra

variable
  W F : Set
  𝔐 : KripkeModel W F

K : {w : W} → {a b : modal F} →
    𝔐 , w ⊩ □ (a ⇒ b) ⇒ (□ a ⇒ □ b)
K a⇒b a v w↝v = a⇒b v w↝v (a v w↝v)

T : Reflexive (KripkeModel.accesses 𝔐) → {w : W} → {a : modal F} →
    𝔐 , w ⊩ □ a ⇒ a
T rfl {w = w} □a = □a w rfl

-- This axiom is given a name 'Q' in reference to the density of the set of rational numbers.

Q : Dense (KripkeModel.accesses 𝔐) → {w : W} → {a : modal F} →
    𝔐 , w ⊩ □ □ a ⇒ □ a
Q dense □□a v w↝v with dense w↝v
... | u , w↝u , u↝v = □□a u w↝u v u↝v

Four : Transitive (KripkeModel.accesses 𝔐) → {w : W} → {a : modal F} →
       𝔐 , w ⊩ □ a ⇒ □ □ a
Four trans □a v w↝v u v↝u = □a u (trans w↝v v↝u)

D : Serial (KripkeModel.accesses 𝔐) → {w : W} → {a : modal F} →
    𝔐 , w ⊩ □ a ⇒ ◇ a
D serial {w = w} □a with serial w
... | v , w↝v = v , w↝v , (□a v w↝v)

D◇⊤ : {rel : Rel W _} → Serial rel → {w : W} →
     simple rel , w ⊩ ◇ (atom true)
D◇⊤ serial {w = w} with serial w
... | v , w↝v = v , w↝v , refl

D¬□⊥ : {rel : Rel W _} → Serial rel → {w : W} →
     simple rel , w ⊩ `¬ □ (atom false)
D¬□⊥ serial {w = w} f with serial w
... | v , w↝v = not-¬ (f v w↝v) refl

B□◇ : Symmetric (KripkeModel.accesses 𝔐) → {w : W} → {a : modal F} →
      𝔐 , w ⊩ a ⇒ □ ◇ a
B□◇ sym {w = w} a v w↝v = w , sym w↝v , a

B◇□ : Symmetric (KripkeModel.accesses 𝔐) → {w : W} → {a : modal F} →
      𝔐 , w ⊩ ◇ □ a ⇒ a
B◇□ sym {w = w} (v , w↝v , □a) = □a w (sym w↝v)

Five : Euclidean (KripkeModel.accesses 𝔐) → {w : W} → {a : modal F} →
       𝔐 , w ⊩ ◇ a ⇒ □ ◇ a
Five euclidean (u , w↝u , a) v w↝v = u , euclidean w↝v w↝u , a

G : Convergent (KripkeModel.accesses 𝔐) → {w : W} → {a : modal F} →
    𝔐 , w ⊩ ◇ □ a ⇒ □ ◇ a
G convergent (u , w↝u , □a) v w↝v with convergent w↝v w↝u
... | t , v↝t , u↝t = t , v↝t , □a t u↝t

-- This axiom is given a name 'N' in reference to null graphs, i.e. graphs that don't contain edges.
-- The name is subject to change, since null graphs are simple graphs and do not contain loops, whereas
-- discrete categories are codomains of diagrams of shapes of disconnected graphs containing loops only.

N : Discrete (KripkeModel.accesses 𝔐) → {w : W} → {a : modal F} →
    𝔐 , w ⊩ a ⇒ □ a
N discrete a v w↝v rewrite discrete w↝v = a

-- This axiom is given a name 'P' in reference to partial functions.

P : Partial (KripkeModel.accesses 𝔐) → {w : W} → {a : modal F} →
    𝔐 , w ⊩ ◇ a ⇒ □ a
P partial (u , w↝u , a) v w↝v rewrite partial w↝v w↝u = a

-- This axiom is given a name '1' in reference to the uniqueness of the target for every
-- source, as it is in total functions.

One : Function (KripkeModel.accesses 𝔐) → {w : W} → {a : modal F} →
      𝔐 , w ⊩ □ a ⇔ ◇ a
One (serial , partial) = D serial , P partial

-- This axiom is given a name '0' in reference to the emptiness to the accessibility relation.

Zero : Empty (KripkeModel.accesses 𝔐) → {w : W} → {a : modal F} →
       𝔐 , w ⊩ □ a
Zero empty {w = w} v w↝v = ⊥-elim (empty w v w↝v)

