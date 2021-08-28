open import Data.Nat
open import Data.Bool hiding (T)
open import Data.Maybe
open import Data.Empty
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

variable
  T : Set

---- Source language
data Exp : Set where
  valB : Bool -> Exp
  valI : ℕ -> Exp
  add : Exp -> Exp -> Exp
  and_ : Exp -> Exp -> Exp
  if : Exp -> Exp -> Exp -> Exp

----- Statics
infix 4 ⊢_∶_

data Ty : Set where
  nat : Ty
  bool : Ty

data ⊢_∶_ : Exp -> Ty -> Set where
  typ-bool : ∀{b : Bool} -> ⊢ (valB b) ∶ bool
  typ-int : ∀{i : ℕ} -> ⊢ (valI i) ∶ nat
  typ-add : ∀{e1 e2} -> ⊢ e1 ∶ nat -> ⊢ e2 ∶ nat -> ⊢ (add e1 e2) ∶ nat
  typ-and : ∀{e1 e2} -> ⊢ e1 ∶ bool -> ⊢ e2 ∶ bool -> ⊢ (and_ e1 e2) ∶ bool
  typ-if : ∀{t e e1 e2} -> ⊢ e ∶ bool -> ⊢ e1 ∶ t -> ⊢ e2 ∶ t -> ⊢ (if e e1 e2) ∶ t

---- Operational semantics

infixr 6 _↝_

-- values
data _done : Exp -> Set where
  val-bool : ∀{b : Bool} -> (valB b)done
  val-int : ∀{i : ℕ} -> (valI i)done

-- Steps-to
data _↝_ : Exp -> Exp -> Set where
  step-add-1 : ∀{e1 e2 e1'} -> (e1 ↝ e1') -> (add e1 e2 ↝ add e1' e2)
  step-add-2 : ∀{e1 e2 e2'} -> (e2 ↝ e2') -> (add e1 e2 ↝ add e1 e2')
  step-add-v : ∀{i1 i2} -> (add (valI i1) (valI i2) ↝ valI (i1 + i2))
  step-and-1 : ∀{e1 e2 e1'} -> (e1 ↝ e1') -> (and_ e1 e2 ↝ and_ e1' e2)
  step-and-2 : ∀{e1 e2 e2'} -> (e2 ↝ e2') -> (and_ e1 e2 ↝ and_ e1 e2')
  step-and-v : ∀{b1 b2} -> (and_ (valB b1) (valB b2) ↝ valB (b1 ∧ b2))
  step-if-cond : ∀{e e' e1 e2} -> (e ↝ e') -> (if e e1 e2 ↝ if e' e1 e2)
  step-if-t : ∀{e1 e2} -> (if (valB true) e1 e2 ↝ e1)
  step-if-f : ∀{e1 e2} -> (if (valB false) e1 e2 ↝ e2)

---- Correctness
data Canonical : Exp -> Ty -> Set where
  c-bool : ∀{b : Bool} -> Canonical (valB b) bool
  c-int : ∀{i : ℕ} -> Canonical (valI i) nat

canonical : ∀{e τ} -> ⊢ e ∶ τ -> e done -> Canonical e τ
canonical {valB b} typ-bool val-bool = c-bool
canonical {valI i} typ-int val-int = c-int

data Progress (e : Exp) : Set where
  steps : ∀{e'} -> (e ↝ e') -> Progress e
  normal : e done -> Progress e

progress : ∀{e τ} -> ⊢ e ∶ τ -> Progress e
progress {valB b} {bool} typ-bool = normal val-bool
progress {valI i} {nat} typ-int = normal val-int
progress {add e1 e2} {nat} (typ-add p1 p2) with progress {e1} p1
... | steps {e1'} p1' = steps (step-add-1 p1')
... | normal p1' with progress {e2} p2
...   | steps {e2'} p2' = steps (step-add-2 p2')
...   | normal p2' with canonical {e1} {nat} p1 p1'
...     | c-int {i1} with canonical {e2} {nat} p2 p2'
...       | c-int {i2} = steps (step-add-v {i1} {i2})
progress {and_ e1 e2} {bool} (typ-and p1 p2) with progress {e1} p1
... | steps {e1'} p1' = steps (step-and-1 p1')
... | normal p1' with progress {e2} p2
...   | steps {e2'} p2' = steps (step-and-2 p2')
...   | normal p2' with canonical {e1} {bool} p1 p1'
...     | c-bool {b1} with canonical {e2} {bool} p2 p2'
...       | c-bool {b2} = steps (step-and-v {b1} {b2})
progress {if e e1 e2} {τ} (typ-if p p1 p2) with progress {e} p
... | steps {e'} p' = steps (step-if-cond p')
... | normal p' with canonical {e} {bool} p p'
...   | c-bool {true} = steps step-if-t
...   | c-bool {false} = steps step-if-f
