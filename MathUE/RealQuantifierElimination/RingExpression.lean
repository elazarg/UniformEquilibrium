import Mathlib.Data.Rat.Cast.CharZero
import Mathlib.Data.Real.Basic

/-!
# Rational ring expressions

Rational expressions carry only syntactic operation instances. Evaluation
into rationals is executable; real evaluation and variable renaming have
structural correctness theorems.
-/

namespace MathUE.RealQuantifierElimination

/-- Rational ring-expression syntax in `n` variables. -/
inductive RingExpression (n : Nat)
  | const (value : ℚ)
  | var (index : Fin n)
  | neg (expression : RingExpression n)
  | add (left right : RingExpression n)
  | mul (left right : RingExpression n)
  deriving DecidableEq, Repr

namespace RingExpression

variable {m n : Nat}

instance : Zero (RingExpression n) := ⟨.const 0⟩
instance : One (RingExpression n) := ⟨.const 1⟩
instance : Neg (RingExpression n) := ⟨.neg⟩
instance : Add (RingExpression n) := ⟨.add⟩
instance : Mul (RingExpression n) := ⟨.mul⟩

/-- Evaluation into a type carrying only the operations used by the syntax. -/
def eval {R : Type*} [Neg R] [Add R] [Mul R]
    (ofRat : ℚ → R) (environment : Fin n → R) : RingExpression n → R
  | .const value => ofRat value
  | .var index => environment index
  | .neg expression => -expression.eval ofRat environment
  | .add left right => left.eval ofRat environment + right.eval ofRat environment
  | .mul left right => left.eval ofRat environment * right.eval ofRat environment

/-- Executable evaluation at a rational environment. -/
def evalRat (environment : Fin n → ℚ) (expression : RingExpression n) : ℚ :=
  expression.eval id environment

/-- Evaluation at a real environment. -/
noncomputable def evalReal
    (environment : Fin n → ℝ) (expression : RingExpression n) : ℝ :=
  expression.eval (fun value : ℚ => (value : ℝ)) environment

/-- Rename every variable by an index map. -/
def rename (indexMap : Fin n → Fin m) : RingExpression n → RingExpression m
  | .const value => .const value
  | .var index => .var (indexMap index)
  | .neg expression => -.rename indexMap expression
  | .add left right => .rename indexMap left + .rename indexMap right
  | .mul left right => .rename indexMap left * .rename indexMap right

/-- Shift every variable past a new variable at index zero. -/
def weaken (expression : RingExpression n) : RingExpression (n + 1) :=
  expression.rename Fin.succ

@[simp]
theorem eval_const {R : Type*} [Neg R] [Add R] [Mul R]
    (ofRat : ℚ → R) (environment : Fin n → R) (value : ℚ) :
    (RingExpression.const value).eval ofRat environment = ofRat value :=
  rfl

@[simp]
theorem eval_var {R : Type*} [Neg R] [Add R] [Mul R]
    (ofRat : ℚ → R) (environment : Fin n → R) (index : Fin n) :
    (RingExpression.var index).eval ofRat environment = environment index :=
  rfl

@[simp]
theorem eval_neg {R : Type*} [Neg R] [Add R] [Mul R]
    (ofRat : ℚ → R) (environment : Fin n → R) (expression : RingExpression n) :
    (-expression).eval ofRat environment = -expression.eval ofRat environment :=
  rfl

@[simp]
theorem eval_add {R : Type*} [Neg R] [Add R] [Mul R]
    (ofRat : ℚ → R) (environment : Fin n → R)
    (left right : RingExpression n) :
    (left + right).eval ofRat environment =
      left.eval ofRat environment + right.eval ofRat environment :=
  rfl

@[simp]
theorem eval_mul {R : Type*} [Neg R] [Add R] [Mul R]
    (ofRat : ℚ → R) (environment : Fin n → R)
    (left right : RingExpression n) :
    (left * right).eval ofRat environment =
      left.eval ofRat environment * right.eval ofRat environment :=
  rfl

@[simp]
theorem eval_zero {R : Type*} [Zero R] [Neg R] [Add R] [Mul R]
    (ofRat : ℚ → R) (environment : Fin n → R) (hzero : ofRat 0 = 0) :
    (0 : RingExpression n).eval ofRat environment = 0 :=
  hzero

@[simp]
theorem eval_one {R : Type*} [One R] [Neg R] [Add R] [Mul R]
    (ofRat : ℚ → R) (environment : Fin n → R) (hone : ofRat 1 = 1) :
    (1 : RingExpression n).eval ofRat environment = 1 :=
  hone

@[simp]
theorem evalRat_const (environment : Fin n → ℚ) (value : ℚ) :
    (RingExpression.const value).evalRat environment = value :=
  rfl

@[simp]
theorem evalRat_var (environment : Fin n → ℚ) (index : Fin n) :
    (RingExpression.var index).evalRat environment = environment index :=
  rfl

@[simp]
theorem evalRat_zero (environment : Fin n → ℚ) :
    (0 : RingExpression n).evalRat environment = 0 :=
  rfl

@[simp]
theorem evalRat_one (environment : Fin n → ℚ) :
    (1 : RingExpression n).evalRat environment = 1 :=
  rfl

@[simp]
theorem evalRat_neg (environment : Fin n → ℚ) (expression : RingExpression n) :
    (-expression).evalRat environment = -expression.evalRat environment :=
  rfl

@[simp]
theorem evalRat_add
    (environment : Fin n → ℚ) (left right : RingExpression n) :
    (left + right).evalRat environment =
      left.evalRat environment + right.evalRat environment :=
  rfl

@[simp]
theorem evalRat_mul
    (environment : Fin n → ℚ) (left right : RingExpression n) :
    (left * right).evalRat environment =
      left.evalRat environment * right.evalRat environment :=
  rfl

@[simp]
theorem evalReal_const (environment : Fin n → ℝ) (value : ℚ) :
    (RingExpression.const value).evalReal environment = (value : ℝ) :=
  rfl

@[simp]
theorem evalReal_var (environment : Fin n → ℝ) (index : Fin n) :
    (RingExpression.var index).evalReal environment = environment index :=
  rfl

@[simp]
theorem evalReal_zero (environment : Fin n → ℝ) :
    (0 : RingExpression n).evalReal environment = 0 := by
  exact Rat.cast_zero

@[simp]
theorem evalReal_one (environment : Fin n → ℝ) :
    (1 : RingExpression n).evalReal environment = 1 := by
  exact Rat.cast_one

@[simp]
theorem evalReal_neg
    (environment : Fin n → ℝ) (expression : RingExpression n) :
    (-expression).evalReal environment = -expression.evalReal environment :=
  rfl

@[simp]
theorem evalReal_add
    (environment : Fin n → ℝ) (left right : RingExpression n) :
    (left + right).evalReal environment =
      left.evalReal environment + right.evalReal environment :=
  rfl

@[simp]
theorem evalReal_mul
    (environment : Fin n → ℝ) (left right : RingExpression n) :
    (left * right).evalReal environment =
      left.evalReal environment * right.evalReal environment :=
  rfl

@[simp]
theorem eval_rename {R : Type*} [Neg R] [Add R] [Mul R]
    (ofRat : ℚ → R) (environment : Fin m → R)
    (indexMap : Fin n → Fin m) (expression : RingExpression n) :
    (expression.rename indexMap).eval ofRat environment =
      expression.eval ofRat (environment ∘ indexMap) := by
  induction expression with
  | const value => rfl
  | var index => rfl
  | neg expression ih =>
      change -eval ofRat environment (expression.rename indexMap) =
        -eval ofRat (environment ∘ indexMap) expression
      exact congrArg Neg.neg ih
  | add left right ihLeft ihRight =>
      change eval ofRat environment (left.rename indexMap) +
          eval ofRat environment (right.rename indexMap) =
        eval ofRat (environment ∘ indexMap) left +
          eval ofRat (environment ∘ indexMap) right
      exact congrArg₂ (· + ·) ihLeft ihRight
  | mul left right ihLeft ihRight =>
      change eval ofRat environment (left.rename indexMap) *
          eval ofRat environment (right.rename indexMap) =
        eval ofRat (environment ∘ indexMap) left *
          eval ofRat (environment ∘ indexMap) right
      exact congrArg₂ (· * ·) ihLeft ihRight

@[simp]
theorem evalRat_rename
    (environment : Fin m → ℚ) (indexMap : Fin n → Fin m)
    (expression : RingExpression n) :
    (expression.rename indexMap).evalRat environment =
      expression.evalRat (environment ∘ indexMap) :=
  eval_rename id environment indexMap expression

@[simp]
theorem evalReal_rename
    (environment : Fin m → ℝ) (indexMap : Fin n → Fin m)
    (expression : RingExpression n) :
    (expression.rename indexMap).evalReal environment =
      expression.evalReal (environment ∘ indexMap) :=
  eval_rename (fun value : ℚ => (value : ℝ)) environment indexMap expression

@[simp]
theorem eval_weaken {R : Type*} [Neg R] [Add R] [Mul R]
    (ofRat : ℚ → R) (environment : Fin (n + 1) → R)
    (expression : RingExpression n) :
    expression.weaken.eval ofRat environment =
      expression.eval ofRat (environment ∘ Fin.succ) :=
  eval_rename ofRat environment Fin.succ expression

@[simp]
theorem evalRat_weaken
    (environment : Fin (n + 1) → ℚ) (expression : RingExpression n) :
    expression.weaken.evalRat environment =
      expression.evalRat (environment ∘ Fin.succ) :=
  evalRat_rename environment Fin.succ expression

@[simp]
theorem evalReal_weaken
    (environment : Fin (n + 1) → ℝ) (expression : RingExpression n) :
    expression.weaken.evalReal environment =
      expression.evalReal (environment ∘ Fin.succ) :=
  evalReal_rename environment Fin.succ expression

/-- Rational evaluation commutes with the canonical embedding into the reals. -/
theorem evalReal_ratCast
    (environment : Fin n → ℚ) (expression : RingExpression n) :
    expression.evalReal (fun index => (environment index : ℝ)) =
      (expression.evalRat environment : ℝ) := by
  induction expression with
  | const value => rfl
  | var index => rfl
  | neg expression ih =>
      change -expression.evalReal (fun index => (environment index : ℝ)) =
        ((-expression.evalRat environment : ℚ) : ℝ)
      rw [ih, Rat.cast_neg]
  | add left right ihLeft ihRight =>
      change left.evalReal (fun index => (environment index : ℝ)) +
          right.evalReal (fun index => (environment index : ℝ)) =
        ((left.evalRat environment + right.evalRat environment : ℚ) : ℝ)
      rw [ihLeft, ihRight]
      exact (Rat.cast_add _ _).symm
  | mul left right ihLeft ihRight =>
      change left.evalReal (fun index => (environment index : ℝ)) *
          right.evalReal (fun index => (environment index : ℝ)) =
        ((left.evalRat environment * right.evalRat environment : ℚ) : ℝ)
      rw [ihLeft, ihRight]
      exact (Rat.cast_mul _ _).symm

/-- A right-associated syntactic sum. -/
def sum : List (RingExpression n) → RingExpression n
  | [] => 0
  | expression :: expressions => expression + sum expressions

/-- A right-associated syntactic product. -/
def product : List (RingExpression n) → RingExpression n
  | [] => 1
  | expression :: expressions => expression * product expressions

@[simp]
theorem eval_sum {R : Type*} [Zero R] [Neg R] [Add R] [Mul R]
    (ofRat : ℚ → R) (environment : Fin n → R) (hzero : ofRat 0 = 0)
    (expressions : List (RingExpression n)) :
    (sum expressions).eval ofRat environment =
      (expressions.map (RingExpression.eval ofRat environment)).sum := by
  induction expressions with
  | nil => simp [sum, hzero]
  | cons expression expressions ih =>
      simp [sum, ih]

@[simp]
theorem eval_product {R : Type*} [One R] [Neg R] [Add R] [Mul R]
    (ofRat : ℚ → R) (environment : Fin n → R) (hone : ofRat 1 = 1)
    (expressions : List (RingExpression n)) :
    (product expressions).eval ofRat environment =
      (expressions.map (RingExpression.eval ofRat environment)).prod := by
  induction expressions with
  | nil => simp [product, hone]
  | cons expression expressions ih =>
      simp [product, ih]

@[simp]
theorem evalRat_sum
    (expressions : List (RingExpression n)) (environment : Fin n → ℚ) :
    (sum expressions).evalRat environment =
      (expressions.map (RingExpression.evalRat environment)).sum := by
  exact eval_sum id environment rfl expressions

@[simp]
theorem evalRat_product
    (expressions : List (RingExpression n)) (environment : Fin n → ℚ) :
    (product expressions).evalRat environment =
      (expressions.map (RingExpression.evalRat environment)).prod := by
  exact eval_product id environment rfl expressions

@[simp]
theorem evalReal_sum
    (expressions : List (RingExpression n)) (environment : Fin n → ℝ) :
    (sum expressions).evalReal environment =
      (expressions.map (RingExpression.evalReal environment)).sum := by
  exact eval_sum (fun value : ℚ => (value : ℝ)) environment (Rat.cast_zero) expressions

@[simp]
theorem evalReal_product
    (expressions : List (RingExpression n)) (environment : Fin n → ℝ) :
    (product expressions).evalReal environment =
      (expressions.map (RingExpression.evalReal environment)).prod := by
  exact eval_product (fun value : ℚ => (value : ℝ)) environment (Rat.cast_one) expressions

end RingExpression
end MathUE.RealQuantifierElimination
