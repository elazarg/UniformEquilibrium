import MathUE.RealQuantifierElimination.QuantifierFreeFormula
import Mathlib.Data.Rat.Cast.Order

/-!
# Indexed polynomial formulas and exact rational evaluation

The indexed syntax supports arbitrary Boolean and quantifier nesting.  This
module gives its real semantics and the executable rational evaluator needed
at the closed quantifier-free endpoint; it does not assume a quantifier
eliminator.
-/

namespace MathUE.RealQuantifierElimination

open Math.PolynomialSignCell

/-- First-order formulas over rational ring expressions in `n` free real
variables.  A quantified body has its bound variable at index zero. -/
inductive PolynomialFormula : Nat → Type
  | atom {n : Nat} (expression : RingExpression n) (expected : SignType) :
      PolynomialFormula n
  | top {n : Nat} : PolynomialFormula n
  | bot {n : Nat} : PolynomialFormula n
  | and {n : Nat} (left right : PolynomialFormula n) : PolynomialFormula n
  | or {n : Nat} (left right : PolynomialFormula n) : PolynomialFormula n
  | not {n : Nat} (formula : PolynomialFormula n) : PolynomialFormula n
  | ex {n : Nat} (body : PolynomialFormula (n + 1)) : PolynomialFormula n
  | all {n : Nat} (body : PolynomialFormula (n + 1)) : PolynomialFormula n
  deriving DecidableEq

namespace PolynomialFormula

/-- Real truth semantics.  A quantified value is inserted at variable index
zero, while existing parameters are shifted by `Fin.succ`. -/
def HoldsAt : {n : Nat} → PolynomialFormula n → (Fin n → ℝ) → Prop
  | _, .atom expression expected, environment =>
      SignType.sign (expression.evalReal environment) = expected
  | _, .top, _ => True
  | _, .bot, _ => False
  | _, .and left right, environment =>
      left.HoldsAt environment ∧ right.HoldsAt environment
  | _, .or left right, environment =>
      left.HoldsAt environment ∨ right.HoldsAt environment
  | _, .not formula, environment => ¬formula.HoldsAt environment
  | _, .ex body, environment =>
      ∃ value : ℝ, body.HoldsAt (Fin.cases value environment)
  | _, .all body, environment =>
      ∀ value : ℝ, body.HoldsAt (Fin.cases value environment)

/-- Embed a quantifier-free formula into the indexed first-order syntax. -/
def ofQuantifierFree {n : Nat} : QuantifierFreeFormula n → PolynomialFormula n
  | .atom expression expected => .atom expression expected
  | .top => .top
  | .bot => .bot
  | .and left right => .and (ofQuantifierFree left) (ofQuantifierFree right)
  | .or left right => .or (ofQuantifierFree left) (ofQuantifierFree right)
  | .not formula => .not (ofQuantifierFree formula)

@[simp]
theorem holdsAt_ofQuantifierFree_iff
    (formula : QuantifierFreeFormula n) (environment : Fin n → ℝ) :
    (ofQuantifierFree formula).HoldsAt environment ↔ formula.HoldsAt environment := by
  induction formula with
  | atom expression expected =>
      rfl
  | top =>
      rfl
  | bot =>
      rfl
  | and left right ihLeft ihRight =>
      exact and_congr ihLeft ihRight
  | or left right ihLeft ihRight =>
      exact or_congr ihLeft ihRight
  | not formula ih =>
      exact not_congr ih

/-- Universally bind every free variable. At arity zero this is the identity.
Original index zero becomes the innermost added universal binder,
followed outward by successor indices. -/
def universallyClose : {n : Nat} → PolynomialFormula n → PolynomialFormula 0
  | 0, formula => formula
  | _ + 1, formula => universallyClose (.all formula)

/-- Universal closure is true exactly when the source formula is true at every
real assignment of its free variables. -/
theorem holdsAt_universallyClose_iff
    (formula : PolynomialFormula n) :
    formula.universallyClose.HoldsAt Fin.elim0 ↔
      ∀ environment : Fin n → ℝ, formula.HoldsAt environment := by
  induction n with
  | zero =>
      constructor
      · intro h environment
        have hempty : environment = Fin.elim0 := by
          funext index
          exact Fin.elim0 index
        simpa [universallyClose, hempty] using h
      · intro h
        simpa [universallyClose] using h Fin.elim0
  | succ n ih =>
      rw [universallyClose, ih]
      change (∀ environment : Fin n → ℝ, ∀ value : ℝ,
          formula.HoldsAt (Fin.cases value environment)) ↔
        ∀ environment : Fin (n + 1) → ℝ, formula.HoldsAt environment
      constructor
      · intro h environment
        have hformula := h (fun index => environment index.succ) (environment 0)
        have hcases :
            Fin.cases (environment 0) (fun index => environment index.succ) = environment := by
          funext index
          refine Fin.cases ?_ (fun successor => ?_) index
          · rfl
          · rfl
        rwa [hcases] at hformula
      · intro h environment value
        exact h (Fin.cases value environment)


end PolynomialFormula

namespace QuantifierFreeFormula

/-- Executable evaluation at a rational environment. -/
def evalRat (formula : QuantifierFreeFormula n) (environment : Fin n → ℚ) : Bool :=
  formula.eval fun expression => SignType.sign (expression.evalRat environment)

private theorem sign_ratCast (value : ℚ) :
    SignType.sign (value : ℝ) = SignType.sign value :=
  StrictMono.sign_comp (f := Rat.castHom ℝ) Rat.cast_strictMono value

/-- Rational evaluation agrees with real truth after casting the environment. -/
theorem evalRat_eq_true_iff_holdsAt
    (formula : QuantifierFreeFormula n) (environment : Fin n → ℚ) :
    formula.evalRat environment = true ↔
      formula.HoldsAt fun index => (environment index : ℝ) := by
  rw [evalRat, SignFormula.eval_eq_true_iff]
  have hsigns :
      (fun expression => SignType.sign (expression.evalRat environment)) =
        realSignAssignment (fun index => (environment index : ℝ)) := by
    funext expression
    rw [realSignAssignment, RingExpression.evalReal_ratCast, sign_ratCast]
  rw [hsigns]
  rfl

/-- Executable decision for a closed quantifier-free formula. -/
def decideClosedQuantifierFree (formula : QuantifierFreeFormula 0) : Bool :=
  formula.evalRat Fin.elim0

/-- The closed rational decision agrees with real truth. -/
theorem decideClosedQuantifierFree_eq_true_iff
    (formula : QuantifierFreeFormula 0) :
    formula.decideClosedQuantifierFree = true ↔ formula.HoldsAt Fin.elim0 := by
  have hempty : (fun index : Fin 0 => ((Fin.elim0 index : ℚ) : ℝ)) = Fin.elim0 := by
    funext index
    exact Fin.elim0 index
  rw [← hempty]
  exact formula.evalRat_eq_true_iff_holdsAt (environment := Fin.elim0)

end QuantifierFreeFormula

end MathUE.RealQuantifierElimination
