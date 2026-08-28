/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors.
-/

import MathUE.Interval.RationalInterval
import Mathlib.Topology.Instances.Real.Lemmas

/-!
# Exact intervals for rational expressions with binary maximum

The syntax is the small executable language needed by rational lower-bound
certificates.  It deliberately retains binary `max` instead of encoding a
maximum by auxiliary polynomial constraints.  Evaluation over rational boxes
is exact computation; the semantic bridge proves enclosure of real
evaluation.
-/

namespace Math
namespace Interval

/-- Factored rational expressions with binary maximum. -/
inductive RationalMaxExpression (variableCount : ℕ) where
  | constant (value : ℚ)
  | var (index : Fin variableCount)
  | add (first second : RationalMaxExpression variableCount)
  | neg (expression : RationalMaxExpression variableCount)
  | mul (first second : RationalMaxExpression variableCount)
  | max (first second : RationalMaxExpression variableCount)
deriving DecidableEq, Repr

namespace RationalMaxExpression

variable {variableCount : ℕ}

instance : Zero (RationalMaxExpression variableCount) :=
  ⟨.constant 0⟩

instance : One (RationalMaxExpression variableCount) :=
  ⟨.constant 1⟩

instance : Add (RationalMaxExpression variableCount) :=
  ⟨.add⟩

instance : Neg (RationalMaxExpression variableCount) :=
  ⟨.neg⟩

instance : Sub (RationalMaxExpression variableCount) :=
  ⟨fun first second ↦ first + -second⟩

instance : Mul (RationalMaxExpression variableCount) :=
  ⟨.mul⟩

/-- Real semantics of a reflected expression. -/
def evalReal (point : Fin variableCount → ℝ) :
    RationalMaxExpression variableCount → ℝ
  | .constant value => value
  | .var index => point index
  | .add first second => evalReal point first + evalReal point second
  | .neg expression => -evalReal point expression
  | .mul first second => evalReal point first * evalReal point second
  | .max first second =>
      Max.max (evalReal point first) (evalReal point second)

/-- Rational semantics, used for exact pointwise checking. -/
def evalRat (point : Fin variableCount → ℚ) :
    RationalMaxExpression variableCount → ℚ
  | .constant value => value
  | .var index => point index
  | .add first second => evalRat point first + evalRat point second
  | .neg expression => -evalRat point expression
  | .mul first second => evalRat point first * evalRat point second
  | .max first second =>
      Max.max (evalRat point first) (evalRat point second)

/-- Interval hull of two rational intervals.  This is the exact natural
interval extension of binary maximum. -/
def intervalMax (first second : RationalInterval) : RationalInterval :=
  ⟨Max.max first.lower second.lower,
    Max.max first.upper second.upper⟩

/-- Natural exact-rational interval evaluation. -/
def evalInterval (box : Fin variableCount → RationalInterval) :
    RationalMaxExpression variableCount → RationalInterval
  | .constant value => RationalInterval.point value
  | .var index => box index
  | .add first second =>
      (evalInterval box first).add (evalInterval box second)
  | .neg expression => (evalInterval box expression).neg
  | .mul first second =>
      (evalInterval box first).mul (evalInterval box second)
  | .max first second =>
      intervalMax (evalInterval box first) (evalInterval box second)

/-- The interval hull encloses a binary real maximum. -/
theorem contains_intervalMax
    {first second : RationalInterval} {x y : ℝ}
    (hfirst : first.Contains x) (hsecond : second.Contains y) :
    (intervalMax first second).Contains (Max.max x y) := by
  constructor
  · change ((Max.max first.lower second.lower : ℚ) : ℝ) ≤ Max.max x y
    rw [show ((Max.max first.lower second.lower : ℚ) : ℝ) =
      Max.max (first.lower : ℝ) (second.lower : ℝ) by exact_mod_cast rfl]
    exact max_le_max hfirst.1 hsecond.1
  · change Max.max x y ≤ ((Max.max first.upper second.upper : ℚ) : ℝ)
    rw [show ((Max.max first.upper second.upper : ℚ) : ℝ) =
      Max.max (first.upper : ℝ) (second.upper : ℝ) by exact_mod_cast rfl]
    exact max_le_max hfirst.2 hsecond.2

/-- Exact interval evaluation encloses real evaluation. -/
theorem evalInterval_sound
    (expression : RationalMaxExpression variableCount)
    (box : Fin variableCount → RationalInterval)
    (point : Fin variableCount → ℝ)
    (hpoint : ∀ index, (box index).Contains (point index)) :
    (evalInterval box expression).Contains
      (evalReal point expression) := by
  induction expression with
  | constant value => exact RationalInterval.contains_point value
  | var index => exact hpoint index
  | add first second hfirst hsecond => exact hfirst.add hsecond
  | neg expression hexpression => exact hexpression.neg
  | mul first second hfirst hsecond => exact hfirst.mul hsecond
  | max first second hfirst hsecond =>
      exact contains_intervalMax hfirst hsecond

/-- Rational evaluation commutes with the canonical cast to the reals. -/
theorem ratCast_evalRat
    (expression : RationalMaxExpression variableCount)
    (point : Fin variableCount → ℚ) :
    (evalRat point expression : ℝ) =
      evalReal (fun index ↦ (point index : ℝ)) expression := by
  induction expression with
  | constant value => rfl
  | var index => rfl
  | add first second hfirst hsecond => simp [evalRat, evalReal, hfirst, hsecond]
  | neg expression hexpression => simp [evalRat, evalReal, hexpression]
  | mul first second hfirst hsecond => simp [evalRat, evalReal, hfirst, hsecond]
  | max first second hfirst hsecond =>
      simp [evalRat, evalReal, hfirst, hsecond]

/-- Natural interval evaluation shrinks exactly to point evaluation whenever
every coordinate endpoint does.  This is the structural convergence theorem
needed to turn strict pointwise separation into finite box certificates; it
does not assume or prescribe a particular subdivision generator. -/
theorem evalInterval_tendsto_point
    {Index : Type*} (filter : Filter Index)
    (expression : RationalMaxExpression variableCount)
    (box : Index → Fin variableCount → RationalInterval)
    (point : Fin variableCount → ℝ)
    (hlower : ∀ coordinate, Filter.Tendsto
      (fun index ↦ ((box index coordinate).lower : ℝ)) filter
      (nhds (point coordinate)))
    (hupper : ∀ coordinate, Filter.Tendsto
      (fun index ↦ ((box index coordinate).upper : ℝ)) filter
      (nhds (point coordinate))) :
    Filter.Tendsto
        (fun index ↦ ((evalInterval (box index) expression).lower : ℝ))
        filter (nhds (evalReal point expression)) ∧
      Filter.Tendsto
        (fun index ↦ ((evalInterval (box index) expression).upper : ℝ))
        filter (nhds (evalReal point expression)) := by
  induction expression with
  | constant value =>
      constructor <;>
        simpa [evalInterval, evalReal, RationalInterval.point] using
          (tendsto_const_nhds : Filter.Tendsto
            (fun _ : Index ↦ (value : ℝ)) filter (nhds (value : ℝ)))
  | var coordinate => exact ⟨hlower coordinate, hupper coordinate⟩
  | add first second hfirst hsecond =>
      constructor
      · simpa only [evalInterval, evalReal, RationalInterval.add,
          Rat.cast_add] using hfirst.1.add hsecond.1
      · simpa only [evalInterval, evalReal, RationalInterval.add,
          Rat.cast_add] using hfirst.2.add hsecond.2
  | neg expression hexpression =>
      constructor
      · simpa only [evalInterval, evalReal, RationalInterval.neg,
          Rat.cast_neg] using hexpression.2.neg
      · simpa only [evalInterval, evalReal, RationalInterval.neg,
          Rat.cast_neg] using hexpression.1.neg
  | mul first second hfirst hsecond =>
      have hll := hfirst.1.mul hsecond.1
      have hlu := hfirst.1.mul hsecond.2
      have hul := hfirst.2.mul hsecond.1
      have huu := hfirst.2.mul hsecond.2
      constructor
      · simpa only [evalInterval, evalReal, RationalInterval.mul,
          Rat.cast_min, Rat.cast_mul, min_self] using
          hll.min (hlu.min (hul.min huu))
      · simpa only [evalInterval, evalReal, RationalInterval.mul,
          Rat.cast_max, Rat.cast_mul, max_self] using
          hll.max (hlu.max (hul.max huu))
  | max first second hfirst hsecond =>
      constructor
      · simpa only [evalInterval, evalReal, intervalMax, Rat.cast_max] using
          hfirst.1.max hsecond.1
      · simpa only [evalInterval, evalReal, intervalMax, Rat.cast_max] using
          hfirst.2.max hsecond.2

end RationalMaxExpression

end Interval
end Math
