/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Real.Basic

/-!
# Rational affine functionals on finite real coordinate spaces

This module records exact rational-affine data independently of any
application-specific polyhedral or Lyapunov interface.
-/

noncomputable section

namespace Math

/-- An affine functional with exact rational coefficients, evaluated later in
real coordinate space. -/
structure RationalAffineFunctional (Coordinate : Type*) where
  offset : ℚ
  coefficient : Coordinate → ℚ

namespace RationalAffineFunctional

/-- Real evaluation of an exact rational affine functional. -/
def eval {Coordinate : Type*} [Fintype Coordinate]
    (functional : RationalAffineFunctional Coordinate)
    (point : Coordinate → ℝ) : ℝ := by
  classical
  exact (functional.offset : ℝ) +
    ∑ coordinate, (functional.coefficient coordinate : ℝ) * point coordinate

end RationalAffineFunctional

end Math

end
