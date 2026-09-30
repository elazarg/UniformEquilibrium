import Mathlib.RingTheory.Polynomial.Bernstein
import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-! # Exact degree-two tensor Bernstein interpolation -/

noncomputable section

namespace Math

/-- The computational degree-two Bernstein basis, indexed by `0,1,2`. -/
def quadraticBernsteinBasis (index : Fin 3) (rate : ℝ) : ℝ :=
  if index = 0 then (1 - rate) ^ 2
  else if index = 1 then 2 * rate * (1 - rate)
  else rate ^ 2

/-- The exact interpolation transform at `0, 1/2, 1` in each coordinate. -/
def quadraticBernsteinCoefficient (function : ℝ → ℝ) (index : Fin 3) : ℝ :=
  if index = 0 then function 0
  else if index = 1 then
    2 * function (1 / 2) - (function 0 + function 1) / 2
  else function 1

/-- Apply the one-dimensional interpolation rule independently in both variables. -/
def quadraticTensorBernsteinCoefficient (function : ℝ → ℝ → ℝ)
    (first second : Fin 3) : ℝ :=
  quadraticBernsteinCoefficient
    (fun x => quadraticBernsteinCoefficient (fun y => function x y) second) first

/-- A bilinear interpolant weighted by an affine survival product, minus another
bilinear interpolant. The result is quadratic in each variable. -/
def bilinearSurvivalDifference (survival : ℝ) (quit cont : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  (1 - survival * (1 - x) * (1 - y)) *
    ((1 - x) * (1 - y) * quit 0 0 + x * (1 - y) * quit 1 0 +
      (1 - x) * y * quit 0 1 + x * y * quit 1 1) -
    ((1 - x) * (1 - y) * cont 0 0 + x * (1 - y) * cont 1 0 +
      (1 - x) * y * cont 0 1 + x * y * cont 1 1)

/-- A biquadratic polynomial reconstructs exactly from its nine samples. -/
theorem quadraticTensorBernsteinInterpolation
    (a00 a01 a02 a10 a11 a12 a20 a21 a22 x y : ℝ) :
    let function : ℝ → ℝ → ℝ := fun x y =>
      a00 + a01 * y + a02 * y ^ 2 +
        a10 * x + a11 * x * y + a12 * x * y ^ 2 +
          a20 * x ^ 2 + a21 * x ^ 2 * y + a22 * x ^ 2 * y ^ 2
    function x y =
      ∑ first : Fin 3, ∑ second : Fin 3,
        quadraticTensorBernsteinCoefficient function first second *
          quadraticBernsteinBasis first x * quadraticBernsteinBasis second y := by
  simp [quadraticTensorBernsteinCoefficient, quadraticBernsteinCoefficient,
    quadraticBernsteinBasis, Fin.sum_univ_succ]
  ring

/-- The bilinear-survival shape reconstructs from its nine transformed samples. -/
theorem bilinearSurvivalDifference_eq_quadraticTensorBernstein
    (survival : ℝ) (quit cont : ℝ → ℝ → ℝ) (x y : ℝ) :
    bilinearSurvivalDifference survival quit cont x y =
      ∑ first : Fin 3, ∑ second : Fin 3,
        quadraticTensorBernsteinCoefficient (bilinearSurvivalDifference survival quit cont)
          first second *
          quadraticBernsteinBasis first x * quadraticBernsteinBasis second y := by
  simp [bilinearSurvivalDifference, quadraticTensorBernsteinCoefficient,
    quadraticBernsteinCoefficient, quadraticBernsteinBasis, Fin.sum_univ_succ]
  ring

/-- The computational basis is the standard Bernstein polynomial at degree two. -/
theorem quadraticBernsteinBasis_eq_eval (index : Fin 3) (rate : ℝ) :
    quadraticBernsteinBasis index rate =
      (bernsteinPolynomial ℝ 2 index.val).eval rate := by
  fin_cases index <;> norm_num [quadraticBernsteinBasis, bernsteinPolynomial]

end Math
