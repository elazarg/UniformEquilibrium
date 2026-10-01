import MathUE.Polynomial.TensorBernsteinQuadratic
import Mathlib.Algebra.BigOperators.Field

/-! # Finite linearity and uniqueness of the canonical quadratic tensor coefficients -/

noncomputable section

namespace Math

/-- Canonical sample coefficients commute with finite sums. -/
theorem quadraticTensorBernsteinCoefficient_sum
    {ι : Type*} [Fintype ι] (functions : ι → ℝ → ℝ → ℝ) (first second : Fin 3) :
    quadraticTensorBernsteinCoefficient (fun x y => ∑ index, functions index x y)
        first second =
      ∑ index, quadraticTensorBernsteinCoefficient (functions index) first second := by
  have hlinear (samples : ι → ℝ → ℝ) (index : Fin 3) :
      quadraticBernsteinCoefficient (fun x => ∑ i, samples i x) index =
        ∑ i, quadraticBernsteinCoefficient (samples i) index := by
    fin_cases index
    · simp [quadraticBernsteinCoefficient]
    · change 2 * (∑ i, samples i (1 / 2)) -
          ((∑ i, samples i 0) + ∑ i, samples i 1) / 2 =
        ∑ i, (2 * samples i (1 / 2) - (samples i 0 + samples i 1) / 2)
      calc
        2 * (∑ i, samples i (1 / 2)) -
            ((∑ i, samples i 0) + ∑ i, samples i 1) / 2 =
          (∑ i, 2 * samples i (1 / 2)) -
            ∑ i, (samples i 0 + samples i 1) / 2 := by
              rw [Finset.mul_sum, ← Finset.sum_add_distrib, Finset.sum_div]
        _ = ∑ i, (2 * samples i (1 / 2) - (samples i 0 + samples i 1) / 2) :=
          by rw [Finset.sum_sub_distrib]
    · simp [quadraticBernsteinCoefficient]
  unfold quadraticTensorBernsteinCoefficient
  have hinner :
      (fun x => quadraticBernsteinCoefficient (fun y => ∑ i, functions i x y) second) =
        fun x => ∑ i, quadraticBernsteinCoefficient (functions i x) second := by
    funext x
    exact hlinear (fun i => functions i x) second
  rw [hinner]
  exact hlinear (fun i x => quadraticBernsteinCoefficient (functions i x) second) first

/-- The coefficient functional is linear in a constant reward coordinate. -/
theorem quadraticTensorBernsteinCoefficient_mul_const
    (function : ℝ → ℝ → ℝ) (constant : ℝ) (first second : Fin 3) :
    quadraticTensorBernsteinCoefficient (fun x y => function x y * constant) first second =
      quadraticTensorBernsteinCoefficient function first second * constant := by
  fin_cases first <;> fin_cases second <;>
    simp [quadraticTensorBernsteinCoefficient, quadraticBernsteinCoefficient] <;> ring

/-- Applying the existing sample transform to a Bernstein expansion recovers
its supplied coefficient exactly. This is the inverse interpolation identity. -/
theorem quadraticTensorBernsteinCoefficient_reconstruction
    (coefficients : Fin 3 → Fin 3 → ℝ) (first second : Fin 3) :
    quadraticTensorBernsteinCoefficient
        (fun x y => ∑ a : Fin 3, ∑ b : Fin 3,
          coefficients a b * quadraticBernsteinBasis a x * quadraticBernsteinBasis b y)
        first second = coefficients first second := by
  fin_cases first <;> fin_cases second <;>
    simp [quadraticTensorBernsteinCoefficient, quadraticBernsteinCoefficient,
      quadraticBernsteinBasis, Fin.sum_univ_succ] <;> ring

/-- Any such expansion must have the canonical coefficients; no new
polynomial representation or independent uniqueness principle is needed. -/
theorem eq_quadraticTensorBernsteinCoefficient_of_reconstruction
    (function : ℝ → ℝ → ℝ) (coefficients : Fin 3 → Fin 3 → ℝ)
    (hreconstruction : ∀ x y, function x y =
      ∑ a : Fin 3, ∑ b : Fin 3,
        coefficients a b * quadraticBernsteinBasis a x * quadraticBernsteinBasis b y)
    (first second : Fin 3) :
    coefficients first second = quadraticTensorBernsteinCoefficient function first second := by
  have heq : function = fun x y => ∑ a : Fin 3, ∑ b : Fin 3,
      coefficients a b * quadraticBernsteinBasis a x * quadraticBernsteinBasis b y := by
    funext x y
    exact hreconstruction x y
  rw [heq, quadraticTensorBernsteinCoefficient_reconstruction]

end Math
