import MathUE.Polynomial.TensorBernsteinDerivativeEstimate
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Algebra.BigOperators.Pi

/-! # Uniform simultaneous derivative convergence of tensor Bernstein polynomials -/

noncomputable section

namespace Math

open scoped BigOperators Topology
open Set Filter

variable {dimension : ℕ}

/-- The closed real unit cube, including the singleton cube in dimension zero. -/
def realUnitCube (dimension : ℕ) : Set (Fin dimension → ℝ) :=
  {point | ∀ coordinate, point coordinate ∈ Icc (0 : ℝ) 1}

theorem isCompact_realUnitCube : IsCompact (realUnitCube dimension) := by
  convert isCompact_univ_pi (fun _ : Fin dimension ↦
    (isCompact_Icc : IsCompact (Icc (0 : ℝ) 1))) using 1
  ext point
  simp [realUnitCube, Pi.le_def, forall_and]

/-- Coordinate evaluation does not increase the distance between derivative operators. -/
theorem abs_apply_single_sub_le_dist
    (first second : (Fin dimension → ℝ) →L[ℝ] ℝ) (coordinate : Fin dimension) :
    |first (Pi.single coordinate 1) - second (Pi.single coordinate 1)| ≤ dist first second := by
  change ‖(first - second) (Pi.single coordinate 1)‖ ≤ dist first second
  simpa only [Pi.norm_single, norm_one, mul_one, dist_eq_norm] using
    (first - second).le_opNorm (Pi.single coordinate 1)

/-- One Bernstein degree works uniformly at every point and for every coordinate derivative. -/
theorem eventually_fderiv_tensorBernsteinApproximation_close_on_unitCube
    (function : (Fin dimension → ℝ) → ℝ)
    (derivative : (Fin dimension → ℝ) → ((Fin dimension → ℝ) →L[ℝ] ℝ))
    (hderivative : ∀ point ∈ realUnitCube dimension,
      HasFDerivAt function (derivative point) point)
    (hcontinuous : ContinuousOn derivative (realUnitCube dimension))
    {error : ℝ} (herror : 0 < error) :
    ∀ᶠ order : ℕ in atTop, ∀ point ∈ realUnitCube dimension, ∀ coordinate : Fin dimension,
      |fderiv ℝ (fun input ↦ MvPolynomial.eval input
        (tensorBernsteinApproximation (fun _ : Fin dimension ↦ order + 1) function))
          point (Pi.single coordinate 1) - derivative point (Pi.single coordinate 1)| < error := by
  obtain ⟨bound, hbound⟩ := isCompact_realUnitCube.exists_bound_of_continuousOn hcontinuous
  have huniform := isCompact_realUnitCube.uniformContinuousOn_of_continuous hcontinuous
  obtain ⟨radius, hradius, hmodulus⟩ :=
    Metric.uniformContinuousOn_iff.mp huniform (error / 2) (half_pos herror)
  have hstepZero : Tendsto (fun order : ℕ ↦ 2 / (order + 1 : ℝ)) atTop (nhds 0) := by
    simpa only [mul_zero, mul_one_div] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul 2
  have hmomentZero : Tendsto
      (fun order : ℕ ↦ (2 * bound) * ((dimension : ℝ) / order) / (radius / 2) ^ 2)
      atTop (nhds 0) := by
    simpa only [mul_zero, zero_div] using
      ((tendsto_const_div_atTop_nhds_zero_nat (dimension : ℝ)).const_mul (2 * bound)).div_const
        ((radius / 2) ^ 2)
  have hstepSmall := hstepZero.eventually (Iio_mem_nhds (half_pos hradius))
  have hmomentSmall := hmomentZero.eventually (Iio_mem_nhds (half_pos herror))
  filter_upwards [eventually_ge_atTop 1, hstepSmall, hmomentSmall] with order horder hstep hmoment
  intro point hpoint coordinate
  have hestimate := abs_fderiv_tensorBernsteinApproximation_sub_le function derivative coordinate
    order (by omega) point hpoint (error / 2) (2 * bound) radius (radius / 2)
    (half_pos herror).le (half_pos hradius) (by linarith)
    hderivative
    (fun input hinput ↦ (abs_apply_single_sub_le_dist _ _ coordinate).trans
      ((dist_le_norm_add_norm _ _).trans (by
        linarith [hbound input hinput, hbound point hpoint])))
    (fun input hinput hdist ↦ (abs_apply_single_sub_le_dist _ _ coordinate).trans
      (hmodulus input hinput point hpoint hdist).le)
  linarith

/-- Scalar-valued operator norm is bounded by the sum of its coordinate entries. -/
theorem norm_le_sum_abs_apply_single (linear : (Fin dimension → ℝ) →L[ℝ] ℝ) :
    ‖linear‖ ≤ ∑ coordinate, |linear (Pi.single coordinate 1)| := by
  apply linear.opNorm_le_bound (Finset.sum_nonneg (fun coordinate _ ↦ abs_nonneg _))
  intro point
  have hdecompose : point = ∑ coordinate, point coordinate • Pi.single coordinate (1 : ℝ) := by
    ext coordinate
    simp [Pi.single_apply]
  calc
    ‖linear point‖ = ‖∑ coordinate, point coordinate * linear (Pi.single coordinate 1)‖ := by
      conv_lhs => rw [hdecompose, map_sum]
      simp only [map_smul, smul_eq_mul]
    _ ≤ ∑ coordinate, |point coordinate| * |linear (Pi.single coordinate 1)| := by
      simpa only [Real.norm_eq_abs, abs_mul] using
        norm_sum_le Finset.univ (fun coordinate ↦
          point coordinate * linear (Pi.single coordinate 1))
    _ ≤ ∑ coordinate, ‖point‖ * |linear (Pi.single coordinate 1)| := by
      apply Finset.sum_le_sum
      intro coordinate _
      exact mul_le_mul_of_nonneg_right (norm_le_pi_norm point coordinate) (abs_nonneg _)
    _ = _ := by rw [← Finset.mul_sum, mul_comm]

/-- A single actual polynomial approximates all partials and the derivative operator uniformly. -/
theorem exists_mvPolynomial_fderiv_close_on_unitCube
    (function : (Fin dimension → ℝ) → ℝ)
    (derivative : (Fin dimension → ℝ) → ((Fin dimension → ℝ) →L[ℝ] ℝ))
    (hderivative : ∀ point ∈ realUnitCube dimension,
      HasFDerivAt function (derivative point) point)
    (hcontinuous : ContinuousOn derivative (realUnitCube dimension))
    {error : ℝ} (herror : 0 < error) :
    ∃ polynomial : MvPolynomial (Fin dimension) ℝ,
      ∀ point ∈ realUnitCube dimension,
        (∑ coordinate, |fderiv ℝ (fun input ↦ MvPolynomial.eval input polynomial) point
          (Pi.single coordinate 1) - derivative point (Pi.single coordinate 1)|) < error ∧
        ‖fderiv ℝ (fun input ↦ MvPolynomial.eval input polynomial) point - derivative point‖ <
          error := by
  have hscaled : 0 < error / (dimension + 1 : ℝ) := div_pos herror (by positivity)
  obtain ⟨order, horder⟩ :=
    (eventually_fderiv_tensorBernsteinApproximation_close_on_unitCube function derivative
      hderivative hcontinuous hscaled).exists
  refine ⟨tensorBernsteinApproximation (fun _ : Fin dimension ↦ order + 1) function, ?_⟩
  intro point hpoint
  have hsum : (∑ coordinate,
      |fderiv ℝ (fun input ↦ MvPolynomial.eval input
        (tensorBernsteinApproximation (fun _ : Fin dimension ↦ order + 1) function))
        point (Pi.single coordinate 1) - derivative point (Pi.single coordinate 1)|) < error := by
    calc
      _ ≤ ∑ _coordinate : Fin dimension, error / (dimension + 1 : ℝ) :=
        Finset.sum_le_sum fun coordinate _ ↦ (horder point hpoint coordinate).le
      _ = (dimension : ℝ) * (error / (dimension + 1 : ℝ)) := by simp
      _ < error := by
        have hcancel : error / (dimension + 1 : ℝ) * (dimension + 1) = error :=
          div_mul_cancel₀ _ (by positivity)
        nlinarith
  exact ⟨hsum, (norm_le_sum_abs_apply_single _).trans_lt hsum⟩

end Math
