import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.ContDiff.Convolution

/-! # One-sided smoothing preserving translated drift -/

noncomputable section

open Filter Function MeasureTheory Set
open scoped ContDiff Convolution Topology

namespace Math.OneSidedCapacitySmoothing

variable {coordinate : Type} [Fintype coordinate]

/-- A normalized smooth kernel whose convolution samples common
coordinatewise shifts in the positive cube `[0, radius]`. The kernel itself
is supported in the reflected negative cube because convolution evaluates a
function at `x - displacement`. -/
structure OneSidedSmoothKernel (coordinate : Type) [Fintype coordinate]
    (radius : ℝ) where
  toFun : (coordinate → ℝ) → ℝ
  nonneg : ∀ displacement, 0 ≤ toFun displacement
  integral_one : ∫ displacement, toFun displacement = 1
  contDiff : ContDiff ℝ ∞ toFun
  hasCompactSupport : HasCompactSupport toFun
  shift_mem : ∀ displacement, toFun displacement ≠ 0 → ∀ who,
    0 < -displacement who ∧ -displacement who < radius

instance (radius : ℝ) : CoeFun (OneSidedSmoothKernel coordinate radius)
    (fun _ ↦ (coordinate → ℝ) → ℝ) :=
  ⟨OneSidedSmoothKernel.toFun⟩

private def negativeCubeBump (radius : ℝ) (hradius : 0 < radius) :
    ContDiffBump (fun _ : coordinate ↦ -radius / 2) :=
  ⟨radius / 8, radius / 4, by positivity, by linarith⟩

/-- The canonical normalized bump used for one-sided smoothing. -/
def canonicalOneSidedSmoothKernel (radius : ℝ) (hradius : 0 < radius) :
    OneSidedSmoothKernel coordinate radius := by
  let bump := negativeCubeBump (coordinate := coordinate) radius hradius
  let kernel := bump.normed (volume : Measure (coordinate → ℝ))
  refine {
    toFun := kernel
    nonneg := bump.nonneg_normed
    integral_one := bump.integral_normed
    contDiff := bump.contDiff_normed
    hasCompactSupport := bump.hasCompactSupport_normed
    shift_mem := ?_ }
  intro displacement hdisplacement who
  have hsupport : displacement ∈ Function.support kernel :=
    Function.mem_support.mpr hdisplacement
  have hball : displacement ∈ Metric.ball (fun _ : coordinate ↦ -radius / 2)
      (radius / 4) := by
    change displacement ∈ Metric.ball (fun _ : coordinate ↦ -radius / 2)
      bump.rOut
    rw [← bump.support_normed_eq
      (μ := (volume : Measure (coordinate → ℝ)))]
    exact hsupport
  have hnorm : ‖displacement - (fun _ : coordinate ↦ -radius / 2)‖ < radius / 4 := by
    simpa only [Metric.mem_ball, dist_eq_norm] using hball
  have hcoordinateNorm :
      |displacement who - (-radius / 2)| ≤
        ‖displacement - (fun _ : coordinate ↦ -radius / 2)‖ := by
    simpa only [Pi.sub_apply, Real.norm_eq_abs] using
      (norm_le_pi_norm (displacement - (fun _ : coordinate ↦ -radius / 2)) who)
  have habs : |displacement who - (-radius / 2)| < radius / 4 :=
    hcoordinateNorm.trans_lt hnorm
  rw [abs_lt] at habs
  constructor <;> linarith

/-- Convolution against a one-sided kernel. -/
def OneSidedSmoothKernel.average {radius : ℝ}
    (kernel : OneSidedSmoothKernel coordinate radius)
    (function : (coordinate → ℝ) → ℝ) : (coordinate → ℝ) → ℝ :=
  function ⋆ kernel.toFun

/-- A locally integrable function becomes smooth after one-sided averaging. -/
theorem OneSidedSmoothKernel.contDiff_average {radius : ℝ}
    (kernel : OneSidedSmoothKernel coordinate radius)
    (function : (coordinate → ℝ) → ℝ)
    (hfunction : LocallyIntegrable function) :
    ContDiff ℝ ∞ (kernel.average function) := by
  exact kernel.hasCompactSupport.contDiff_convolution_right
    (ContinuousLinearMap.lsmul ℝ ℝ) hfunction kernel.contDiff

/-- Averaging preserves every common-translation drift inequality. -/
theorem OneSidedSmoothKernel.charge_add_average_le_average
    {radius charge : ℝ}
    (kernel : OneSidedSmoothKernel coordinate radius)
    (function : (coordinate → ℝ) → ℝ)
    (hfunction : LocallyIntegrable function)
    (source target : coordinate → ℝ)
    (hdrift : ∀ displacement, kernel displacement ≠ 0 →
      charge + function (target - displacement) ≤
        function (source - displacement)) :
    charge + kernel.average function target ≤
      kernel.average function source := by
  let multiplication : ℝ →L[ℝ] ℝ →L[ℝ] ℝ :=
    ContinuousLinearMap.lsmul ℝ ℝ
  have hkernelIntegrable : Integrable kernel.toFun :=
    kernel.contDiff.continuous.integrable_of_hasCompactSupport
      kernel.hasCompactSupport
  have htargetExists := kernel.hasCompactSupport.convolutionExists_right
    multiplication hfunction kernel.contDiff.continuous target
  have hsourceExists := kernel.hasCompactSupport.convolutionExists_right
    multiplication hfunction kernel.contDiff.continuous source
  have htargetIntegrable := htargetExists.integrable_swap
  have hsourceIntegrable := hsourceExists.integrable_swap
  have htargetIntegrable' : Integrable (fun displacement ↦
      function (target - displacement) * kernel displacement) := by
    simpa only [multiplication, ContinuousLinearMap.lsmul_apply, smul_eq_mul] using
      htargetIntegrable
  have hsourceIntegrable' : Integrable (fun displacement ↦
      function (source - displacement) * kernel displacement) := by
    simpa only [multiplication, ContinuousLinearMap.lsmul_apply, smul_eq_mul] using
      hsourceIntegrable
  have hleftIntegrable : Integrable (fun displacement ↦
      (charge + function (target - displacement)) * kernel displacement) := by
    have hconstant : Integrable (fun displacement ↦
        charge * kernel displacement) := hkernelIntegrable.const_mul charge
    refine (hconstant.add htargetIntegrable').congr ?_
    filter_upwards with displacement
    simp only [Pi.add_apply, add_mul]
  calc
    charge + kernel.average function target =
        charge + ∫ displacement,
          function (target - displacement) * kernel displacement := by
      rw [OneSidedSmoothKernel.average,
        MeasureTheory.convolution_lsmul_swap]
      simp only [smul_eq_mul]
    _ = charge * (∫ displacement, kernel displacement) +
        ∫ displacement,
          function (target - displacement) * kernel displacement := by
      rw [kernel.integral_one]
      ring
    _ = (∫ displacement, charge * kernel displacement) +
        ∫ displacement,
          function (target - displacement) * kernel displacement := by
      rw [integral_const_mul]
    _ = ∫ displacement,
        charge * kernel displacement +
          function (target - displacement) * kernel displacement := by
      rw [integral_add (hkernelIntegrable.const_mul charge)
        htargetIntegrable']
    _ = ∫ displacement,
        (charge + function (target - displacement)) * kernel displacement := by
      congr 1
      funext displacement
      ring
    _ ≤ ∫ displacement,
        function (source - displacement) * kernel displacement := by
      apply integral_mono hleftIntegrable hsourceIntegrable
      intro displacement
      by_cases hkernel : kernel displacement = 0
      · simp only [multiplication, ContinuousLinearMap.lsmul_apply,
          smul_zero, hkernel, mul_zero]
        exact le_rfl
      · exact mul_le_mul_of_nonneg_right (hdrift displacement hkernel)
          (kernel.nonneg displacement)
    _ = kernel.average function source := by
      rw [OneSidedSmoothKernel.average,
        MeasureTheory.convolution_lsmul_swap]
      simp only [smul_eq_mul]

end Math.OneSidedCapacitySmoothing
