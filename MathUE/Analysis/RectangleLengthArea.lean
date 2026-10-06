module

public import Mathlib.MeasureTheory.Integral.MeanInequalities
public import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-! # The rectangle length–area estimate

The Cauchy–Schwarz, Tonelli and exceptional-set argument of Milnor,
*Dynamics in One Complex Variable*, §§15.1–15.2:
https://legacy-www.math.harvard.edu/archive/118r_spring_05/docs/milnor.pdf

Lengths are actual integrals of the nonnegative speed, and energy is its actual
square integral. The general product-measure statements specialize to rectangles.
Zero energy is handled without dividing by energy. These are measure-theoretic
estimates, not a conformal spherical-area formula or a crosscut construction.
-/

public section

namespace Math.RectangleLengthArea

open MeasureTheory Set
open scoped ENNReal

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
variable {μ : Measure X} {ν : Measure Y}

theorem sq_lintegral_le_measure_mul_lintegral_sq
    {speed : Y → ℝ≥0∞} (hspeed : Measurable speed) :
    (∫⁻ y, speed y ∂ν) ^ 2 ≤ ν univ * ∫⁻ y, speed y ^ 2 ∂ν := by
  have hholder := ENNReal.lintegral_mul_le_Lp_mul_Lq ν
    (show Real.HolderConjugate 2 2 by norm_num [Real.holderConjugate_iff])
    measurable_const.aemeasurable hspeed.aemeasurable
      (f := fun _ : Y => (1 : ℝ≥0∞))
  simp only [Pi.mul_apply, one_mul, ENNReal.rpow_two, one_pow, lintegral_one] at hholder
  have hsqrt (t : ℝ≥0∞) : (t ^ (1 / 2 : ℝ)) ^ 2 = t := by
    rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
    norm_num
  have hsquared := pow_le_pow_left' hholder 2
  simpa only [mul_pow, hsqrt] using hsquared

variable [SFinite ν]

/-- The square of each slice length, integrated across the rectangle. -/
theorem lintegral_slice_sq_le
    {speed : X × Y → ℝ≥0∞} (hspeed : Measurable speed) :
    (∫⁻ x, (∫⁻ y, speed (x, y) ∂ν) ^ 2 ∂μ) ≤
      ν univ * ∫⁻ point, speed point ^ 2 ∂μ.prod ν := by
  calc
    _ ≤ ∫⁻ x, ν univ * ∫⁻ y, speed (x, y) ^ 2 ∂ν ∂μ :=
      lintegral_mono fun x => sq_lintegral_le_measure_mul_lintegral_sq
        (hspeed.comp (measurable_const.prodMk measurable_id))
    _ = _ := by
      rw [lintegral_const_mul _ ((hspeed.pow_const 2).lintegral_prod_right'),
        ← lintegral_prod _ (hspeed.pow_const 2).aemeasurable]

/-- A bound for the actual set of long slices, including when energy is zero. -/
theorem measure_long_slices_le
    {speed : X × Y → ℝ≥0∞} (hspeed : Measurable speed)
    {threshold : ℝ≥0∞} (hpositive : threshold ≠ 0) (hfinite : threshold ≠ ∞) :
    μ {x | threshold ≤ ∫⁻ y, speed (x, y) ∂ν} ≤
      (ν univ * ∫⁻ point, speed point ^ 2 ∂μ.prod ν) / threshold ^ 2 := by
  have hmeas := hspeed.lintegral_prod_right' (ν := ν)
  calc
    _ ≤ μ {x | threshold ^ 2 ≤ (∫⁻ y, speed (x, y) ∂ν) ^ 2} :=
      measure_mono fun x hx => pow_le_pow_left' hx 2
    _ ≤ (∫⁻ x, (∫⁻ y, speed (x, y) ∂ν) ^ 2 ∂μ) / threshold ^ 2 :=
      meas_ge_le_lintegral_div (hmeas.pow_const 2).aemeasurable
        (pow_ne_zero _ hpositive) (by simp [hfinite])
    _ ≤ _ := ENNReal.div_le_div_right (lintegral_slice_sq_le hspeed) _

theorem slice_eq_zero_ae_of_energy_zero
    {speed : X × Y → ℝ≥0∞} (hspeed : Measurable speed)
    (henergy : (∫⁻ point, speed point ^ 2 ∂μ.prod ν) = 0) :
    ∀ᵐ x ∂μ, (∫⁻ y, speed (x, y) ∂ν) = 0 := by
  have hzero : (∫⁻ x, (∫⁻ y, speed (x, y) ∂ν) ^ 2 ∂μ) = 0 := by
    have hbound : (∫⁻ x, (∫⁻ y, speed (x, y) ∂ν) ^ 2 ∂μ) ≤ 0 := by
      simpa only [henergy, mul_zero] using lintegral_slice_sq_le (μ := μ) (ν := ν) hspeed
    exact le_antisymm hbound zero_le
  have hae := (lintegral_eq_zero_iff (hspeed.lintegral_prod_right'.pow_const 2)).mp hzero
  filter_upwards [hae] with x hx
  exact eq_zero_of_pow_eq_zero hx

/-- Milnor's quantitative threshold, with positive finite energy computed from
the speed. The zero-energy case is the preceding almost-everywhere equality. -/
theorem measure_two_sqrt_energy_le_quarter
    {speed : X × Y → ℝ≥0∞} (hspeed : Measurable speed)
    (hpositive : (∫⁻ point, speed point ^ 2 ∂μ.prod ν) ≠ 0)
    (hfinite : (∫⁻ point, speed point ^ 2 ∂μ.prod ν) ≠ ∞) :
    μ {x | ENNReal.ofReal
        (2 * Real.sqrt (∫⁻ point, speed point ^ 2 ∂μ.prod ν).toReal) ≤
      ∫⁻ y, speed (x, y) ∂ν} ≤ ν univ / 4 := by
  let energy := ∫⁻ point, speed point ^ 2 ∂μ.prod ν
  have hreal : 0 < energy.toReal := ENNReal.toReal_pos hpositive hfinite
  have hthreshold : 0 < 2 * Real.sqrt energy.toReal :=
    mul_pos (by norm_num) (Real.sqrt_pos.mpr hreal)
  have hsquare : ENNReal.ofReal (2 * Real.sqrt energy.toReal) ^ 2 = 4 * energy := by
    rw [← ENNReal.ofReal_pow hthreshold.le, mul_pow, Real.sq_sqrt hreal.le]
    norm_num only [show (2 : ℝ) ^ 2 = 4 by norm_num]
    rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_toReal hfinite]
    norm_num [energy]
  have hbound := measure_long_slices_le (μ := μ) (ν := ν) hspeed
    (ENNReal.ofReal_pos.mpr hthreshold).ne' ENNReal.ofReal_ne_top
  change μ {x | ENNReal.ofReal (2 * Real.sqrt energy.toReal) ≤
      ∫⁻ y, speed (x, y) ∂ν} ≤ ν univ / 4
  refine hbound.trans_eq ?_
  rw [hsquare]
  exact ENNReal.mul_div_mul_right (ν univ) 4 hpositive hfinite

theorem slice_lt_top_ae_of_energy_lt_top [IsFiniteMeasure ν]
    {speed : X × Y → ℝ≥0∞} (hspeed : Measurable speed)
    (henergy : (∫⁻ point, speed point ^ 2 ∂μ.prod ν) < ∞) :
    ∀ᵐ x ∂μ, (∫⁻ y, speed (x, y) ∂ν) < ∞ := by
  have hbound := (lintegral_slice_sq_le hspeed).trans_lt
    (ENNReal.mul_lt_top (measure_lt_top ν univ) henergy)
  have hae := ae_lt_top (hspeed.lintegral_prod_right'.pow_const 2) hbound.ne
  filter_upwards [hae] with x hx
  by_contra hnot
  have heq : (∫⁻ y, speed (x, y) ∂ν) = ∞ := top_le_iff.mp (not_lt.mp hnot)
  simp [heq] at hx

/-- Literal rectangles; no conformality or source-area witness is assumed. -/
theorem rectangle_lintegral_slice_sq_le
    {speed : ℝ × ℝ → ℝ≥0∞} (hspeed : Measurable speed) (a b c d : ℝ) :
    (∫⁻ x in Ioc a b, (∫⁻ y in Ioc c d, speed (x, y)) ^ 2) ≤
      ENNReal.ofReal (d - c) *
        ∫⁻ point, speed point ^ 2 ∂(volume.restrict (Ioc a b)).prod
          (volume.restrict (Ioc c d)) := by
  simpa only [Measure.restrict_apply_univ, Real.volume_Ioc] using
    (lintegral_slice_sq_le (μ := volume.restrict (Ioc a b))
      (ν := volume.restrict (Ioc c d)) hspeed)

end Math.RectangleLengthArea
