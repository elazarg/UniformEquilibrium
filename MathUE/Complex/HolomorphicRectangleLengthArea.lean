module

public import MathUE.Analysis.RectangleLengthArea
public import MathUE.Complex.HolomorphicSphericalEnergy
public import Mathlib.MeasureTheory.Measure.Lebesgue.Complex

/-! # Actual short slices of a holomorphic complex chart

The speed is extended by zero outside the open holomorphic domain. Thus no
measurability of the arbitrary original function outside that domain is assumed.
The complex/real-product equivalence preserves the actual Lebesgue measure.
The resulting energy is derived from the map, not supplied as a certificate.
This is the analytic rectangle step of Milnor §§15.1–15.2, not a crosscut or
spherical-distance theorem, and it does not handle a chart containing infinity.
-/

public section

namespace Math.ComplexAnalysis

open MeasureTheory Set
open scoped ENNReal

@[expose] def openComplexSquare (width : ℝ) : Set ℂ :=
  Complex.measurableEquivRealProd.symm '' (Ioo 0 width ×ˢ Ioo 0 width)

@[expose] noncomputable def chartRectangleSpeed (f : ℂ → ℂ) (U : Set ℂ)
    (point : ℝ × ℝ) : ℝ≥0∞ :=
  U.indicator (fun z => ENNReal.ofReal (sphericalDerivativeSpeed f z))
    (Complex.measurableEquivRealProd.symm point)

@[expose] noncomputable def chartSquareEnergy (f : ℂ → ℂ) (U : Set ℂ)
    (width : ℝ) : ℝ≥0∞ :=
  ∫⁻ point, chartRectangleSpeed f U point ^ 2
    ∂(volume.restrict (Ioo 0 width)).prod (volume.restrict (Ioo 0 width))

theorem measurableSet_openComplexSquare (width : ℝ) :
    MeasurableSet (openComplexSquare width) :=
  Complex.measurableEquivRealProd.symm.measurableEmbedding.measurableSet_image.mpr
    (measurableSet_Ioo.prod measurableSet_Ioo)

theorem measurable_chartRectangleSpeed {f : ℂ → ℂ} {U : Set ℂ}
    (hU : IsOpen U) (hf : DifferentiableOn ℂ f U) :
    Measurable (chartRectangleSpeed f U) := by
  classical
  have hderiv := (hf.analyticOnNhd hU).deriv.continuousOn
  have hfunction := hf.continuousOn
  have hspeed : ContinuousOn (fun z => ENNReal.ofReal (sphericalDerivativeSpeed f z)) U := by
    apply ENNReal.continuous_ofReal.comp_continuousOn
    unfold sphericalDerivativeSpeed
    exact (continuousOn_const.mul hderiv.norm).div
      (continuousOn_const.add (hfunction.norm.pow 2)) (fun z _ => by positivity)
  exact (hspeed.measurable_piecewise continuousOn_const hU.measurableSet).comp
    Complex.measurableEquivRealProd.symm.measurable

theorem chartSquareEnergy_eq_actual_energy {f : ℂ → ℂ} {U : Set ℂ} {width : ℝ}
    (hcontained : openComplexSquare width ⊆ U) :
    chartSquareEnergy f U width =
      ∫⁻ z in openComplexSquare width,
        ENNReal.ofReal (sphericalDerivativeSpeed f z ^ 2) := by
  classical
  unfold chartSquareEnergy
  rw [Measure.prod_restrict]
  have htransport := Complex.volume_preserving_equiv_real_prod.symm.setLIntegral_comp_emb
    Complex.measurableEquivRealProd.symm.measurableEmbedding
    (fun z => ENNReal.ofReal (sphericalDerivativeSpeed f z ^ 2))
    (Ioo 0 width ×ˢ Ioo 0 width)
  unfold openComplexSquare
  rw [← Measure.volume_eq_prod ℝ ℝ, ← htransport]
  apply setLIntegral_congr_fun (measurableSet_Ioo.prod measurableSet_Ioo)
  intro point hpoint
  have hin : Complex.measurableEquivRealProd.symm point ∈ U :=
    hcontained ⟨point, hpoint, rfl⟩
  simp only [chartRectangleSpeed, indicator_of_mem hin]
  rw [ENNReal.ofReal_pow (by unfold sphericalDerivativeSpeed; positivity)]

theorem chartSquareEnergy_lt_top {f : ℂ → ℂ} {U : Set ℂ} {width : ℝ}
    (hU : IsOpen U) (hf : DifferentiableOn ℂ f U) (hinj : InjOn f U)
    (hcontained : openComplexSquare width ⊆ U) : chartSquareEnergy f U width < ∞ := by
  rw [chartSquareEnergy_eq_actual_energy hcontained]
  exact spherical_energy_lt_top hU hf hinj (measurableSet_openComplexSquare width) hcontained

/-- The displayed slice is the integral of the original map's actual speed. -/
theorem chart_slice_eq_actual {f : ℂ → ℂ} {U : Set ℂ} {width x : ℝ}
    (hcontained : openComplexSquare width ⊆ U) (hx : x ∈ Ioo 0 width) :
    (∫⁻ y in Ioo 0 width, chartRectangleSpeed f U (x, y)) =
      ∫⁻ y in Ioo 0 width,
        ENNReal.ofReal (sphericalDerivativeSpeed f
          (Complex.measurableEquivRealProd.symm (x, y))) := by
  apply setLIntegral_congr_fun measurableSet_Ioo
  intro y hy
  exact indicator_of_mem (hcontained ⟨(x, y), ⟨hx, hy⟩, rfl⟩) _

theorem chart_slice_finite_ae {f : ℂ → ℂ} {U : Set ℂ} {width : ℝ}
    (hU : IsOpen U) (hf : DifferentiableOn ℂ f U) (hinj : InjOn f U)
    (hcontained : openComplexSquare width ⊆ U) :
    ∀ᵐ x ∂volume.restrict (Ioo 0 width),
      (∫⁻ y in Ioo 0 width, chartRectangleSpeed f U (x, y)) < ∞ :=
  RectangleLengthArea.slice_lt_top_ae_of_energy_lt_top
    (measurable_chartRectangleSpeed hU hf) (chartSquareEnergy_lt_top hU hf hinj hcontained)

theorem chart_long_slices_le_quarter {f : ℂ → ℂ} {U : Set ℂ} {width : ℝ}
    (hU : IsOpen U) (hf : DifferentiableOn ℂ f U) (hinj : InjOn f U)
    (hcontained : openComplexSquare width ⊆ U)
    (hpositive : chartSquareEnergy f U width ≠ 0) :
    (volume.restrict (Ioo 0 width))
      {x | ENNReal.ofReal (2 * Real.sqrt (chartSquareEnergy f U width).toReal) ≤
        ∫⁻ y in Ioo 0 width, chartRectangleSpeed f U (x, y)} ≤
      ENNReal.ofReal width / 4 := by
  simpa only [chartSquareEnergy, Measure.restrict_apply_univ, Real.volume_Ioo, sub_zero] using
    RectangleLengthArea.measure_two_sqrt_energy_le_quarter
      (μ := volume.restrict (Ioo 0 width)) (ν := volume.restrict (Ioo 0 width))
      (measurable_chartRectangleSpeed hU hf) hpositive
      (chartSquareEnergy_lt_top hU hf hinj hcontained).ne

/-- A genuine short slice is selected inside the square. Zero energy gives
an exactly zero slice; positive energy gives the strict Milnor threshold. -/
theorem exists_chart_short_slice {f : ℂ → ℂ} {U : Set ℂ} {width : ℝ}
    (hwidth : 0 < width) (hU : IsOpen U) (hf : DifferentiableOn ℂ f U)
    (hinj : InjOn f U) (hcontained : openComplexSquare width ⊆ U) :
    ∃ x ∈ Ioo 0 width,
      (chartSquareEnergy f U width = 0 ∧
          (∫⁻ y in Ioo 0 width, chartRectangleSpeed f U (x, y)) = 0) ∨
        (∫⁻ y in Ioo 0 width, chartRectangleSpeed f U (x, y)) <
          ENNReal.ofReal (2 * Real.sqrt (chartSquareEnergy f U width).toReal) := by
  have hmeasure : volume (Ioo 0 width) ≠ 0 := by
    simpa only [Real.volume_Ioo, sub_zero] using (ENNReal.ofReal_pos.mpr hwidth).ne'
  by_cases hzero : chartSquareEnergy f U width = 0
  · have hae := RectangleLengthArea.slice_eq_zero_ae_of_energy_zero
      (μ := volume.restrict (Ioo 0 width)) (ν := volume.restrict (Ioo 0 width))
      (measurable_chartRectangleSpeed hU hf) hzero
    obtain ⟨x, hx, hslice⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae hmeasure hae
    exact ⟨x, hx, Or.inl ⟨hzero, hslice⟩⟩
  · by_contra hnot
    have hall : ∀ x ∈ Ioo 0 width,
        ENNReal.ofReal (2 * Real.sqrt (chartSquareEnergy f U width).toReal) ≤
          ∫⁻ y in Ioo 0 width, chartRectangleSpeed f U (x, y) := by
      intro x hx
      exact le_of_not_gt fun hlt => hnot ⟨x, hx, Or.inr hlt⟩
    have hlower := measure_mono (μ := volume.restrict (Ioo 0 width)) hall
    rw [Measure.restrict_apply_self, Real.volume_Ioo, sub_zero] at hlower
    have hquarter := hlower.trans (chart_long_slices_le_quarter hU hf hinj hcontained hzero)
    have hstrict : ENNReal.ofReal width / 4 < ENNReal.ofReal width := by
      rw [ENNReal.div_lt_iff (Or.inl (by norm_num)) (Or.inl (by norm_num))]
      simpa only [one_mul, mul_one, mul_comm] using ENNReal.mul_lt_mul_left
        (ENNReal.ofReal_pos.mpr hwidth).ne' ENNReal.ofReal_ne_top
        (show (1 : ℝ≥0∞) < 4 by norm_num)
    exact hstrict.not_ge hquarter

end Math.ComplexAnalysis
