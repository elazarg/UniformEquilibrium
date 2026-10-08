import MathUE.Probability.SignedConditioningLikelihood
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Probability.ConditionalProbability

/-! # Signed conditioning of measurable probability laws

A positive measurable event supplies a two-sided signed variation toward its
ordinary conditional law. The actual nonnegative likelihood constructs a
probability measure, with likelihood between one half and three halves on the
closed signed radius. Both absolute continuity directions and the affine
integral formula are derived. No topology or atomlessness is required.

The distant parameter one is not placed in the small signed radius. Ordinary
conditioning is the existing `ProbabilityTheory.cond` measure, and appears only
in the valid affine integral interpretation.
-/

noncomputable section

open Set Filter

namespace MeasureTheory.ProbabilityMeasure

variable {X : Type*} [MeasurableSpace X]

def signedCondRadius (law : ProbabilityMeasure X) (event : Set X) : ℝ :=
  min (1 / 2 : ℝ) ((law : Measure X).real event / 2)

theorem signedCondRadius_pos (law : ProbabilityMeasure X) (event : Set X)
    (hmass : 0 < (law : Measure X).real event) : 0 < law.signedCondRadius event := by
  unfold signedCondRadius
  exact lt_min (by norm_num) (by positivity)

def signedCondLikelihood (law : ProbabilityMeasure X) (event : Set X)
    (parameter : ℝ) (x : X) : ℝ :=
  (1 - parameter) + event.indicator (fun _ => parameter / (law : Measure X).real event) x

theorem measurable_signedCondLikelihood (law : ProbabilityMeasure X) (event : Set X)
    (hevent : MeasurableSet event) (parameter : ℝ) :
    Measurable (law.signedCondLikelihood event parameter) :=
  measurable_const.add (measurable_const.indicator hevent)

theorem signedCondLikelihood_bounds (law : ProbabilityMeasure X) (event : Set X)
    (hmass : 0 < (law : Measure X).real event) (parameter : ℝ)
    (hparameter : |parameter| ≤ law.signedCondRadius event) (x : X) :
    (1 / 2 : ℝ) ≤ law.signedCondLikelihood event parameter x ∧
      law.signedCondLikelihood event parameter x ≤ 3 / 2 := by
  classical
  have hmassOne : (law : Measure X).real event ≤ 1 := by
    simpa only [measureReal_def, measure_univ, ENNReal.toReal_one] using
      (measureReal_mono (μ := (law : Measure X)) (subset_univ event))
  simpa only [signedCondLikelihood, Set.indicator_apply] using
    Math.Probability.signedConditioningLikelihood_bounds
      ((law : Measure X).real event) hmass hmassOne parameter hparameter (x ∈ event)

theorem integrable_signedCondLikelihood (law : ProbabilityMeasure X) (event : Set X)
    (hevent : MeasurableSet event) (parameter : ℝ) :
    Integrable (law.signedCondLikelihood event parameter) (law : Measure X) :=
  (integrable_const _).add ((integrable_const _).indicator hevent)

theorem integral_signedCondLikelihood (law : ProbabilityMeasure X) (event : Set X)
    (hevent : MeasurableSet event) (hmass : 0 < (law : Measure X).real event)
    (parameter : ℝ) : ∫ x, law.signedCondLikelihood event parameter x ∂(law : Measure X) = 1 := by
  unfold signedCondLikelihood
  rw [integral_add (integrable_const _) ((integrable_const _).indicator hevent),
    integral_const, integral_indicator_const _ hevent]
  have huniv : (law : Measure X).real univ = 1 := by
    simp only [measureReal_def, measure_univ, ENNReal.toReal_one]
  rw [huniv, one_smul, smul_eq_mul, mul_div_cancel₀ _ hmass.ne']
  ring

/-- The probability law is built from the actual likelihood, not a normalization oracle. -/
def signedCond (law : ProbabilityMeasure X) (event : Set X) (hevent : MeasurableSet event)
    (hmass : 0 < (law : Measure X).real event) (parameter : ℝ)
    (hparameter : |parameter| ≤ law.signedCondRadius event) : ProbabilityMeasure X :=
  ⟨(law : Measure X).withDensity (fun x => ENNReal.ofReal
      (law.signedCondLikelihood event parameter x)), ⟨by
    rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
      ← ofReal_integral_eq_lintegral_ofReal
        (integrable_signedCondLikelihood law event hevent parameter)
        (Eventually.of_forall fun x => (by norm_num : (0 : ℝ) ≤ 1 / 2).trans
          (signedCondLikelihood_bounds law event hmass parameter hparameter x).1),
      integral_signedCondLikelihood law event hevent hmass parameter, ENNReal.ofReal_one]⟩⟩

theorem coe_signedCond (law : ProbabilityMeasure X) (event : Set X)
    (hevent : MeasurableSet event) (hmass : 0 < (law : Measure X).real event)
    (parameter : ℝ) (hparameter : |parameter| ≤ law.signedCondRadius event) :
    (law.signedCond event hevent hmass parameter hparameter : Measure X) =
      (law : Measure X).withDensity (fun x => ENNReal.ofReal
        (law.signedCondLikelihood event parameter x)) := rfl

/-- Both measure bounds hold on the closed signed radius. -/
theorem signedCond_bounds (law : ProbabilityMeasure X) (event : Set X)
    (hevent : MeasurableSet event) (hmass : 0 < (law : Measure X).real event)
    (parameter : ℝ) (hparameter : |parameter| ≤ law.signedCondRadius event) :
    (1 / 2 : ENNReal) • (law : Measure X) ≤
        (law.signedCond event hevent hmass parameter hparameter : Measure X) ∧
      (law.signedCond event hevent hmass parameter hparameter : Measure X) ≤
        (3 / 2 : ENNReal) • (law : Measure X) := by
  rw [coe_signedCond]
  constructor
  · calc
      _ = (law : Measure X).withDensity (fun _ => ENNReal.ofReal (1 / 2 : ℝ)) := by
        rw [withDensity_const, ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2)]
        norm_num
      _ ≤ _ := withDensity_mono (Eventually.of_forall fun x => ENNReal.ofReal_le_ofReal
        (signedCondLikelihood_bounds law event hmass parameter hparameter x).1)
  · calc
      _ ≤ (law : Measure X).withDensity (fun _ => ENNReal.ofReal (3 / 2 : ℝ)) :=
        withDensity_mono (Eventually.of_forall fun x => ENNReal.ofReal_le_ofReal
          (signedCondLikelihood_bounds law event hmass parameter hparameter x).2)
      _ = _ := by
        rw [withDensity_const, ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2)]
        norm_num

theorem signedCond_mutuallyAbsolutelyContinuous (law : ProbabilityMeasure X) (event : Set X)
    (hevent : MeasurableSet event) (hmass : 0 < (law : Measure X).real event)
    (parameter : ℝ) (hparameter : |parameter| ≤ law.signedCondRadius event) :
    (law.signedCond event hevent hmass parameter hparameter : Measure X) ≪ (law : Measure X) ∧
      (law : Measure X) ≪ (law.signedCond event hevent hmass parameter hparameter : Measure X) := by
  obtain ⟨hlower, hupper⟩ := signedCond_bounds law event hevent hmass parameter hparameter
  refine ⟨Measure.absolutelyContinuous_of_le_smul hupper, ?_⟩
  exact (Measure.absolutelyContinuous_smul (by norm_num : (1 / 2 : ENNReal) ≠ 0)).trans
    (Measure.absolutelyContinuous_of_le hlower)

theorem integrable_signedCond (law : ProbabilityMeasure X) (event : Set X)
    (hevent : MeasurableSet event) (hmass : 0 < (law : Measure X).real event)
    (parameter : ℝ) (hparameter : |parameter| ≤ law.signedCondRadius event)
    {test : X → ℝ} (htest : Integrable test (law : Measure X)) :
    Integrable test (law.signedCond event hevent hmass parameter hparameter : Measure X) :=
  (htest.smul_measure (ENNReal.div_ne_top (by norm_num : (3 : ENNReal) ≠ ⊤)
    (by norm_num : (2 : ENNReal) ≠ 0))).mono_measure
    (signedCond_bounds law event hevent hmass parameter hparameter).2

/-- Every integrable test has the literal affine conditional-expectation formula. -/
theorem integral_signedCond (law : ProbabilityMeasure X) (event : Set X)
    (hevent : MeasurableSet event) (hmass : 0 < (law : Measure X).real event)
    (parameter : ℝ) (hparameter : |parameter| ≤ law.signedCondRadius event)
    (test : X → ℝ) (htest : Integrable test (law : Measure X)) :
    ∫ x, test x ∂(law.signedCond event hevent hmass parameter hparameter : Measure X) =
      (1 - parameter) * (∫ x, test x ∂(law : Measure X)) +
        (parameter / (law : Measure X).real event) * ∫ x in event, test x ∂(law : Measure X) := by
  rw [coe_signedCond, integral_withDensity_eq_integral_toReal_smul
    (measurable_signedCondLikelihood law event hevent parameter).ennreal_ofReal
    (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  have hpointwise (x : X) :
      (ENNReal.ofReal (law.signedCondLikelihood event parameter x)).toReal • test x =
        (1 - parameter) * test x +
          (parameter / (law : Measure X).real event) * event.indicator test x := by
    rw [ENNReal.toReal_ofReal ((by norm_num : (0 : ℝ) ≤ 1 / 2).trans
      (signedCondLikelihood_bounds law event hmass parameter hparameter x).1), smul_eq_mul]
    classical
    by_cases hx : x ∈ event
    · simp only [signedCondLikelihood, Set.indicator_of_mem hx]
      ring
    · simp only [signedCondLikelihood, Set.indicator_of_notMem hx, add_zero, mul_zero]
  simp_rw [hpointwise]
  rw [integral_add (htest.const_mul _) ((htest.indicator hevent).const_mul _),
    integral_const_mul, integral_const_mul, integral_indicator hevent]

/-- The ordinary conditional is only an interpretation of the affine integral formula. -/
theorem integral_signedCond_eq_affine_cond (law : ProbabilityMeasure X) (event : Set X)
    (hevent : MeasurableSet event) (hmass : 0 < (law : Measure X).real event)
    (parameter : ℝ) (hparameter : |parameter| ≤ law.signedCondRadius event)
    (test : X → ℝ) (htest : Integrable test (law : Measure X)) :
    ∫ x, test x ∂(law.signedCond event hevent hmass parameter hparameter : Measure X) =
      (1 - parameter) * (∫ x, test x ∂(law : Measure X)) +
        parameter * ∫ x, test x ∂ProbabilityTheory.cond (law : Measure X) event := by
  rw [integral_signedCond law event hevent hmass parameter hparameter test htest,
    ProbabilityTheory.cond, integral_smul_measure, ENNReal.toReal_inv]
  simp only [smul_eq_mul, measureReal_def, div_eq_mul_inv, mul_assoc]

theorem signedCond_zero (law : ProbabilityMeasure X) (event : Set X)
    (hevent : MeasurableSet event) (hmass : 0 < (law : Measure X).real event) :
    law.signedCond event hevent hmass 0
      (by simpa only [abs_zero] using (signedCondRadius_pos law event hmass).le) = law := by
  apply toMeasure_injective
  rw [coe_signedCond]
  have hlikelihood : (fun x => ENNReal.ofReal (law.signedCondLikelihood event 0 x)) = 1 := by
    funext x
    simp [signedCondLikelihood]
  rw [hlikelihood, withDensity_one]

/-- A mass-one event is a redundant direction; positivity is derived from its mass. -/
theorem signedCond_eq_self_of_measureReal_eq_one (law : ProbabilityMeasure X) (event : Set X)
    (hevent : MeasurableSet event) (hmass : (law : Measure X).real event = 1)
    (parameter : ℝ) (hparameter : |parameter| ≤ law.signedCondRadius event) :
    law.signedCond event hevent (by rw [hmass]; norm_num) parameter hparameter = law := by
  have hmeasure : (law : Measure X) event = 1 := by
    rw [← ENNReal.ofReal_toReal (measure_ne_top (law : Measure X) event)]
    change ENNReal.ofReal ((law : Measure X).real event) = 1
    rw [hmass, ENNReal.ofReal_one]
  have hae : ∀ᵐ x ∂(law : Measure X), x ∈ event :=
    (mem_ae_iff_prob_eq_one hevent).mpr hmeasure
  apply toMeasure_injective
  rw [coe_signedCond]
  calc
    _ = (law : Measure X).withDensity 1 := by
      apply withDensity_congr_ae
      filter_upwards [hae] with x hx
      simp only [signedCondLikelihood, Set.indicator_of_mem hx, hmass, div_one,
        sub_add_cancel, ENNReal.ofReal_one, Pi.one_apply]
    _ = (law : Measure X) := withDensity_one

end MeasureTheory.ProbabilityMeasure
