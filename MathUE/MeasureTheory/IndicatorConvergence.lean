import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.Normed.Group.Indicator

/-! # Integrable tests under eventually agreeing indicator masks

Almost-everywhere eventual membership agreement makes fixed integrable tests
converge in L1 under moving measurable masks. The measure is arbitrary and the
test takes values in any normed additive commutative group. Measurability of the
limiting mask is derived, not imposed on its set.
-/

noncomputable section

namespace MeasureTheory

open Filter
open scoped Topology

/-- Eventually agreeing memberships give norm-integral convergence for every integrable test. -/
theorem tendsto_integral_norm_indicator_sub_of_ae_eventually_mem_iff
    {X E : Type*} [MeasurableSpace X] [NormedAddCommGroup E]
    (measure : Measure X) (sets : ℕ → Set X) (limit : Set X)
    (hsets : ∀ k, MeasurableSet (sets k)) (test : X → E) (htest : Integrable test measure)
    (hmembership : ∀ᵐ x ∂measure, ∀ᶠ k in atTop, x ∈ sets k ↔ x ∈ limit) :
    Tendsto (fun k => ∫ x, ‖(sets k).indicator test x - limit.indicator test x‖ ∂measure)
      atTop (𝓝 0) := by
  classical
  have hmeasurable (k : ℕ) : AEStronglyMeasurable ((sets k).indicator test) measure :=
    htest.aestronglyMeasurable.indicator (hsets k)
  have hlimit : ∀ᵐ x ∂measure,
      Tendsto (fun k => (sets k).indicator test x) atTop (𝓝 (limit.indicator test x)) := by
    filter_upwards [hmembership] with x hx
    apply tendsto_const_nhds.congr'
    filter_upwards [hx] with k hk
    by_cases hmem : x ∈ limit
    · simp only [Set.indicator_of_mem (hk.mpr hmem), Set.indicator_of_mem hmem]
    · simp only [Set.indicator_of_notMem (fun h => hmem (hk.mp h)),
        Set.indicator_of_notMem hmem]
  have h := tendsto_lintegral_norm_of_dominated_convergence hmeasurable
    htest.norm.hasFiniteIntegral
    (fun k => Eventually.of_forall fun x => norm_indicator_le_norm_self _ _) hlimit
  have hlimitMeasurable := aestronglyMeasurable_of_tendsto_ae atTop hmeasurable hlimit
  have hintegral (k : ℕ) :
      ∫ x, ‖(sets k).indicator test x - limit.indicator test x‖ ∂measure =
        (∫⁻ x, ENNReal.ofReal ‖(sets k).indicator test x - limit.indicator test x‖
          ∂measure).toReal :=
    integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun _ => norm_nonneg _)
      ((hmeasurable k).sub hlimitMeasurable).norm
  simpa only [Function.comp_def, ← hintegral, ENNReal.toReal_zero] using
    (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp h

end MeasureTheory
