import Research.MarkedCalendar.SupportedAtomVariation
import Mathlib.Probability.ConditionalProbability

/-! # Ordinary conditioning on unchanged reference cells

Positive finite cell events compile to the ordinary conditional measure on the
same old latent chart. Selected-cell conditioning leaves the original law intact
at zero-mass source indices. A positive limiting retained-gap mass derives the
eventual normalization bound and the actual conditional weak limit on the same
source subsequence.

This is the ordinary conditioning endpoint, not the signed constructor evaluated
at parameter one. Chronological moving-cut producers and joint semantic carrier
consumers remain separate subsequent adapters.
-/

noncomputable section

open Set Filter MeasureTheory TopologicalSpace GameTheory.Math.Probability
open scoped Topology

namespace GameTheory.MarkedCalendarChart

variable {ι : Type} [Fintype ι] [Nonempty ι]

/-- Ordinary finite conditioning compiles to the literal conditional measure on the old chart.
The positive support witness and the latent normalizer are derived from the finite event mass. -/
theorem referenceMeasure_condOn (reference : ι → FinDist (Option ℕ))
    (p : FinDist (Cell reference)) (event : Set (Cell reference))
    (hmass : 0 < p.probOf event) :
    referenceMeasure reference
        (p.condOn event (p.exists_mem_support_of_probOf_pos event hmass)) =
      ProbabilityTheory.cond (referenceMeasure reference p) (decodeCell reference ⁻¹' event) := by
  classical
  have hevent : MeasurableSet (decodeCell reference ⁻¹' event) :=
    event.toFinite.measurableSet.preimage (measurable_decodeCell reference)
  have hnormalizer : referenceMeasure reference p (decodeCell reference ⁻¹' event) =
      ENNReal.ofReal (p.probOf event) := by
    rw [← ENNReal.ofReal_toReal
      (measure_ne_top (referenceMeasure reference p) (decodeCell reference ⁻¹' event))]
    exact congrArg ENNReal.ofReal (referenceLaw_decodeCell_event_real reference p event)
  rw [ProbabilityTheory.cond, hnormalizer]
  change volume.withDensity _ = (ENNReal.ofReal (p.probOf event))⁻¹ •
    (volume.withDensity (fun x => ENNReal.ofReal (referenceDensity reference p x))).restrict
      (decodeCell reference ⁻¹' event)
  rw [restrict_withDensity hevent, ← withDensity_indicator hevent,
    ← withDensity_smul _
      ((measurable_referenceDensity reference p).ennreal_ofReal.indicator hevent)]
  apply withDensity_congr_ae
  filter_upwards [ae_mem_interval reference] with x hx
  obtain ⟨cell, hcell⟩ := hx
  change ENNReal.ofReal
      (referenceDensity reference
        (p.condOn event (p.exists_mem_support_of_probOf_pos event hmass)) x) =
    (ENNReal.ofReal (p.probOf event))⁻¹ *
      (decodeCell reference ⁻¹' event).indicator
        (fun y => ENNReal.ofReal (referenceDensity reference p y)) x
  rw [referenceDensity_eq_of_mem_interval reference _ hcell, FinDist.prob_condOn]
  have hdecode := decodeCell_of_mem_interval reference hcell
  by_cases hmem : cell ∈ event
  · rw [ite_eq_left hmem, Set.indicator_of_mem (by simpa only [mem_preimage, hdecode] using hmem),
      referenceDensity_eq_of_mem_interval reference p hcell, div_right_comm,
      ENNReal.ofReal_div_of_pos hmass]
    simp only [div_eq_mul_inv, mul_comm]
  · rw [ite_eq_right hmem, zero_div, ENNReal.ofReal_zero,
      Set.indicator_of_notMem (by simpa only [mem_preimage, hdecode] using hmem), mul_zero]

/-- An ordinary conditional with safe original-law fallback when its source event is null. -/
def conditionalCellLaw (reference : ι → FinDist (Option ℕ))
    (p : FinDist (Cell reference)) (event : Set (Cell reference)) : FinDist (Cell reference) := by
  classical
  exact if hmass : 0 < p.probOf event then
    p.condOn event (p.exists_mem_support_of_probOf_pos event hmass)
  else p

theorem prob_conditionalCellLaw_le (reference : ι → FinDist (Option ℕ))
    (p : FinDist (Cell reference)) (event : Set (Cell reference))
    (hmass : 0 < p.probOf event) (a : Cell reference) :
    (conditionalCellLaw reference p event).prob a ≤ p.prob a / p.probOf event := by
  classical
  rw [conditionalCellLaw, dite_eq_left hmass, FinDist.prob_condOn]
  split
  · exact le_rfl
  · exact div_nonneg (p.prob_nonneg a) hmass.le

def conditionalSelectedCellLaw (laws : ι → FinDist (Option ℕ)) (i : ι)
    (x : unitInterval) : FinDist (Cell laws) :=
  conditionalCellLaw laws (cellLaw laws i) {decodeCell laws x}

omit [Fintype ι] [Nonempty ι] in
/-- The limiting endpoint is the existing ordinary conditional measure, with positivity derived
by the source producer before this definition is used. -/
def gapConditionalLaw (law : ProbabilityMeasure unitInterval) (a b : ℝ)
    (hmass : 0 < (law : Measure unitInterval).real
      {x | a < (x : ℝ) ∧ (x : ℝ) < b}) : ProbabilityMeasure unitInterval :=
  ⟨ProbabilityTheory.cond (law : Measure unitInterval)
    {x | a < (x : ℝ) ∧ (x : ℝ) < b},
    ProbabilityTheory.cond_isProbabilityMeasure (ENNReal.toReal_pos_iff.mp hmass).1.ne'⟩

omit [Fintype ι] [Nonempty ι] in
theorem integral_gapConditionalLaw (law : ProbabilityMeasure unitInterval) (a b : ℝ)
    (hmass : 0 < (law : Measure unitInterval).real
      {x | a < (x : ℝ) ∧ (x : ℝ) < b}) (test : unitInterval → ℝ) :
    ∫ x, test x ∂(gapConditionalLaw law a b hmass : Measure unitInterval) =
      (∫ x in {y | a < (y : ℝ) ∧ (y : ℝ) < b}, test x ∂(law : Measure unitInterval)) /
        (law : Measure unitInterval).real {x | a < (x : ℝ) ∧ (x : ℝ) < b} := by
  change (∫ x, test x ∂ProbabilityTheory.cond (law : Measure unitInterval) _) = _
  rw [ProbabilityTheory.cond, integral_smul_measure, ENNReal.toReal_inv]
  simp only [smul_eq_mul, measureReal_def, div_eq_mul_inv, mul_comm]

private theorem integral_referenceLaw_conditionalSelectedCellLaw
    (laws : ι → FinDist (Option ℕ)) (i : ι) (x : unitInterval)
    (hpositive : 0 < (cellLaw laws i).prob (decodeCell laws x))
    (test : unitInterval → ℝ) :
    ∫ y, test y ∂(referenceLaw laws (conditionalSelectedCellLaw laws i x) :
      Measure unitInterval) =
        (∫ y, (interval laws (decodeCell laws x)).indicator test y
          ∂(chartLaw laws i : Measure unitInterval)) /
            (cellLaw laws i).prob (decodeCell laws x) := by
  have hmass : 0 < (cellLaw laws i).probOf {decodeCell laws x} := by
    simpa only [FinDist.probOf_singleton] using hpositive
  change (∫ y, test y ∂referenceMeasure laws
    (conditionalCellLaw laws (cellLaw laws i) {decodeCell laws x})) = _
  rw [conditionalCellLaw, dite_eq_left hmass, referenceMeasure_condOn laws _ _ hmass,
    ProbabilityTheory.cond, integral_smul_measure, ENNReal.toReal_inv]
  have hsets : decodeCell laws ⁻¹' {decodeCell laws x}
      =ᵐ[(chartLaw laws i : Measure unitInterval)] interval laws (decodeCell laws x) := by
    filter_upwards [ae_decodeCell_mem_interval laws i] with y hy
    apply propext
    change decodeCell laws y = decodeCell laws x ↔ y ∈ interval laws (decodeCell laws x)
    exact ⟨fun h => h ▸ hy, decodeCell_of_mem_interval laws⟩
  have hevent : MeasurableSet (decodeCell laws ⁻¹' {decodeCell laws x}) :=
    (measurableSet_singleton _).preimage (measurable_decodeCell laws)
  have hintegral := integral_congr_ae (indicator_ae_eq_of_ae_eq_set (f := test) hsets)
  rw [integral_indicator hevent] at hintegral
  change ((chartLaw laws i : Measure unitInterval).real
      (decodeCell laws ⁻¹' {decodeCell laws x}))⁻¹ *
      (∫ y in decodeCell laws ⁻¹' {decodeCell laws x}, test y
        ∂(chartLaw laws i : Measure unitInterval)) = _
  rw [hintegral]
  have hmassEq := referenceLaw_decodeCell_event_real laws (cellLaw laws i) {decodeCell laws x}
  change (chartLaw laws i : Measure unitInterval).real _ = _ at hmassEq
  rw [hmassEq, FinDist.probOf_singleton, div_eq_mul_inv, mul_comm]

/-- Positive limiting mass supplies an eventual common density bound; no bound is supplied. -/
theorem eventually_conditionalSelectedCellLaw_le
    (source : ℕ → ι → FinDist (Option ℕ)) (subsequence : ℕ → ℕ)
    {limit : MathUE.MarkedCalendar.Calendar}
    (hE : Tendsto (fun k => (calendar (source (subsequence k))).endpoints) atTop
      (𝓝 limit.endpoints)) (i : ι) {law : ProbabilityMeasure unitInterval}
    (hlaw : Tendsto (fun k => chartLaw (source (subsequence k)) i) atTop (𝓝 law))
    {a b : ℝ} (hgap : Math.Topology.IsGap limit.endpoints a b)
    {x : unitInterval} (hax : a < (x : ℝ)) (hxb : (x : ℝ) < b)
    (hmass : 0 < (law : Measure unitInterval).real {y | a < (y : ℝ) ∧ (y : ℝ) < b}) :
    ∀ᶠ k in atTop, ∀ cell : Cell (source (subsequence k)),
      (conditionalSelectedCellLaw (source (subsequence k)) i x).prob cell ≤
        ((2 / (law : Measure unitInterval).real {y | a < (y : ℝ) ∧ (y : ℝ) < b}) *
          Fintype.card ι) * weight (source (subsequence k)) cell := by
  let mass := (law : Measure unitInterval).real {y | a < (y : ℝ) ∧ (y : ℝ) < b}
  have hmasslim := tendsto_decodeCell_ownMass_of_limit_gap
    source subsequence hE i hlaw hgap hax hxb
  have hhalf : mass / 2 < mass := by dsimp only [mass]; linarith
  filter_upwards [hmasslim.eventually (lt_mem_nhds hhalf)] with k hk
  intro cell
  have hpositive : 0 < (cellLaw (source (subsequence k)) i).prob
      (decodeCell (source (subsequence k)) x) := by
    change 0 < mass at hmass
    linarith
  have hpositiveEvent : 0 < (cellLaw (source (subsequence k)) i).probOf
      {decodeCell (source (subsequence k)) x} := by
    simpa only [FinDist.probOf_singleton] using hpositive
  have hfirst := prob_conditionalCellLaw_le (source (subsequence k))
    (cellLaw (source (subsequence k)) i) _ hpositiveEvent cell
  rw [FinDist.probOf_singleton] at hfirst
  change 0 < mass at hmass
  have hdiv := div_le_div_of_nonneg_left
    ((cellLaw (source (subsequence k)) i).prob_nonneg cell)
    (by linarith : 0 < mass / 2) hk.le
  have hrearrange : (cellLaw (source (subsequence k)) i).prob cell / (mass / 2) =
      (2 / mass) * (cellLaw (source (subsequence k)) i).prob cell := by
    field_simp [hmass.ne']
  have hown := mul_le_mul_of_nonneg_left (ownWeight_le (source (subsequence k)) i cell)
    (div_nonneg (by norm_num : (0 : ℝ) ≤ 2) hmass.le)
  have hcombined := hfirst.trans hdiv
  rw [hrearrange, cellLaw_prob] at hcombined
  exact hcombined.trans (by simpa only [mul_assoc] using hown)

/-- Literal ordinary conditioning converges on the same old source to its actual raw-gap
conditional law. This proof does not evaluate the small signed family at parameter one. -/
theorem tendsto_referenceLaw_conditionalSelectedCellLaw
    (source : ℕ → ι → FinDist (Option ℕ)) (subsequence : ℕ → ℕ)
    {limit : MathUE.MarkedCalendar.Calendar}
    (hE : Tendsto (fun k => (calendar (source (subsequence k))).endpoints) atTop
      (𝓝 limit.endpoints)) (i : ι) {law : ProbabilityMeasure unitInterval}
    (hlaw : Tendsto (fun k => chartLaw (source (subsequence k)) i) atTop (𝓝 law))
    {a b : ℝ} (hgap : Math.Topology.IsGap limit.endpoints a b)
    {x : unitInterval} (hax : a < (x : ℝ)) (hxb : (x : ℝ) < b)
    (hmass : 0 < (law : Measure unitInterval).real {y | a < (y : ℝ) ∧ (y : ℝ) < b}) :
    Tendsto (fun k => referenceLaw (source (subsequence k))
      (conditionalSelectedCellLaw (source (subsequence k)) i x)) atTop
      (𝓝 (gapConditionalLaw law a b hmass)) := by
  have hmasslim := tendsto_decodeCell_ownMass_of_limit_gap
    source subsequence hE i hlaw hgap hax hxb
  have hpositive : ∀ᶠ k in atTop,
      0 < (cellLaw (source (subsequence k)) i).prob (decodeCell (source (subsequence k)) x) :=
    hmasslim.eventually (lt_mem_nhds hmass)
  apply ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mpr
  intro test
  have hmasked := tendsto_integral_selectedCell_chartLaw source subsequence hE i hlaw
    hgap hax hxb test (test.integrable volume)
  have h := hmasked.div hmasslim hmass.ne'
  have hevent : MeasurableSet {y : unitInterval | a < (y : ℝ) ∧ (y : ℝ) < b} :=
    measurableSet_Ioo.preimage measurable_subtype_coe
  rw [integral_indicator hevent, ← integral_gapConditionalLaw law a b hmass test] at h
  apply h.congr'
  filter_upwards [hpositive] with k hk
  exact (integral_referenceLaw_conditionalSelectedCellLaw
    (source (subsequence k)) i x hk test).symm

end GameTheory.MarkedCalendarChart
