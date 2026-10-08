import Research.MarkedCalendar.FiniteLawGeometry
import MathUE.Probability.FiniteSignedConditioning

/-! # Supported-atom variations on the unchanged reference cells

An interior point of a retained gap selects an actual reference cell at every
source index. Its endpoints converge on the supplied subsequence. Signed
singleton conditioning uses the literal original cell law whenever the selected
own atom or the signed radius is unavailable; this makes the source family
well-defined even at exceptional indices.

This first slice proves the selector geometry, convergence of its own mass to
the actual limiting gap mass, and the common signed radius and finite-law bounds. Actual
limiting likelihood laws, their convergence, and semantic carrier consumers are
separate subsequent steps, not hypotheses hidden in this construction.
-/

noncomputable section

open Set Filter MeasureTheory TopologicalSpace GameTheory.Math.Probability
open scoped Topology

namespace GameTheory.MarkedCalendarChart

variable {ι : Type} [Fintype ι] [Nonempty ι]

/-- The actual cell containing a fixed interior point eventually has the neighboring endpoints.
The decoder remains defined at every earlier index, without a positive own-atom premise. -/
theorem eventually_decodeCell_endpoints_of_limit_gap
    (source : ℕ → ι → FinDist (Option ℕ)) (subsequence : ℕ → ℕ)
    {limit : MathUE.MarkedCalendar.Calendar}
    (hE : Tendsto (fun k => (calendar (source (subsequence k))).endpoints) atTop
      (𝓝 limit.endpoints)) {a b : ℝ} (hgap : Math.Topology.IsGap limit.endpoints a b)
    {x : unitInterval} (hax : a < (x : ℝ)) (hxb : (x : ℝ) < b) :
    ∀ᶠ k in atTop,
      left (source (subsequence k)) (decodeCell (source (subsequence k)) x) =
        (calendar (source (subsequence k))).lowerEndpoint x ∧
      right (source (subsequence k)) (decodeCell (source (subsequence k)) x) =
        (calendar (source (subsequence k))).upperEndpoint x ∧
      x ∈ interval (source (subsequence k)) (decodeCell (source (subsequence k)) x) := by
  have hxE : (x : ℝ) ∉ limit.endpoints := by
    intro hx
    rcases hgap.2.2.2 _ hx with h | h
    · exact (not_le_of_gt hax) h
    · exact (not_le_of_gt hxb) h
  have hxregular : (x : ℝ) ∉ limit.exceptionalEndpoints := by
    rintro (h | h) <;> exact hxE h.1
  obtain ⟨hlower, hupper⟩ := limit.endpoints_of_gap hgap hax hxb
  have hleft := MathUE.MarkedCalendar.Calendar.tendsto_lowerEndpoint hE hxregular
  have hright := MathUE.MarkedCalendar.Calendar.tendsto_upperEndpoint hE hxregular
  rw [hlower] at hleft
  rw [hupper] at hright
  filter_upwards [hleft.eventually (gt_mem_nhds hax),
    hright.eventually (lt_mem_nhds hxb)] with k hkleft hkright
  have hxk : (x : ℝ) ∉ (calendar (source (subsequence k))).endpoints := by
    intro hx
    rw [(calendar (source (subsequence k))).lowerEndpoint_eq_of_mem hx] at hkleft
    exact (lt_irrefl _) hkleft
  obtain ⟨hsourcegap, _, _⟩ := (calendar (source (subsequence k))).gap_of_not_mem hxk
  obtain ⟨cell, hcellLeft, hcellRight⟩ :=
    exists_cell_of_calendar_gap (source (subsequence k)) hsourcegap
  have hxcell : x ∈ interval (source (subsequence k)) cell := by
    change left (source (subsequence k)) cell ≤ (x : ℝ) ∧
      (x : ℝ) < right (source (subsequence k)) cell
    rw [hcellLeft, hcellRight]
    exact ⟨hkleft.le, hkright⟩
  rw [decodeCell_of_mem_interval (source (subsequence k)) hxcell]
  exact ⟨hcellLeft, hcellRight, hxcell⟩

/-- No further subsequence is selected to follow a retained cell. -/
theorem tendsto_decodeCell_endpoints_of_limit_gap
    (source : ℕ → ι → FinDist (Option ℕ)) (subsequence : ℕ → ℕ)
    {limit : MathUE.MarkedCalendar.Calendar}
    (hE : Tendsto (fun k => (calendar (source (subsequence k))).endpoints) atTop
      (𝓝 limit.endpoints)) {a b : ℝ} (hgap : Math.Topology.IsGap limit.endpoints a b)
    {x : unitInterval} (hax : a < (x : ℝ)) (hxb : (x : ℝ) < b) :
    Tendsto (fun k => left (source (subsequence k))
      (decodeCell (source (subsequence k)) x)) atTop (𝓝 a) ∧
    Tendsto (fun k => right (source (subsequence k))
      (decodeCell (source (subsequence k)) x)) atTop (𝓝 b) := by
  have hxregular : (x : ℝ) ∉ limit.exceptionalEndpoints := by
    rintro (h | h) <;> rcases hgap.2.2.2 _ h.1 with h | h
    all_goals linarith
  obtain ⟨hlower, hupper⟩ := limit.endpoints_of_gap hgap hax hxb
  have hleft := MathUE.MarkedCalendar.Calendar.tendsto_lowerEndpoint hE hxregular
  have hright := MathUE.MarkedCalendar.Calendar.tendsto_upperEndpoint hE hxregular
  rw [hlower] at hleft
  rw [hupper] at hright
  have hevent := eventually_decodeCell_endpoints_of_limit_gap source subsequence hE hgap hax hxb
  exact ⟨hleft.congr' (hevent.mono fun _ hk => hk.1.symm),
    hright.congr' (hevent.mono fun _ hk => hk.2.1.symm)⟩

/-- The selected own mass tends to the actual limiting gap mass, not a supplied coefficient. -/
theorem tendsto_decodeCell_ownMass_of_limit_gap
    (source : ℕ → ι → FinDist (Option ℕ)) (subsequence : ℕ → ℕ)
    {limit : MathUE.MarkedCalendar.Calendar}
    (hE : Tendsto (fun k => (calendar (source (subsequence k))).endpoints) atTop
      (𝓝 limit.endpoints)) (i : ι) {law : ProbabilityMeasure unitInterval}
    (hlaw : Tendsto (fun k => chartLaw (source (subsequence k)) i) atTop (𝓝 law))
    {a b : ℝ} (hgap : Math.Topology.IsGap limit.endpoints a b)
    {x : unitInterval} (hax : a < (x : ℝ)) (hxb : (x : ℝ) < b) :
    Tendsto (fun k => (cellLaw (source (subsequence k)) i).prob
      (decodeCell (source (subsequence k)) x)) atTop
      (𝓝 ((law : Measure unitInterval).real {y | a < (y : ℝ) ∧ (y : ℝ) < b})) := by
  let gap : Set unitInterval := {y | a < (y : ℝ) ∧ (y : ℝ) < b}
  have hgapMeasurable : MeasurableSet gap := measurableSet_Ioo.preimage measurable_subtype_coe
  obtain ⟨value, _, hpointwise⟩ :=
    exists_tendsto_density_on_limit_gap source subsequence hE i hlaw hgap
  obtain ⟨hleft, hright⟩ :=
    tendsto_decodeCell_endpoints_of_limit_gap source subsequence hE hgap hax hxb
  have hwidth := hright.sub hleft
  have hmass := (hpointwise x hax hxb).mul hwidth
  have hmass' : Tendsto (fun k => (cellLaw (source (subsequence k)) i).prob
      (decodeCell (source (subsequence k)) x)) atTop (𝓝 (value * (b - a))) := by
    apply hmass.congr'
    filter_upwards [eventually_decodeCell_endpoints_of_limit_gap source subsequence
      hE hgap hax hxb] with k hk
    rw [density_eq_of_mem_interval _ i hk.2.2, cellLaw_prob, right]
    simp only [add_sub_cancel_left]
    exact div_mul_cancel₀ _ (weight_pos _ _).ne'
  have hconvergence := tendsto_integral_of_dominated_convergence
    (μ := (volume : Measure unitInterval).restrict gap)
    (F := fun k y => density (source (subsequence k)) i y) (f := fun _ => value)
    (fun _ => (Fintype.card ι : ℝ))
    (fun k => (measurable_density (source (subsequence k)) i).aestronglyMeasurable)
    (integrable_const _) (fun k => Eventually.of_forall fun y => by
      simpa only [Real.norm_eq_abs, abs_of_nonneg (density_nonneg _ _ _)] using
        density_le_card (source (subsequence k)) i y) (by
      filter_upwards [ae_restrict_mem hgapMeasurable] with y hy
      exact hpointwise y hy.1 hy.2)
  have hweak := ProbabilityMeasure.tendsto_integral_of_tendsto_of_le_smul base
    (Fintype.card ι : NNReal) hlaw
    (Eventually.of_forall fun k => chartLaw_le (source (subsequence k)) i)
    (gap.indicator (fun _ => (1 : ℝ))) ((integrable_const _).indicator hgapMeasurable)
  have hweak' := hweak.congr' (Eventually.of_forall fun k =>
    integral_indicator_chartLaw (source (subsequence k)) i gap hgapMeasurable)
  have heq := tendsto_nhds_unique hweak' hconvergence
  have hvolume : (volume : Measure unitInterval).real gap = b - a := by
    change ((volume : Measure unitInterval)
      (Ioo ⟨a, limit.endpoints_subset hgap.1⟩
        ⟨b, limit.endpoints_subset hgap.2.1⟩)).toReal = b - a
    rw [unitInterval.volume_Ioo, ENNReal.toReal_ofReal (sub_nonneg.mpr hgap.2.2.1.le)]
  have hidentify : (law : Measure unitInterval).real gap = value * (b - a) := by
    rw [integral_indicator_const _ hgapMeasurable] at heq
    simp only [integral_const, measureReal_def, Measure.restrict_apply_univ,
      smul_eq_mul, mul_one] at heq
    change (law : Measure unitInterval).real gap =
      (volume : Measure unitInterval).real gap * value at heq
    rwa [hvolume, mul_comm] at heq
  change Tendsto _ atTop (𝓝 ((law : Measure unitInterval).real gap))
  rw [hidentify]
  exact hmass'

/-- An all-index law on the old cells. Unavailable signed resets leave the original law intact. -/
def signedSelectedCellLaw (laws : ι → FinDist (Option ℕ)) (i : ι)
    (x : unitInterval) (parameter : ℝ) : FinDist (Cell laws) := by
  classical
  let p := cellLaw laws i
  let cell := decodeCell laws x
  exact if h : 0 < p.prob cell ∧ |parameter| ≤ p.signedCondRadius {cell} then
    p.signedCond {cell} (by simpa only [FinDist.probOf_singleton] using h.1) parameter h.2
  else p

/-- Both signs preserve the original support, including at fallback indices. -/
theorem support_signedSelectedCellLaw (laws : ι → FinDist (Option ℕ)) (i : ι)
    (x : unitInterval) (parameter : ℝ) :
    (signedSelectedCellLaw laws i x parameter).support = (cellLaw laws i).support := by
  classical
  unfold signedSelectedCellLaw
  dsimp only
  split
  · exact FinDist.support_signedCond ..
  · rfl

/-- The closed signed branch and the fallback share the same uniform likelihood bounds. -/
theorem prob_signedSelectedCellLaw_bounds (laws : ι → FinDist (Option ℕ)) (i : ι)
    (x : unitInterval) (parameter : ℝ) (cell : Cell laws) :
    (1 / 2 : ℝ) * (cellLaw laws i).prob cell ≤
        (signedSelectedCellLaw laws i x parameter).prob cell ∧
      (signedSelectedCellLaw laws i x parameter).prob cell ≤
        (3 / 2 : ℝ) * (cellLaw laws i).prob cell := by
  classical
  unfold signedSelectedCellLaw
  dsimp only
  split
  · exact FinDist.prob_signedCond_bounds ..
  · have hnonneg := (cellLaw laws i).prob_nonneg cell
    constructor <;> linarith

/-- The common old-reference envelope is derived, not supplied with the variation. -/
theorem prob_signedSelectedCellLaw_le (laws : ι → FinDist (Option ℕ)) (i : ι)
    (x : unitInterval) (parameter : ℝ) (cell : Cell laws) :
    (signedSelectedCellLaw laws i x parameter).prob cell ≤
      (2 * Fintype.card ι : ℝ) * weight laws cell := by
  have hbound := (prob_signedSelectedCellLaw_bounds laws i x parameter cell).2
  rw [cellLaw_prob] at hbound
  have hown := ownWeight_le laws i cell
  have hnonneg := ownWeight_nonneg laws i cell
  nlinarith

theorem signedSelectedCellLaw_zero (laws : ι → FinDist (Option ℕ)) (i : ι)
    (x : unitInterval) : signedSelectedCellLaw laws i x 0 = cellLaw laws i := by
  classical
  unfold signedSelectedCellLaw
  dsimp only
  split
  · exact FinDist.signedCond_zero ..
  · rfl

/-- Positive gap mass supplies one closed signed radius, eventually valid for all parameters.
Exceptional indices need no positivity and use the literal fallback. -/
theorem eventually_signedSelectedCellLaw_affine_of_limit_gap
    (source : ℕ → ι → FinDist (Option ℕ)) (subsequence : ℕ → ℕ)
    {limit : MathUE.MarkedCalendar.Calendar}
    (hE : Tendsto (fun k => (calendar (source (subsequence k))).endpoints) atTop
      (𝓝 limit.endpoints)) (i : ι) {law : ProbabilityMeasure unitInterval}
    (hlaw : Tendsto (fun k => chartLaw (source (subsequence k)) i) atTop (𝓝 law))
    {a b : ℝ} (hgap : Math.Topology.IsGap limit.endpoints a b)
    {x : unitInterval} (hax : a < (x : ℝ)) (hxb : (x : ℝ) < b)
    (hmass : 0 < (law : Measure unitInterval).real {y | a < (y : ℝ) ∧ (y : ℝ) < b}) :
    let radius := min (1 / 2 : ℝ)
      ((law : Measure unitInterval).real {y | a < (y : ℝ) ∧ (y : ℝ) < b} / 4)
    0 < radius ∧ ∀ᶠ k in atTop, ∀ parameter : ℝ, |parameter| ≤ radius →
      ∀ cell : Cell (source (subsequence k)),
        (signedSelectedCellLaw (source (subsequence k)) i x parameter).prob cell =
          (1 - parameter) * (cellLaw (source (subsequence k)) i).prob cell +
            parameter * (FinDist.pure (decodeCell (source (subsequence k)) x)).prob cell := by
  classical
  dsimp only
  let mass := (law : Measure unitInterval).real {y | a < (y : ℝ) ∧ (y : ℝ) < b}
  have hmasspos : 0 < mass := hmass
  refine ⟨lt_min (by norm_num) (by positivity), ?_⟩
  have hlim := tendsto_decodeCell_ownMass_of_limit_gap source subsequence hE i hlaw hgap hax hxb
  have hhalf : mass / 2 < mass := by linarith
  filter_upwards [hlim.eventually (lt_mem_nhds hhalf)] with k hk
  intro parameter hparameter cell
  have hpos : 0 < (cellLaw (source (subsequence k)) i).prob
      (decodeCell (source (subsequence k)) x) := by linarith
  have hradius : |parameter| ≤ (cellLaw (source (subsequence k)) i).signedCondRadius
      {decodeCell (source (subsequence k)) x} := by
    rw [FinDist.signedCondRadius, FinDist.probOf_singleton]
    refine le_min (hparameter.trans (min_le_left _ _)) ?_
    have hsmall := hparameter.trans (min_le_right _ _)
    change |parameter| ≤ mass / 4 at hsmall
    linarith
  unfold signedSelectedCellLaw
  dsimp only
  rw [dite_eq_left ⟨hpos, hradius⟩]
  exact FinDist.prob_signedCond_singleton _ _ hpos parameter hradius cell

end GameTheory.MarkedCalendarChart
