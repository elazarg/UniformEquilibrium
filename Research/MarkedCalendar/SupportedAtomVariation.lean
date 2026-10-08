import Research.MarkedCalendar.FiniteLawGeometry
import MathUE.Probability.FiniteSignedConditioning

/-! # Supported-atom variations on the unchanged reference cells

An interior point of a retained gap selects an actual reference cell at every
source index. Its endpoints converge on the supplied subsequence. Signed
singleton conditioning uses the literal original cell law whenever the selected
own atom or the signed radius is unavailable; this makes the source family
well-defined even at exceptional indices.

The selector geometry determines convergence of its own mass to the actual
limiting gap mass, a common signed radius, and finite-law bounds. Interval masks
converge in base L1 for every fixed integrable real test. The actual reference
laws then converge, on the same source subsequence, to the explicitly constructed
measurable signed conditional law. No limiting replacement law is supplied.

Positive finite atoms of the actual collapsed marginal determine a retained gap,
its exact raw mass, and one selector before every legal signed parameter. Positive
Never mass similarly supplies the actual nonempty terminal gap and one selector.
Mapped reset identities, chronological facades, and semantic carrier consumers
remain separate subsequent steps. Parameter one is not identified with the signed
constructor's fallback.
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

/-- Only the two raw endpoints are exceptional. Positive-mass collapsed ties are not removed. -/
theorem ae_eventually_mem_selectedCell_interval_iff
    (source : ℕ → ι → FinDist (Option ℕ)) (subsequence : ℕ → ℕ)
    {limit : MathUE.MarkedCalendar.Calendar}
    (hE : Tendsto (fun k => (calendar (source (subsequence k))).endpoints) atTop
      (𝓝 limit.endpoints)) {a b : ℝ} (hgap : Math.Topology.IsGap limit.endpoints a b)
    {x : unitInterval} (hax : a < (x : ℝ)) (hxb : (x : ℝ) < b) :
    ∀ᵐ y : unitInterval ∂volume, ∀ᶠ k in atTop,
      y ∈ interval (source (subsequence k)) (decodeCell (source (subsequence k)) x) ↔
        a < (y : ℝ) ∧ (y : ℝ) < b := by
  obtain ⟨hleft, hright⟩ :=
    tendsto_decodeCell_endpoints_of_limit_gap source subsequence hE hgap hax hxb
  let first : unitInterval := ⟨a, limit.endpoints_subset hgap.1⟩
  let last : unitInterval := ⟨b, limit.endpoints_subset hgap.2.1⟩
  filter_upwards [volume.ae_ne first, volume.ae_ne last] with y hyfirst hylast
  have hya : (y : ℝ) ≠ a := fun h => hyfirst (Subtype.ext h)
  have hyb : (y : ℝ) ≠ b := fun h => hylast (Subtype.ext h)
  have hleftMem : ∀ᶠ k in atTop,
      left (source (subsequence k)) (decodeCell (source (subsequence k)) x) ≤ (y : ℝ) ↔
        a < (y : ℝ) := by
    rcases lt_or_gt_of_ne hya with hya | hay
    · filter_upwards [tendsto_const_nhds.eventually_lt hleft hya] with k hk
      exact iff_of_false (not_le_of_gt hk) (not_lt_of_gt hya)
    · filter_upwards [hleft.eventually_lt tendsto_const_nhds hay] with k hk
      exact iff_of_true hk.le hay
  have hrightMem : ∀ᶠ k in atTop,
      (y : ℝ) < right (source (subsequence k)) (decodeCell (source (subsequence k)) x) ↔
        (y : ℝ) < b := by
    rcases lt_or_gt_of_ne hyb with hyb | hby
    · filter_upwards [tendsto_const_nhds.eventually_lt hright hyb] with k hk
      exact iff_of_true hk hyb
    · filter_upwards [hright.eventually_lt tendsto_const_nhds hby] with k hk
      exact iff_of_false (not_lt_of_gt hk) (not_lt_of_gt hby)
  filter_upwards [hleftMem, hrightMem] with k hkleft hkright
  change (_ ≤ (y : ℝ) ∧ (y : ℝ) < _) ↔ _
  exact and_congr hkleft hkright

/-- Actual interval masks converge in base L1 for every fixed base-integrable real test. -/
theorem tendsto_integral_norm_selectedCell_indicator_sub
    (source : ℕ → ι → FinDist (Option ℕ)) (subsequence : ℕ → ℕ)
    {limit : MathUE.MarkedCalendar.Calendar}
    (hE : Tendsto (fun k => (calendar (source (subsequence k))).endpoints) atTop
      (𝓝 limit.endpoints)) {a b : ℝ} (hgap : Math.Topology.IsGap limit.endpoints a b)
    {x : unitInterval} (hax : a < (x : ℝ)) (hxb : (x : ℝ) < b)
    (test : unitInterval → ℝ) (htest : Integrable test (volume : Measure unitInterval)) :
    Tendsto (fun k => ∫ y, ‖(interval (source (subsequence k))
      (decodeCell (source (subsequence k)) x)).indicator test y -
        ({z : unitInterval | a < (z : ℝ) ∧ (z : ℝ) < b}).indicator test y‖ ∂volume)
      atTop (𝓝 0) := by
  let gap : Set unitInterval := {y | a < (y : ℝ) ∧ (y : ℝ) < b}
  have hgapMeasurable : MeasurableSet gap := measurableSet_Ioo.preimage measurable_subtype_coe
  have h := tendsto_integral_of_dominated_convergence
    (μ := (volume : Measure unitInterval))
    (F := fun k y => ‖(interval (source (subsequence k))
      (decodeCell (source (subsequence k)) x)).indicator test y - gap.indicator test y‖)
    (f := fun _ => (0 : ℝ)) (fun y => 2 * ‖test y‖)
    (fun k => (((htest.indicator (measurableSet_interval _ _)).sub
      (htest.indicator hgapMeasurable)).norm).aestronglyMeasurable)
    (htest.norm.const_mul 2) (fun k => Eventually.of_forall fun y => by
      rw [norm_norm]
      calc
        _ ≤ ‖(interval (source (subsequence k))
            (decodeCell (source (subsequence k)) x)).indicator test y‖ +
              ‖gap.indicator test y‖ := norm_sub_le _ _
        _ ≤ ‖test y‖ + ‖test y‖ :=
          add_le_add (norm_indicator_le_norm_self _ _) (norm_indicator_le_norm_self _ _)
        _ = _ := by ring) (by
      filter_upwards [ae_eventually_mem_selectedCell_interval_iff source subsequence hE
        hgap hax hxb] with y hy
      apply tendsto_const_nhds.congr'
      filter_upwards [hy] with k hk
      have heq : (interval (source (subsequence k))
          (decodeCell (source (subsequence k)) x)).indicator test y = gap.indicator test y := by
        classical
        by_cases hmem : y ∈ gap
        · rw [Set.indicator_of_mem (hk.mpr hmem), Set.indicator_of_mem hmem]
        · rw [Set.indicator_of_notMem (fun h => hmem (hk.mp h)), Set.indicator_of_notMem hmem]
      simp only [heq, sub_self, norm_zero])
  simpa only [integral_zero] using h

/-- Moving old-cell masks have their actual limiting integral under the original marginal laws. -/
theorem tendsto_integral_selectedCell_chartLaw
    (source : ℕ → ι → FinDist (Option ℕ)) (subsequence : ℕ → ℕ)
    {limit : MathUE.MarkedCalendar.Calendar}
    (hE : Tendsto (fun k => (calendar (source (subsequence k))).endpoints) atTop
      (𝓝 limit.endpoints)) (i : ι) {law : ProbabilityMeasure unitInterval}
    (hlaw : Tendsto (fun k => chartLaw (source (subsequence k)) i) atTop (𝓝 law))
    {a b : ℝ} (hgap : Math.Topology.IsGap limit.endpoints a b)
    {x : unitInterval} (hax : a < (x : ℝ)) (hxb : (x : ℝ) < b)
    (test : unitInterval → ℝ) (htest : Integrable test (volume : Measure unitInterval)) :
    Tendsto (fun k => ∫ y, (interval (source (subsequence k))
      (decodeCell (source (subsequence k)) x)).indicator test y
        ∂(chartLaw (source (subsequence k)) i : Measure unitInterval)) atTop
      (𝓝 (∫ y, ({z : unitInterval | a < (z : ℝ) ∧ (z : ℝ) < b}).indicator test y
        ∂(law : Measure unitInterval))) := by
  exact ProbabilityMeasure.tendsto_integral_moving_test_of_tendsto_of_le_smul base
    (Fintype.card ι : NNReal) hlaw
    (Eventually.of_forall fun k => chartLaw_le (source (subsequence k)) i)
    _ (htest.indicator (measurableSet_Ioo.preimage measurable_subtype_coe)) _
    (Eventually.of_forall fun k => htest.indicator (measurableSet_interval _ _))
    (tendsto_integral_norm_selectedCell_indicator_sub source subsequence hE hgap hax hxb test htest)

private theorem integral_referenceLaw_signedSelectedCellLaw
    (laws : ι → FinDist (Option ℕ)) (i : ι) (x : unitInterval) (parameter : ℝ)
    (hpositive : 0 < (cellLaw laws i).prob (decodeCell laws x))
    (hparameter : |parameter| ≤ (cellLaw laws i).signedCondRadius {decodeCell laws x})
    (test : unitInterval → ℝ)
    (htest : Integrable test (chartLaw laws i : Measure unitInterval)) :
    ∫ y, test y ∂(referenceLaw laws (signedSelectedCellLaw laws i x parameter) :
      Measure unitInterval) =
        (1 - parameter) * (∫ y, test y ∂(chartLaw laws i : Measure unitInterval)) +
          (parameter / (cellLaw laws i).prob (decodeCell laws x)) *
            ∫ y, (interval laws (decodeCell laws x)).indicator test y
              ∂(chartLaw laws i : Measure unitInterval) := by
  classical
  have hevent : MeasurableSet (decodeCell laws ⁻¹' {decodeCell laws x}) :=
    (measurableSet_singleton _).preimage (measurable_decodeCell laws)
  have hintegral : ∫ y in decodeCell laws ⁻¹' {decodeCell laws x}, test y
      ∂(referenceLaw laws (cellLaw laws i) : Measure unitInterval) =
        ∫ y, (interval laws (decodeCell laws x)).indicator test y
          ∂(chartLaw laws i : Measure unitInterval) := by
    rw [← integral_indicator hevent]
    apply integral_congr_ae
    filter_upwards [ae_decodeCell_mem_interval_referenceMeasure laws (cellLaw laws i)] with y hy
    have heq : y ∈ decodeCell laws ⁻¹' {decodeCell laws x} ↔
        y ∈ interval laws (decodeCell laws x) := by
      change decodeCell laws y = decodeCell laws x ↔ _
      constructor
      · intro h
        simpa only [h] using hy
      · exact fun h => decodeCell_of_mem_interval laws h
    by_cases hmem : y ∈ interval laws (decodeCell laws x)
    · rw [Set.indicator_of_mem (heq.mpr hmem), Set.indicator_of_mem hmem]
    · rw [Set.indicator_of_notMem (fun h => hmem (heq.mp h)), Set.indicator_of_notMem hmem]
  unfold signedSelectedCellLaw
  dsimp only
  rw [dite_eq_left ⟨hpositive, hparameter⟩, referenceLaw_signedCond]
  have hmass : 0 < (referenceLaw laws (cellLaw laws i) : Measure unitInterval).real
      (decodeCell laws ⁻¹' {decodeCell laws x}) := by
    rw [referenceLaw_decodeCell_event_real, FinDist.probOf_singleton]
    exact hpositive
  have hradius : |parameter| ≤ (referenceLaw laws (cellLaw laws i)).signedCondRadius
      (decodeCell laws ⁻¹' {decodeCell laws x}) := by
    rw [referenceLaw_signedCondRadius]
    exact hparameter
  have h := ProbabilityMeasure.integral_signedCond (referenceLaw laws (cellLaw laws i))
    (decodeCell laws ⁻¹' {decodeCell laws x}) hevent hmass parameter hradius test htest
  simpa only [referenceLaw_decodeCell_event_real, FinDist.probOf_singleton, hintegral,
    chartLaw] using h

/-- The all-index finite variations converge to their internally constructed signed probability
law on the SAME source subsequence. No limiting replacement law or test convergence is supplied. -/
theorem tendsto_referenceLaw_signedSelectedCellLaw
    (source : ℕ → ι → FinDist (Option ℕ)) (subsequence : ℕ → ℕ)
    {limit : MathUE.MarkedCalendar.Calendar}
    (hE : Tendsto (fun k => (calendar (source (subsequence k))).endpoints) atTop
      (𝓝 limit.endpoints)) (i : ι) {law : ProbabilityMeasure unitInterval}
    (hlaw : Tendsto (fun k => chartLaw (source (subsequence k)) i) atTop (𝓝 law))
    {a b : ℝ} (hgap : Math.Topology.IsGap limit.endpoints a b)
    {x : unitInterval} (hax : a < (x : ℝ)) (hxb : (x : ℝ) < b)
    (hmass : 0 < (law : Measure unitInterval).real {y | a < (y : ℝ) ∧ (y : ℝ) < b})
    (parameter : ℝ) (hparameter : |parameter| ≤ min (1 / 2 : ℝ)
      ((law : Measure unitInterval).real {y | a < (y : ℝ) ∧ (y : ℝ) < b} / 4)) :
    Tendsto (fun k => referenceLaw (source (subsequence k))
      (signedSelectedCellLaw (source (subsequence k)) i x parameter)) atTop
      (𝓝 (law.signedCond {y | a < (y : ℝ) ∧ (y : ℝ) < b}
        (by
          change MeasurableSet ((Subtype.val : unitInterval → ℝ) ⁻¹' Ioo a b)
          exact measurableSet_Ioo.preimage measurable_subtype_coe) hmass parameter (by
          change |parameter| ≤ min (1 / 2 : ℝ)
            ((law : Measure unitInterval).real {y | a < (y : ℝ) ∧ (y : ℝ) < b} / 2)
          refine le_min (hparameter.trans (min_le_left _ _)) ?_
          have hsmall := hparameter.trans (min_le_right _ _)
          linarith))) := by
  let gap : Set unitInterval := {y | a < (y : ℝ) ∧ (y : ℝ) < b}
  have hgapMeasurable : MeasurableSet gap := by
    change MeasurableSet ((Subtype.val : unitInterval → ℝ) ⁻¹' Ioo a b)
    exact measurableSet_Ioo.preimage measurable_subtype_coe
  have hmasslim := tendsto_decodeCell_ownMass_of_limit_gap
    source subsequence hE i hlaw hgap hax hxb
  have hmassgap : 0 < (law : Measure unitInterval).real gap := hmass
  have hradius : |parameter| ≤ law.signedCondRadius gap := by
    apply le_min (hparameter.trans (min_le_left _ _))
    have hsmall := hparameter.trans (min_le_right _ _)
    change |parameter| ≤ (law : Measure unitInterval).real gap / 4 at hsmall
    linarith
  let signed := law.signedCond gap hgapMeasurable hmassgap parameter hradius
  change Tendsto _ atTop (𝓝 signed)
  have hvalid : ∀ᶠ k in atTop,
      0 < (cellLaw (source (subsequence k)) i).prob (decodeCell (source (subsequence k)) x) ∧
        |parameter| ≤ (cellLaw (source (subsequence k)) i).signedCondRadius
          {decodeCell (source (subsequence k)) x} := by
    have hhalf : (law : Measure unitInterval).real gap / 2 <
        (law : Measure unitInterval).real gap := by linarith
    filter_upwards [hmasslim.eventually (lt_mem_nhds hhalf)] with k hk
    refine ⟨by linarith, ?_⟩
    rw [FinDist.signedCondRadius, FinDist.probOf_singleton]
    refine le_min (hparameter.trans (min_le_left _ _)) ?_
    have hsmall := hparameter.trans (min_le_right _ _)
    change |parameter| ≤ (law : Measure unitInterval).real gap / 4 at hsmall
    linarith
  apply ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mpr
  intro test
  have hplain := (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hlaw) test
  have hmasked := tendsto_integral_selectedCell_chartLaw source subsequence hE i hlaw
    hgap hax hxb test (test.integrable volume)
  have h := (hplain.const_mul (1 - parameter)).add
    (((tendsto_const_nhds : Tendsto (fun _ : ℕ => parameter) atTop (𝓝 parameter)).div
      hmasslim hmass.ne').mul hmasked)
  have hintegral := ProbabilityMeasure.integral_signedCond law gap hgapMeasurable hmassgap
    parameter hradius test (test.integrable (law : Measure unitInterval))
  rw [← integral_indicator hgapMeasurable] at hintegral
  change Tendsto _ atTop (𝓝 (∫ y, test y ∂(signed : Measure unitInterval)))
  change (∫ y, test y ∂(signed : Measure unitInterval)) = _ at hintegral
  rw [hintegral]
  apply h.congr'
  filter_upwards [hvalid] with k hk
  exact (integral_referenceLaw_signedSelectedCellLaw (source (subsequence k)) i x parameter
    hk.1 hk.2 test (test.integrable _)).symm

/-- A positive own finite atom produces its actual retained gap and exact raw mass.
The mixture atom is derived from marginal domination, not supplied separately. -/
theorem exists_limit_gap_of_positive_finite_own_atom
    (source : ℕ → ι → FinDist (Option ℕ)) (subsequence : ℕ → ℕ)
    (limit : MathUE.MarkedCalendar.Calendar) (i : ι)
    {law : ProbabilityMeasure unitInterval}
    (hlaw : Tendsto (fun k => chartLaw (source (subsequence k)) i) atTop (𝓝 law))
    {t : ℝ}
    (hatom : 0 < ((law : Measure unitInterval).map limit.collapseClock).real {↑t}) :
    ∃ a b : ℝ, Math.Topology.IsGap limit.endpoints a b ∧
      b ≤ (limit.cutoff : ℝ) ∧ t = (a + b) / 2 ∧ t < (limit.cutoff : ℝ) ∧
      limit.collapseClock ⁻¹' {(t : WithTop ℝ)} =
        {x : unitInterval | a < (x : ℝ) ∧ (x : ℝ) < b} ∧
      (law : Measure unitInterval).real {x | a < (x : ℝ) ∧ (x : ℝ) < b} =
        ((law : Measure unitInterval).map limit.collapseClock).real {↑t} := by
  have hmixture : (volume : Measure unitInterval).map limit.collapseClock {↑t} ≠ 0 := by
    intro hzero
    have hown := map_limit_chartLaw_atom_eq_zero_of_map_volume_eq_zero
      source subsequence limit i hlaw hzero
    have hfalse : (0 : ℝ) < 0 := by
      simpa only [measureReal_def, hown, ENNReal.toReal_zero] using hatom
    exact (lt_irrefl 0) hfalse
  obtain ⟨a, b, hgap, hb, ht⟩ := exists_gap_of_map_volume_collapseClock_atom limit hmixture
  have hfiber : limit.collapseClock ⁻¹' {(t : WithTop ℝ)} =
      {x : unitInterval | a < (x : ℝ) ∧ (x : ℝ) < b} := by
    rw [ht]
    exact collapseClock_fiber_midpoint limit hgap hb
  refine ⟨a, b, hgap, hb, ht, ?_, hfiber, ?_⟩
  · have hab := hgap.2.2.1
    linarith
  · simp only [measureReal_def, Measure.map_apply limit.measurable_collapseClock
      (measurableSet_singleton _), hfiber]

/-- One actual finite own atom selects its gap and old-cell selector before every legal signed
parameter. The limiting probability law is constructed from that same marginal and raw event. -/
theorem exists_signedSelectedCellLaw_limit_of_positive_finite_atom
    (source : ℕ → ι → FinDist (Option ℕ)) (subsequence : ℕ → ℕ)
    {limit : MathUE.MarkedCalendar.Calendar}
    (hE : Tendsto (fun k => (calendar (source (subsequence k))).endpoints) atTop
      (𝓝 limit.endpoints)) (i : ι) {law : ProbabilityMeasure unitInterval}
    (hlaw : Tendsto (fun k => chartLaw (source (subsequence k)) i) atTop (𝓝 law))
    {t : ℝ}
    (hatom : 0 < ((law : Measure unitInterval).map limit.collapseClock).real {↑t}) :
    ∃ (a b : ℝ) (x : unitInterval)
      (hmass : 0 < (law : Measure unitInterval).real
        {y | a < (y : ℝ) ∧ (y : ℝ) < b}),
      Math.Topology.IsGap limit.endpoints a b ∧ b ≤ (limit.cutoff : ℝ) ∧
      t = (a + b) / 2 ∧ (x : ℝ) = t ∧ t < (limit.cutoff : ℝ) ∧
      limit.collapseClock ⁻¹' {(t : WithTop ℝ)} =
        {y : unitInterval | a < (y : ℝ) ∧ (y : ℝ) < b} ∧
      (law : Measure unitInterval).real {y | a < (y : ℝ) ∧ (y : ℝ) < b} =
        ((law : Measure unitInterval).map limit.collapseClock).real {↑t} ∧
      ∀ (parameter : ℝ) (hparameter : |parameter| ≤ min (1 / 2 : ℝ)
        ((law : Measure unitInterval).real {y | a < (y : ℝ) ∧ (y : ℝ) < b} / 4)),
        Tendsto (fun k => referenceLaw (source (subsequence k))
          (signedSelectedCellLaw (source (subsequence k)) i x parameter)) atTop
          (𝓝 (law.signedCond {y | a < (y : ℝ) ∧ (y : ℝ) < b}
            (by
              change MeasurableSet ((Subtype.val : unitInterval → ℝ) ⁻¹' Ioo a b)
              exact measurableSet_Ioo.preimage measurable_subtype_coe)
            hmass parameter (by
              change |parameter| ≤ min (1 / 2 : ℝ)
                ((law : Measure unitInterval).real
                  {y | a < (y : ℝ) ∧ (y : ℝ) < b} / 2)
              refine le_min (hparameter.trans (min_le_left _ _)) ?_
              have hsmall := hparameter.trans (min_le_right _ _)
              linarith))) := by
  obtain ⟨a, b, hgap, hb, ht, htc, hfiber, hmassEq⟩ :=
    exists_limit_gap_of_positive_finite_own_atom source subsequence limit i hlaw hatom
  have hat : a < t := by linarith [hgap.2.2.1]
  have htb : t < b := by linarith [hgap.2.2.1]
  have htIcc : t ∈ Icc (0 : ℝ) 1 :=
    ⟨(limit.endpoints_subset hgap.1).1.trans hat.le,
      htb.le.trans (limit.endpoints_subset hgap.2.1).2⟩
  let x : unitInterval := ⟨t, htIcc⟩
  have hmass : 0 < (law : Measure unitInterval).real
      {y | a < (y : ℝ) ∧ (y : ℝ) < b} := by
    rw [hmassEq]
    exact hatom
  refine ⟨a, b, x, hmass, hgap, hb, ht, rfl, htc, hfiber, hmassEq, ?_⟩
  intro parameter hparameter
  exact tendsto_referenceLaw_signedSelectedCellLaw source subsequence hE i hlaw
    hgap (show a < (x : ℝ) from hat) (show (x : ℝ) < b from htb)
    hmass parameter hparameter

/-- Positive own Never mass forces the actual terminal gap to be nonempty. Its open raw
interval has exactly that mass; the two raw endpoints are null by derived domination. -/
theorem limit_never_gap_of_positive_own_atom
    (source : ℕ → ι → FinDist (Option ℕ)) (subsequence : ℕ → ℕ)
    {limit : MathUE.MarkedCalendar.Calendar}
    (hE : Tendsto (fun k => (calendar (source (subsequence k))).endpoints) atTop
      (𝓝 limit.endpoints))
    (hc : Tendsto (fun k => cutoff (source (subsequence k))) atTop (𝓝 limit.cutoff))
    (i : ι) {law : ProbabilityMeasure unitInterval}
    (hlaw : Tendsto (fun k => chartLaw (source (subsequence k)) i) atTop (𝓝 law))
    (hatom : 0 < ((law : Measure unitInterval).map limit.collapseClock).real {⊤}) :
    (limit.cutoff : ℝ) < 1 ∧
      Math.Topology.IsGap limit.endpoints (limit.cutoff : ℝ) 1 ∧
      limit.collapseClock ⁻¹' {⊤} = Ici limit.cutoff ∧
      (law : Measure unitInterval).real
        {x | (limit.cutoff : ℝ) < (x : ℝ) ∧ (x : ℝ) < 1} =
        ((law : Measure unitInterval).map limit.collapseClock).real {⊤} := by
  have hcut : (limit.cutoff : ℝ) < 1 := by
    apply lt_of_le_of_ne limit.cutoff.property.2
    intro heq
    have hcutoff : limit.cutoff = 1 := Subtype.ext heq
    have hzero := map_limit_chartLaw_top_eq_zero_of_cutoff_eq_one
      source subsequence limit hcutoff i hlaw
    have hfalse : (0 : ℝ) < 0 := by
      simpa only [measureReal_def, hzero, ENNReal.toReal_zero] using hatom
    exact (lt_irrefl 0) hfalse
  have hgap : Math.Topology.IsGap limit.endpoints (limit.cutoff : ℝ) 1 := by
    refine ⟨limit.cutoff_mem, limit.one_mem, hcut, ?_⟩
    intro x hx
    have hnot := limit_endpoints_notMem_Ioo_cutoff_one source subsequence hE hc hx
    by_cases hxc : x ≤ (limit.cutoff : ℝ)
    · exact Or.inl hxc
    · exact Or.inr (le_of_not_gt fun hxone => hnot ⟨lt_of_not_ge hxc, hxone⟩)
  have hfiber : limit.collapseClock ⁻¹' {⊤} = Ici limit.cutoff := by
    ext x
    exact limit.collapseClock_eq_top_iff x
  have hbound : (law : Measure unitInterval) ≤
      (Fintype.card ι : NNReal) • (base : Measure unitInterval) :=
    ProbabilityMeasure.le_of_tendsto_of_le_measure _ hlaw
      (Eventually.of_forall fun k => chartLaw_le (source (subsequence k)) i)
  have habs : (law : Measure unitInterval) ≪ volume :=
    Measure.absolutelyContinuous_of_le_smul hbound
  have hae : {x : unitInterval | (limit.cutoff : ℝ) < (x : ℝ) ∧ (x : ℝ) < 1}
      =ᵐ[(law : Measure unitInterval)] Ici limit.cutoff := by
    filter_upwards [habs.ae_le (volume.ae_ne limit.cutoff), habs.ae_le (volume.ae_ne 1)]
      with x hxc hxone
    have hxcReal : (x : ℝ) ≠ (limit.cutoff : ℝ) := fun h => hxc (Subtype.ext h)
    have hxoneReal : (x : ℝ) ≠ 1 := fun h => hxone (Subtype.ext h)
    apply propext
    change ((limit.cutoff : ℝ) < (x : ℝ) ∧ (x : ℝ) < 1) ↔
      (limit.cutoff : ℝ) ≤ (x : ℝ)
    exact ⟨fun h => h.1.le, fun h =>
      ⟨lt_of_le_of_ne h hxcReal.symm, lt_of_le_of_ne x.property.2 hxoneReal⟩⟩
  refine ⟨hcut, hgap, hfiber, ?_⟩
  rw [measureReal_def, measureReal_def, Measure.map_apply limit.measurable_collapseClock
    (measurableSet_singleton _), hfiber, measure_congr hae]

/-- The actual positive Never atom chooses one terminal-gap selector before every legal signed
parameter, and the literal replacement laws converge along the same source subsequence. -/
theorem exists_signedSelectedCellLaw_limit_of_positive_never_atom
    (source : ℕ → ι → FinDist (Option ℕ)) (subsequence : ℕ → ℕ)
    {limit : MathUE.MarkedCalendar.Calendar}
    (hE : Tendsto (fun k => (calendar (source (subsequence k))).endpoints) atTop
      (𝓝 limit.endpoints))
    (hc : Tendsto (fun k => cutoff (source (subsequence k))) atTop (𝓝 limit.cutoff))
    (i : ι) {law : ProbabilityMeasure unitInterval}
    (hlaw : Tendsto (fun k => chartLaw (source (subsequence k)) i) atTop (𝓝 law))
    (hatom : 0 < ((law : Measure unitInterval).map limit.collapseClock).real {⊤}) :
    ∃ (x : unitInterval)
      (hmass : 0 < (law : Measure unitInterval).real
        {y | (limit.cutoff : ℝ) < (y : ℝ) ∧ (y : ℝ) < 1}),
      (limit.cutoff : ℝ) < 1 ∧
      Math.Topology.IsGap limit.endpoints (limit.cutoff : ℝ) 1 ∧
      (x : ℝ) = ((limit.cutoff : ℝ) + 1) / 2 ∧
      (law : Measure unitInterval).real
        {y | (limit.cutoff : ℝ) < (y : ℝ) ∧ (y : ℝ) < 1} =
        ((law : Measure unitInterval).map limit.collapseClock).real {⊤} ∧
      ∀ (parameter : ℝ) (hparameter : |parameter| ≤ min (1 / 2 : ℝ)
        ((law : Measure unitInterval).real
          {y | (limit.cutoff : ℝ) < (y : ℝ) ∧ (y : ℝ) < 1} / 4)),
        Tendsto (fun k => referenceLaw (source (subsequence k))
          (signedSelectedCellLaw (source (subsequence k)) i x parameter)) atTop
          (𝓝 (law.signedCond {y | (limit.cutoff : ℝ) < (y : ℝ) ∧ (y : ℝ) < 1}
            (by
              change MeasurableSet
                ((Subtype.val : unitInterval → ℝ) ⁻¹' Ioo (limit.cutoff : ℝ) 1)
              exact measurableSet_Ioo.preimage measurable_subtype_coe)
            hmass parameter (by
              change |parameter| ≤ min (1 / 2 : ℝ)
                ((law : Measure unitInterval).real
                  {y | (limit.cutoff : ℝ) < (y : ℝ) ∧ (y : ℝ) < 1} / 2)
              refine le_min (hparameter.trans (min_le_left _ _)) ?_
              have hsmall := hparameter.trans (min_le_right _ _)
              linarith))) := by
  obtain ⟨hcut, hgap, _, hmassEq⟩ :=
    limit_never_gap_of_positive_own_atom source subsequence hE hc i hlaw hatom
  have hxIcc : ((limit.cutoff : ℝ) + 1) / 2 ∈ Icc (0 : ℝ) 1 := by
    constructor <;> linarith [limit.cutoff.property.1]
  let x : unitInterval := ⟨((limit.cutoff : ℝ) + 1) / 2, hxIcc⟩
  have hmass : 0 < (law : Measure unitInterval).real
      {y | (limit.cutoff : ℝ) < (y : ℝ) ∧ (y : ℝ) < 1} := by
    rw [hmassEq]
    exact hatom
  refine ⟨x, hmass, hcut, hgap, rfl, hmassEq, ?_⟩
  intro parameter hparameter
  have hleft : (limit.cutoff : ℝ) < (x : ℝ) := by dsimp only [x]; linarith
  have hright : (x : ℝ) < 1 := by dsimp only [x]; linarith
  exact tendsto_referenceLaw_signedSelectedCellLaw source subsequence hE i hlaw
    hgap hleft hright hmass parameter hparameter

end GameTheory.MarkedCalendarChart
