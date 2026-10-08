import Research.MarkedCalendar.SupportedAtomConditioning

/-! # Ordinary chronological conditioning on whole old cells

Actual old endpoints cut whole cells into an early prefix and a late suffix.
Their decoded events agree almost everywhere with the corresponding raw
half-lines. Converging cuts yield actual masked L1 and marginal-mass limits.
Positive limiting event mass then produces ordinary conditional weak limits
and an eventual density envelope on the same source subsequence.

Every limiting endpoint has one all-index source-endpoint selector, chosen
before owners, limiting marginals, and conditioning sides. No mask, normalizer,
or conditional-limit oracle is supplied. Signed-event variations and joint
semantic carrier consumers remain subsequent adapters.
-/

noncomputable section

open Set Filter MeasureTheory TopologicalSpace GameTheory.Math.Probability
open scoped Topology

namespace GameTheory.MarkedCalendarChart

inductive ChronologicalSide where
  | before
  | after

def rawCutEvent : ChronologicalSide → ℝ → Set unitInterval
  | .before, cut => {x | (x : ℝ) < cut}
  | .after, cut => {x | cut ≤ (x : ℝ)}

theorem measurableSet_rawCutEvent (side : ChronologicalSide) (cut : ℝ) :
    MeasurableSet (rawCutEvent side cut) := by
  cases side
  · exact measurableSet_lt measurable_subtype_coe measurable_const
  · exact measurableSet_le measurable_const measurable_subtype_coe

variable {ι : Type} [Fintype ι] [Nonempty ι]

def cellCutEvent (laws : ι → FinDist (Option ℕ)) :
    ChronologicalSide → ℝ → Set (Cell laws)
  | .before, cut => {cell | right laws cell ≤ cut}
  | .after, cut => {cell | cut ≤ left laws cell}

/-- No old cell straddles an actual endpoint. Both sides retain their literal order meaning. -/
theorem mem_cellCutEvent_iff_of_mem_interval (laws : ι → FinDist (Option ℕ))
    (side : ChronologicalSide) (cut : ℝ) (hcut : cut ∈ (calendar laws).endpoints)
    {cell : Cell laws} {x : unitInterval} (hx : x ∈ interval laws cell) :
    cell ∈ cellCutEvent laws side cut ↔ x ∈ rawCutEvent side cut := by
  have hsplit := (isGap_interval laws cell).2.2.2 cut hcut
  change left laws cell ≤ (x : ℝ) ∧ (x : ℝ) < right laws cell at hx
  cases side
  · change right laws cell ≤ cut ↔ (x : ℝ) < cut
    constructor
    · exact fun h => hx.2.trans_le h
    · intro h
      rcases hsplit with hleft | hright
      · exact (not_lt_of_ge (hleft.trans hx.1) h).elim
      · exact hright
  · change cut ≤ left laws cell ↔ cut ≤ (x : ℝ)
    constructor
    · exact fun h => h.trans hx.1
    · intro h
      rcases hsplit with hleft | hright
      · exact hleft
      · exact (not_lt_of_ge h (hx.2.trans_le hright)).elim

/-- A late cut weakly before the finite cutoff includes the literal old Never cell. -/
theorem never_mem_cellCutEvent_after (laws : ι → FinDist (Option ℕ))
    (cell : Cell laws) (htop : (cell : WithTop ℕ) = ⊤)
    (cut : ℝ) (hcut : cut ≤ (cutoff laws : ℝ)) :
    cell ∈ cellCutEvent laws .after cut := by
  change cut ≤ left laws cell
  exact hcut.trans_eq (cutoff_eq_left_of_top laws cell htop)

/-- The decoded whole-cell event has the actual raw half-line as its almost-everywhere image. -/
theorem ae_decodeCell_cellCutEvent (laws : ι → FinDist (Option ℕ))
    (p : FinDist (Cell laws)) (side : ChronologicalSide) (cut : ℝ)
    (hcut : cut ∈ (calendar laws).endpoints) :
    decodeCell laws ⁻¹' cellCutEvent laws side cut
      =ᵐ[referenceMeasure laws p] rawCutEvent side cut := by
  filter_upwards [ae_decodeCell_mem_interval_referenceMeasure laws p] with x hx
  apply propext
  exact mem_cellCutEvent_iff_of_mem_interval laws side cut hcut hx

theorem probOf_cellCutEvent (laws : ι → FinDist (Option ℕ))
    (p : FinDist (Cell laws)) (side : ChronologicalSide) (cut : ℝ)
    (hcut : cut ∈ (calendar laws).endpoints) :
    p.probOf (cellCutEvent laws side cut) =
      (referenceLaw laws p : Measure unitInterval).real (rawCutEvent side cut) := by
  rw [← referenceLaw_decodeCell_event_real]
  exact measureReal_congr (ae_decodeCell_cellCutEvent laws p side cut hcut)

omit [Fintype ι] [Nonempty ι] in
/-- Only the raw seam is exceptional; no positive collapsed-clock tie is discarded. -/
theorem ae_eventually_mem_rawCutEvent_iff (cuts : ℕ → ℝ) {cut : ℝ}
    (hcuts : Tendsto cuts atTop (𝓝 cut)) (side : ChronologicalSide) :
    ∀ᵐ x : unitInterval ∂volume, ∀ᶠ k in atTop,
      x ∈ rawCutEvent side (cuts k) ↔ x ∈ rawCutEvent side cut := by
  have hne : ∀ᵐ x : unitInterval ∂volume, (x : ℝ) ≠ cut := by
    exact ((Set.countable_singleton cut).preimage
      (f := fun x : unitInterval => (x : ℝ)) Subtype.val_injective).ae_notMem volume
  filter_upwards [hne] with x hx
  rcases lt_or_gt_of_ne hx with hlt | hgt
  · filter_upwards [tendsto_const_nhds.eventually_lt hcuts hlt] with k hk
    cases side
    · exact iff_of_true hk hlt
    · exact iff_of_false (not_le_of_gt hk) (not_le_of_gt hlt)
  · filter_upwards [hcuts.eventually_lt tendsto_const_nhds hgt] with k hk
    cases side
    · exact iff_of_false (not_lt_of_gt hk) (not_lt_of_gt hgt)
    · exact iff_of_true hk.le hgt.le

omit [Fintype ι] [Nonempty ι] in
theorem tendsto_integral_norm_rawCutEvent_indicator_sub (cuts : ℕ → ℝ) {cut : ℝ}
    (hcuts : Tendsto cuts atTop (𝓝 cut)) (side : ChronologicalSide)
    (test : unitInterval → ℝ) (htest : Integrable test (volume : Measure unitInterval)) :
    Tendsto (fun k => ∫ x, ‖(rawCutEvent side (cuts k)).indicator test x -
      (rawCutEvent side cut).indicator test x‖ ∂volume) atTop (𝓝 0) :=
  tendsto_integral_norm_indicator_sub_of_ae_eventually_mem_iff volume
    (fun k => rawCutEvent side (cuts k)) (rawCutEvent side cut)
    (fun k => measurableSet_rawCutEvent side (cuts k)) test htest
    (ae_eventually_mem_rawCutEvent_iff cuts hcuts side)

/-- The actual original marginal laws see the limiting masked integral. -/
theorem tendsto_integral_rawCutEvent_chartLaw
    (source : ℕ → ι → FinDist (Option ℕ)) (subsequence : ℕ → ℕ)
    (cuts : ℕ → ℝ) {cut : ℝ} (hcuts : Tendsto cuts atTop (𝓝 cut))
    (side : ChronologicalSide) (i : ι) {law : ProbabilityMeasure unitInterval}
    (hlaw : Tendsto (fun k => chartLaw (source (subsequence k)) i) atTop (𝓝 law))
    (test : unitInterval → ℝ) (htest : Integrable test (volume : Measure unitInterval)) :
    Tendsto (fun k => ∫ x, (rawCutEvent side (cuts k)).indicator test x
      ∂(chartLaw (source (subsequence k)) i : Measure unitInterval)) atTop
      (𝓝 (∫ x, (rawCutEvent side cut).indicator test x ∂(law : Measure unitInterval))) := by
  exact ProbabilityMeasure.tendsto_integral_moving_test_of_tendsto_of_le_smul base
    (Fintype.card ι : NNReal) hlaw
    (Eventually.of_forall fun k => chartLaw_le (source (subsequence k)) i)
    _ (htest.indicator (measurableSet_rawCutEvent side cut)) _
    (Eventually.of_forall fun k => htest.indicator (measurableSet_rawCutEvent side (cuts k)))
    (tendsto_integral_norm_rawCutEvent_indicator_sub cuts hcuts side test htest)

/-- The finite event's normalizer converges to its actual raw half-line mass. -/
theorem tendsto_probOf_cellCutEvent
    (source : ℕ → ι → FinDist (Option ℕ)) (subsequence : ℕ → ℕ)
    (cuts : ℕ → ℝ)
    (hmem : ∀ k, cuts k ∈ (calendar (source (subsequence k))).endpoints)
    {cut : ℝ} (hcuts : Tendsto cuts atTop (𝓝 cut))
    (side : ChronologicalSide) (i : ι) {law : ProbabilityMeasure unitInterval}
    (hlaw : Tendsto (fun k => chartLaw (source (subsequence k)) i) atTop (𝓝 law)) :
    Tendsto (fun k => (cellLaw (source (subsequence k)) i).probOf
      (cellCutEvent (source (subsequence k)) side (cuts k))) atTop
      (𝓝 ((law : Measure unitInterval).real (rawCutEvent side cut))) := by
  have h := tendsto_integral_rawCutEvent_chartLaw source subsequence cuts hcuts side i hlaw
    (fun _ => (1 : ℝ)) (integrable_const 1)
  simp only [integral_indicator_const _ (measurableSet_rawCutEvent side _),
    smul_eq_mul, mul_one] at h
  apply h.congr'
  exact Eventually.of_forall fun k =>
    (probOf_cellCutEvent (source (subsequence k)) (cellLaw (source (subsequence k)) i)
      side (cuts k) (hmem k)).symm

def conditionalCutCellLaw (laws : ι → FinDist (Option ℕ))
    (side : ChronologicalSide) (cut : ℝ) (i : ι) : FinDist (Cell laws) :=
  conditionalCellLaw laws (cellLaw laws i) (cellCutEvent laws side cut)

omit [Fintype ι] [Nonempty ι] in
def cutConditionalLaw (law : ProbabilityMeasure unitInterval)
    (side : ChronologicalSide) (cut : ℝ)
    (hmass : 0 < (law : Measure unitInterval).real (rawCutEvent side cut)) :
    ProbabilityMeasure unitInterval :=
  ⟨ProbabilityTheory.cond (law : Measure unitInterval) (rawCutEvent side cut),
    ProbabilityTheory.cond_isProbabilityMeasure (ENNReal.toReal_pos_iff.mp hmass).1.ne'⟩

private theorem integral_referenceLaw_conditionalCutCellLaw
    (laws : ι → FinDist (Option ℕ)) (side : ChronologicalSide) (cut : ℝ)
    (hcut : cut ∈ (calendar laws).endpoints) (i : ι)
    (hmass : 0 < (cellLaw laws i).probOf (cellCutEvent laws side cut))
    (test : unitInterval → ℝ) :
    ∫ x, test x ∂(referenceLaw laws (conditionalCutCellLaw laws side cut i) :
      Measure unitInterval) =
      (∫ x, (rawCutEvent side cut).indicator test x
        ∂(chartLaw laws i : Measure unitInterval)) /
          (cellLaw laws i).probOf (cellCutEvent laws side cut) := by
  have hevent : MeasurableSet (decodeCell laws ⁻¹' cellCutEvent laws side cut) :=
    (cellCutEvent laws side cut).toFinite.measurableSet.preimage (measurable_decodeCell laws)
  have hsets := ae_decodeCell_cellCutEvent laws (cellLaw laws i) side cut hcut
  have hintegral := integral_congr_ae (indicator_ae_eq_of_ae_eq_set (f := test) hsets)
  rw [integral_indicator hevent] at hintegral
  change (∫ x, test x ∂referenceMeasure laws
    (conditionalCellLaw laws (cellLaw laws i) (cellCutEvent laws side cut))) = _
  rw [conditionalCellLaw, dite_eq_left hmass, referenceMeasure_condOn laws _ _ hmass,
    ProbabilityTheory.cond, integral_smul_measure, ENNReal.toReal_inv, hintegral]
  have hnormalizer := referenceLaw_decodeCell_event_real laws (cellLaw laws i)
    (cellCutEvent laws side cut)
  change (referenceMeasure laws (cellLaw laws i)).real _ = _ at hnormalizer
  change ((referenceMeasure laws (cellLaw laws i)).real
    (decodeCell laws ⁻¹' cellCutEvent laws side cut))⁻¹ * _ = _
  rw [hnormalizer, div_eq_mul_inv, mul_comm]
  rfl

/-- The ordinary endpoint envelope is derived from positive limiting event mass. -/
theorem eventually_conditionalCutCellLaw_le
    (source : ℕ → ι → FinDist (Option ℕ)) (subsequence : ℕ → ℕ)
    (cuts : ℕ → ℝ)
    (hmem : ∀ k, cuts k ∈ (calendar (source (subsequence k))).endpoints)
    {cut : ℝ} (hcuts : Tendsto cuts atTop (𝓝 cut))
    (side : ChronologicalSide) (i : ι) {law : ProbabilityMeasure unitInterval}
    (hlaw : Tendsto (fun k => chartLaw (source (subsequence k)) i) atTop (𝓝 law))
    (hmass : 0 < (law : Measure unitInterval).real (rawCutEvent side cut)) :
    ∀ᶠ k in atTop, ∀ cell : Cell (source (subsequence k)),
      (conditionalCutCellLaw (source (subsequence k)) side (cuts k) i).prob cell ≤
        ((2 / (law : Measure unitInterval).real (rawCutEvent side cut)) * Fintype.card ι) *
          weight (source (subsequence k)) cell := by
  let mass := (law : Measure unitInterval).real (rawCutEvent side cut)
  have hmasslim := tendsto_probOf_cellCutEvent source subsequence cuts hmem hcuts side i hlaw
  have hpositive : 0 < mass := hmass
  filter_upwards [hmasslim.eventually (lt_mem_nhds (by linarith : mass / 2 < mass))] with k hk
  intro cell
  have hevent : 0 < (cellLaw (source (subsequence k)) i).probOf
      (cellCutEvent (source (subsequence k)) side (cuts k)) := by linarith
  calc
    _ ≤ (cellLaw (source (subsequence k)) i).prob cell /
        (cellLaw (source (subsequence k)) i).probOf
          (cellCutEvent (source (subsequence k)) side (cuts k)) :=
      prob_conditionalCellLaw_le _ _ _ hevent cell
    _ ≤ (cellLaw (source (subsequence k)) i).prob cell / (mass / 2) :=
      div_le_div_of_nonneg_left ((cellLaw (source (subsequence k)) i).prob_nonneg cell)
        (by linarith) hk.le
    _ ≤ ((Fintype.card ι : ℝ) * weight (source (subsequence k)) cell) / (mass / 2) := by
      apply div_le_div_of_nonneg_right _ (by linarith)
      simpa only [cellLaw_prob] using ownWeight_le (source (subsequence k)) i cell
    _ = _ := by change _ = ((2 / mass) * Fintype.card ι) * _; field_simp

/-- Whole-old-cell ordinary conditionals have an internally identified half-line weak limit. -/
theorem tendsto_referenceLaw_conditionalCutCellLaw
    (source : ℕ → ι → FinDist (Option ℕ)) (subsequence : ℕ → ℕ)
    (cuts : ℕ → ℝ)
    (hmem : ∀ k, cuts k ∈ (calendar (source (subsequence k))).endpoints)
    {cut : ℝ} (hcuts : Tendsto cuts atTop (𝓝 cut))
    (side : ChronologicalSide) (i : ι) {law : ProbabilityMeasure unitInterval}
    (hlaw : Tendsto (fun k => chartLaw (source (subsequence k)) i) atTop (𝓝 law))
    (hmass : 0 < (law : Measure unitInterval).real (rawCutEvent side cut)) :
    Tendsto (fun k => referenceLaw (source (subsequence k))
      (conditionalCutCellLaw (source (subsequence k)) side (cuts k) i)) atTop
      (𝓝 (cutConditionalLaw law side cut hmass)) := by
  have hmasslim := tendsto_probOf_cellCutEvent source subsequence cuts hmem hcuts side i hlaw
  have hpositive := hmasslim.eventually (lt_mem_nhds hmass)
  apply ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mpr
  intro test
  have h := (tendsto_integral_rawCutEvent_chartLaw source subsequence cuts hcuts side i hlaw
    test (test.integrable volume)).div hmasslim hmass.ne'
  have hintegral : ∫ x, test x ∂(cutConditionalLaw law side cut hmass : Measure unitInterval) =
      (∫ x, (rawCutEvent side cut).indicator test x ∂(law : Measure unitInterval)) /
        (law : Measure unitInterval).real (rawCutEvent side cut) := by
    change (∫ x, test x ∂ProbabilityTheory.cond (law : Measure unitInterval) _) = _
    rw [ProbabilityTheory.cond, integral_smul_measure, ENNReal.toReal_inv,
      integral_indicator (measurableSet_rawCutEvent side cut)]
    simp only [smul_eq_mul, measureReal_def, div_eq_mul_inv, mul_comm]
  rw [← hintegral] at h
  apply h.congr'
  filter_upwards [hpositive] with k hk
  exact (integral_referenceLaw_conditionalCutCellLaw
    (source (subsequence k)) side (cuts k) (hmem k) i hk test).symm

/-- One actual endpoint selector is produced before both conditioning sides, every owner and
every positive limiting marginal event. No additional subsequence is extracted. -/
theorem exists_chronological_conditioning_of_mem_limit_endpoints
    (source : ℕ → ι → FinDist (Option ℕ)) (subsequence : ℕ → ℕ)
    {limit : MathUE.MarkedCalendar.Calendar}
    (hE : Tendsto (fun k => (calendar (source (subsequence k))).endpoints) atTop
      (𝓝 limit.endpoints)) {cut : ℝ} (hcut : cut ∈ limit.endpoints) :
    ∃ cuts : ℕ → ℝ,
      (∀ k, cuts k ∈ (calendar (source (subsequence k))).endpoints) ∧
      Tendsto cuts atTop (𝓝 cut) ∧
      ∀ (side : ChronologicalSide) (i : ι) (law : ProbabilityMeasure unitInterval),
        Tendsto (fun k => chartLaw (source (subsequence k)) i) atTop (𝓝 law) →
        ∀ hmass : 0 < (law : Measure unitInterval).real (rawCutEvent side cut),
          (∀ᶠ k in atTop, ∀ cell : Cell (source (subsequence k)),
            (conditionalCutCellLaw (source (subsequence k)) side (cuts k) i).prob cell ≤
              ((2 / (law : Measure unitInterval).real (rawCutEvent side cut)) * Fintype.card ι) *
                weight (source (subsequence k)) cell) ∧
          Tendsto (fun k => referenceLaw (source (subsequence k))
            (conditionalCutCellLaw (source (subsequence k)) side (cuts k) i)) atTop
            (𝓝 (cutConditionalLaw law side cut hmass)) := by
  obtain ⟨cuts, hmem, hcuts⟩ :=
    Math.Topology.exists_mem_tendsto_of_nonemptyCompacts_tendsto hE hcut
  refine ⟨cuts, hmem, hcuts, ?_⟩
  intro side i law hlaw hmass
  exact ⟨eventually_conditionalCutCellLaw_le source subsequence cuts hmem hcuts side i hlaw hmass,
    tendsto_referenceLaw_conditionalCutCellLaw source subsequence cuts hmem hcuts side i hlaw hmass⟩

end GameTheory.MarkedCalendarChart
