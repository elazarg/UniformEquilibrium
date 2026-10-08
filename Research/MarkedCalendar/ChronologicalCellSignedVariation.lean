import Research.MarkedCalendar.ChronologicalCellConditioning

/-! # Signed chronological variations on unchanged old cells

The same whole-cell early and late events used by ordinary conditioning define
safe signed source laws. Their support and three-halves envelope hold at every
index, including fallback indices. Actual event-mass convergence produces one
positive signed radius before all parameters, and ordinary conditional weak
convergence supplies the actual signed weak limit on the same subsequence.

An all-index old-endpoint selector is produced before both sides, owners, and
parameters. The ordinary conditioning endpoint remains a different constructor;
no signed parameter-one or full-cap endpoint identity is asserted here. Joint
semantic carrier and SUM-floor consumers remain subsequent adapters.
-/

noncomputable section

open Set Filter MeasureTheory TopologicalSpace GameTheory.Math.Probability
open scoped Topology

namespace GameTheory.MarkedCalendarChart

variable {ι : Type} [Fintype ι] [Nonempty ι]

def signedCutCellLaw (laws : ι → FinDist (Option ℕ))
    (side : ChronologicalSide) (cut : ℝ) (i : ι) (parameter : ℝ) : FinDist (Cell laws) :=
  (cellLaw laws i).signedCondOrSelf (cellCutEvent laws side cut) parameter

/-- No old supported clock, including Never, disappears anywhere in the safe signed family. -/
theorem support_signedCutCellLaw (laws : ι → FinDist (Option ℕ))
    (side : ChronologicalSide) (cut : ℝ) (i : ι) (parameter : ℝ) :
    (signedCutCellLaw laws side cut i parameter).support = (cellLaw laws i).support :=
  FinDist.support_signedCondOrSelf ..

theorem signedCutCellLaw_zero (laws : ι → FinDist (Option ℕ))
    (side : ChronologicalSide) (cut : ℝ) (i : ι) :
    signedCutCellLaw laws side cut i 0 = cellLaw laws i :=
  FinDist.signedCondOrSelf_zero ..

theorem prob_signedCutCellLaw_bounds (laws : ι → FinDist (Option ℕ))
    (side : ChronologicalSide) (cut : ℝ) (i : ι) (parameter : ℝ) (cell : Cell laws) :
    (1 / 2 : ℝ) * (cellLaw laws i).prob cell ≤
        (signedCutCellLaw laws side cut i parameter).prob cell ∧
      (signedCutCellLaw laws side cut i parameter).prob cell ≤
        (3 / 2 : ℝ) * (cellLaw laws i).prob cell :=
  FinDist.prob_signedCondOrSelf_bounds ..

/-- The old-reference envelope is derived for every parameter and every source index. -/
theorem prob_signedCutCellLaw_le (laws : ι → FinDist (Option ℕ))
    (side : ChronologicalSide) (cut : ℝ) (i : ι) (parameter : ℝ) (cell : Cell laws) :
    (signedCutCellLaw laws side cut i parameter).prob cell ≤
      ((3 / 2 : ℝ) * Fintype.card ι) * weight laws cell := by
  have hbound := (prob_signedCutCellLaw_bounds laws side cut i parameter cell).2
  rw [cellLaw_prob] at hbound
  have hown := ownWeight_le laws i cell
  nlinarith

omit [Fintype ι] [Nonempty ι] in
def cutSignedRadius (law : ProbabilityMeasure unitInterval)
    (side : ChronologicalSide) (cut : ℝ) : ℝ :=
  min (1 / 2 : ℝ) ((law : Measure unitInterval).real (rawCutEvent side cut) / 4)

omit [Fintype ι] [Nonempty ι] in
theorem cutSignedRadius_pos (law : ProbabilityMeasure unitInterval)
    (side : ChronologicalSide) (cut : ℝ)
    (hmass : 0 < (law : Measure unitInterval).real (rawCutEvent side cut)) :
    0 < cutSignedRadius law side cut :=
  lt_min (by norm_num) (div_pos hmass (by norm_num))

omit [Fintype ι] [Nonempty ι] in
theorem cutSignedRadius_le_signedCondRadius (law : ProbabilityMeasure unitInterval)
    (side : ChronologicalSide) (cut : ℝ) :
    cutSignedRadius law side cut ≤ law.signedCondRadius (rawCutEvent side cut) := by
  apply min_le_min le_rfl
  have hmass : 0 ≤ (law : Measure unitInterval).real (rawCutEvent side cut) := measureReal_nonneg
  linarith

omit [Fintype ι] [Nonempty ι] in
def cutSignedLaw (law : ProbabilityMeasure unitInterval)
    (side : ChronologicalSide) (cut : ℝ)
    (hmass : 0 < (law : Measure unitInterval).real (rawCutEvent side cut))
    (parameter : ℝ) (hparameter : |parameter| ≤ cutSignedRadius law side cut) :
    ProbabilityMeasure unitInterval :=
  law.signedCond (rawCutEvent side cut) (measurableSet_rawCutEvent side cut) hmass parameter
    (hparameter.trans (cutSignedRadius_le_signedCondRadius law side cut))

omit [Fintype ι] [Nonempty ι] in
theorem cutSignedLaw_zero (law : ProbabilityMeasure unitInterval)
    (side : ChronologicalSide) (cut : ℝ)
    (hmass : 0 < (law : Measure unitInterval).real (rawCutEvent side cut)) :
    cutSignedLaw law side cut hmass 0
      (by simpa only [abs_zero] using (cutSignedRadius_pos law side cut hmass).le) = law :=
  ProbabilityMeasure.signedCond_zero law _ _ _

/-- Actual event-mass convergence gives eventual legality simultaneously for every parameter
in one fixed positive signed interval. -/
theorem eventually_signedCutCellLaw_valid
    (source : ℕ → ι → FinDist (Option ℕ)) (subsequence : ℕ → ℕ)
    (cuts : ℕ → ℝ)
    (hmem : ∀ k, cuts k ∈ (calendar (source (subsequence k))).endpoints)
    {cut : ℝ} (hcuts : Tendsto cuts atTop (𝓝 cut))
    (side : ChronologicalSide) (i : ι) {law : ProbabilityMeasure unitInterval}
    (hlaw : Tendsto (fun k => chartLaw (source (subsequence k)) i) atTop (𝓝 law))
    (hmass : 0 < (law : Measure unitInterval).real (rawCutEvent side cut)) :
    ∀ᶠ k in atTop, ∀ parameter : ℝ, |parameter| ≤ cutSignedRadius law side cut →
      0 < (cellLaw (source (subsequence k)) i).probOf
          (cellCutEvent (source (subsequence k)) side (cuts k)) ∧
        |parameter| ≤ (cellLaw (source (subsequence k)) i).signedCondRadius
          (cellCutEvent (source (subsequence k)) side (cuts k)) := by
  let mass := (law : Measure unitInterval).real (rawCutEvent side cut)
  have hmasslim := tendsto_probOf_cellCutEvent source subsequence cuts hmem hcuts side i hlaw
  have hpositive : 0 < mass := hmass
  filter_upwards [hmasslim.eventually (lt_mem_nhds (by linarith : mass / 2 < mass))] with k hk
  intro parameter hparameter
  refine ⟨by linarith, ?_⟩
  apply le_min (hparameter.trans (min_le_left _ _))
  have hsmall := hparameter.trans (min_le_right _ _)
  change |parameter| ≤ mass / 4 at hsmall
  linarith

private theorem integral_referenceLaw_signedCutCellLaw
    (laws : ι → FinDist (Option ℕ)) (side : ChronologicalSide) (cut : ℝ) (i : ι)
    (hmass : 0 < (cellLaw laws i).probOf (cellCutEvent laws side cut))
    (parameter : ℝ)
    (hparameter : |parameter| ≤ (cellLaw laws i).signedCondRadius (cellCutEvent laws side cut))
    (test : unitInterval → ℝ) (htest : Integrable test (chartLaw laws i : Measure unitInterval)) :
    ∫ x, test x ∂(referenceLaw laws (signedCutCellLaw laws side cut i parameter) :
      Measure unitInterval) =
      (1 - parameter) * (∫ x, test x ∂(chartLaw laws i : Measure unitInterval)) +
        parameter * ∫ x, test x ∂(referenceLaw laws (conditionalCutCellLaw laws side cut i) :
          Measure unitInterval) := by
  have hevent : MeasurableSet (decodeCell laws ⁻¹' cellCutEvent laws side cut) :=
    (cellCutEvent laws side cut).toFinite.measurableSet.preimage (measurable_decodeCell laws)
  have hpositive : 0 < (referenceLaw laws (cellLaw laws i) : Measure unitInterval).real
      (decodeCell laws ⁻¹' cellCutEvent laws side cut) := by
    rw [referenceLaw_decodeCell_event_real]
    exact hmass
  have hradius : |parameter| ≤ (referenceLaw laws (cellLaw laws i)).signedCondRadius
      (decodeCell laws ⁻¹' cellCutEvent laws side cut) := by
    rw [referenceLaw_signedCondRadius]
    exact hparameter
  have hordinary : (referenceLaw laws (conditionalCutCellLaw laws side cut i) :
      Measure unitInterval) = ProbabilityTheory.cond
        (referenceLaw laws (cellLaw laws i) : Measure unitInterval)
        (decodeCell laws ⁻¹' cellCutEvent laws side cut) := by
    change referenceMeasure laws
      (conditionalCellLaw laws (cellLaw laws i) (cellCutEvent laws side cut)) = _
    rw [conditionalCellLaw, dite_eq_left hmass, referenceMeasure_condOn laws _ _ hmass]
    rfl
  rw [signedCutCellLaw, FinDist.signedCondOrSelf_eq_signedCond _ _ hmass _ hparameter,
    referenceLaw_signedCond]
  have h := ProbabilityMeasure.integral_signedCond_eq_affine_cond
    (referenceLaw laws (cellLaw laws i)) _ hevent hpositive parameter hradius test htest
  rw [← hordinary] at h
  simpa only [chartLaw] using h

/-- The weak limit is the actual signed law of the raw half-line. The proof reuses the checked
ordinary conditional weak limit, not a supplied replacement-law convergence hypothesis. -/
theorem tendsto_referenceLaw_signedCutCellLaw
    (source : ℕ → ι → FinDist (Option ℕ)) (subsequence : ℕ → ℕ)
    (cuts : ℕ → ℝ)
    (hmem : ∀ k, cuts k ∈ (calendar (source (subsequence k))).endpoints)
    {cut : ℝ} (hcuts : Tendsto cuts atTop (𝓝 cut))
    (side : ChronologicalSide) (i : ι) {law : ProbabilityMeasure unitInterval}
    (hlaw : Tendsto (fun k => chartLaw (source (subsequence k)) i) atTop (𝓝 law))
    (hmass : 0 < (law : Measure unitInterval).real (rawCutEvent side cut))
    (parameter : ℝ) (hparameter : |parameter| ≤ cutSignedRadius law side cut) :
    Tendsto (fun k => referenceLaw (source (subsequence k))
      (signedCutCellLaw (source (subsequence k)) side (cuts k) i parameter)) atTop
      (𝓝 (cutSignedLaw law side cut hmass parameter hparameter)) := by
  have hvalid := eventually_signedCutCellLaw_valid
    source subsequence cuts hmem hcuts side i hlaw hmass
  have hord := tendsto_referenceLaw_conditionalCutCellLaw
    source subsequence cuts hmem hcuts side i hlaw hmass
  apply ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mpr
  intro test
  have hplain := (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hlaw) test
  have hconditional := (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hord) test
  have h := (hplain.const_mul (1 - parameter)).add (hconditional.const_mul parameter)
  have hintegral := ProbabilityMeasure.integral_signedCond_eq_affine_cond law
    (rawCutEvent side cut) (measurableSet_rawCutEvent side cut) hmass parameter
    (hparameter.trans (cutSignedRadius_le_signedCondRadius law side cut))
    test (test.integrable _)
  change (∫ x, test x ∂(cutSignedLaw law side cut hmass parameter hparameter :
      Measure unitInterval)) =
    (1 - parameter) * (∫ x, test x ∂(law : Measure unitInterval)) +
      parameter * ∫ x, test x ∂(cutConditionalLaw law side cut hmass : Measure unitInterval)
    at hintegral
  rw [← hintegral] at h
  apply h.congr'
  filter_upwards [hvalid] with k hk
  exact (integral_referenceLaw_signedCutCellLaw (source (subsequence k)) side (cuts k) i
    (hk parameter hparameter).1 parameter (hk parameter hparameter).2 test
    (test.integrable _)).symm

/-- The old-endpoint selector is fixed before conditioning sides, owners and all signed
parameters. Every positive actual limiting event supplies its own common signed radius. -/
theorem exists_chronological_signed_variation_of_mem_limit_endpoints
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
          0 < cutSignedRadius law side cut ∧
          ∀ (parameter : ℝ) (hparameter : |parameter| ≤ cutSignedRadius law side cut),
            Tendsto (fun k => referenceLaw (source (subsequence k))
              (signedCutCellLaw (source (subsequence k)) side (cuts k) i parameter)) atTop
              (𝓝 (cutSignedLaw law side cut hmass parameter hparameter)) := by
  obtain ⟨cuts, hmem, hcuts, _⟩ :=
    exists_chronological_conditioning_of_mem_limit_endpoints source subsequence hE hcut
  refine ⟨cuts, hmem, hcuts, ?_⟩
  intro side i law hlaw hmass
  exact ⟨cutSignedRadius_pos law side cut hmass, fun parameter hparameter =>
    tendsto_referenceLaw_signedCutCellLaw source subsequence cuts hmem hcuts side i
      hlaw hmass parameter hparameter⟩

end GameTheory.MarkedCalendarChart
