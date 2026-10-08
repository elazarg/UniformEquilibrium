import Research.MarkedCalendar.ReferenceLawTransport
import MathUE.MeasureTheory.FiniteProductDominatedWeakCompactness
import MathUE.Topology.NonemptyCompactLimits

/-! # Compactification of the actual finite-law charts

One subsequence of the specified source family simultaneously converges in its
endpoint calendars, full legal finite-menu images, cutoffs, and marginal chart
laws. The limiting marginals retain domination and the exact common mixture.
Every mark in the limiting menu is approached by genuine original menu replies.
The same subsequence gives every fixed finite-outcome expectation and every
original response expectation whose actual marks converge; Never is separate.
The integral dictionaries also apply to arbitrary actual finite laws on the old
reference cells, without changing the reference calendar or its reply marks.

The subsequence and limit objects are chosen before any test or limiting legal
mark. The menu is not enlarged to all geometrically compatible marks. Finite
cutoffs remain real marks, distinct from the separate Never response. Limiting
complete caps and original variation witnesses are not asserted here.
-/

noncomputable section

open Set Filter MeasureTheory TopologicalSpace GameTheory.Math.Probability
open scoped Topology BigOperators

namespace GameTheory.MarkedCalendarChart

variable {ι : Type} [Fintype ι] [Nonempty ι]

/-- The actual finite menu image as a nonempty compact set; its cutoff is a genuine reply. -/
def legalMenuCompacts (laws : ι → FinDist (Option ℕ)) : NonemptyCompacts ℝ where
  carrier := legalFiniteMenu laws
  isCompact' := (legalFiniteMenu laws).finite_toSet.isCompact
  nonempty' := ⟨cutoff laws, cutoff_mem_legalFiniteMenu laws⟩

theorem legalMenuCompacts_subset (laws : ι → FinDist (Option ℕ)) :
    (legalMenuCompacts laws : Set ℝ) ⊆ Icc 0 1 := by
  intro t ht
  obtain ⟨time, _, rfl⟩ := (mem_legalFiniteMenu_iff laws t).mp ht
  exact ⟨mark_nonneg laws time, (mark_le_cutoff laws time).trans (cutoff laws).property.2⟩

/-- Every limiting legal mark is realized along genuine finite entries of the original menus. -/
theorem exists_legal_reply_dates_tendsto
    (source : ℕ → ι → FinDist (Option ℕ)) (subsequence : ℕ → ℕ)
    {menu : NonemptyCompacts ℝ}
    (hmenu : Tendsto (fun k => legalMenuCompacts (source (subsequence k))) atTop (𝓝 menu))
    {t : ℝ} (ht : t ∈ menu) :
    ∃ dates : ℕ → ℕ,
      (∀ k, some (dates k) ∈ quittingFiniteOpponentAtomGapReplyMenu
        (quittingFiniteStoppingCalendar (source (subsequence k)))) ∧
      Tendsto (fun k => mark (source (subsequence k)) (dates k)) atTop (𝓝 t) := by
  obtain ⟨points, hmem, hpoints⟩ :=
    Math.Topology.exists_mem_tendsto_of_nonemptyCompacts_tendsto hmenu ht
  have hdates (k : ℕ) :=
    (mem_legalFiniteMenu_iff (source (subsequence k)) (points k)).mp (hmem k)
  choose dates hlegal hmark using hdates
  refine ⟨dates, hlegal, ?_⟩
  exact hpoints.congr' (Eventually.of_forall hmark)

private theorem sum_toFiniteMeasure_chartLaw (laws : ι → FinDist (Option ℕ)) :
    (∑ i, (chartLaw laws i).toFiniteMeasure) =
      (Fintype.card ι : NNReal) • base.toFiniteMeasure := by
  apply FiniteMeasure.toMeasure_injective
  simp only [FiniteMeasure.toMeasure_sum, FiniteMeasure.toMeasure_smul,
    ProbabilityMeasure.toMeasure_comp_toFiniteMeasure_eq_toMeasure]
  change (∑ i, chartMeasure laws i) =
    (Fintype.card ι : NNReal) • (volume : Measure unitInterval)
  rw [← Measure.coe_nnreal_smul]
  exact sum_chartMeasure laws

/-- The exact common mixture survives a weak limit of the same specified chart marginals. -/
theorem sum_limit_chartLaws
    (source : ℕ → ι → FinDist (Option ℕ)) (subsequence : ℕ → ℕ)
    {marginals : ι → ProbabilityMeasure unitInterval}
    (hlaws : Tendsto (fun k => chartLaw (source (subsequence k))) atTop (𝓝 marginals)) :
    (∑ i, (marginals i : Measure unitInterval)) =
      (Fintype.card ι : NNReal) • (base : Measure unitInterval) := by
  have hsum : Tendsto (fun k => ∑ i, (chartLaw (source (subsequence k)) i).toFiniteMeasure)
      atTop (𝓝 (∑ i, (marginals i).toFiniteMeasure)) := by
    apply tendsto_finsetSum
    intro i _
    exact ProbabilityMeasure.toFiniteMeasure_continuous.continuousAt.tendsto.comp
      (hlaws.apply_nhds i)
  have hconst : Tendsto
      (fun k => ∑ i, (chartLaw (source (subsequence k)) i).toFiniteMeasure) atTop
      (𝓝 ((Fintype.card ι : NNReal) • base.toFiniteMeasure)) := by
    simpa only [sum_toFiniteMeasure_chartLaw] using
      (tendsto_const_nhds : Tendsto
        (fun _ : ℕ => (Fintype.card ι : NNReal) • base.toFiniteMeasure) atTop _)
  have heq := congrArg (fun law : FiniteMeasure unitInterval => (law : Measure unitInterval))
    (tendsto_nhds_unique hsum hconst)
  simpa only [FiniteMeasure.toMeasure_sum, FiniteMeasure.toMeasure_smul,
    ProbabilityMeasure.toMeasure_comp_toFiniteMeasure_eq_toMeasure] using heq

/-- One actual source subsequence is selected before every test and every limiting legal mark.
No feasible limit, density, tester set, or transport certificate is supplied as an input. -/
theorem exists_chart_compactification (source : ℕ → ι → FinDist (Option ℕ)) :
    ∃ (subsequence : ℕ → ℕ) (limit : MathUE.MarkedCalendar.Calendar)
      (menu : NonemptyCompacts ℝ) (marginals : ι → ProbabilityMeasure unitInterval),
      StrictMono subsequence ∧
      Tendsto (fun k => (calendar (source (subsequence k))).endpoints) atTop
        (𝓝 limit.endpoints) ∧
      Tendsto (fun k => cutoff (source (subsequence k))) atTop (𝓝 limit.cutoff) ∧
      Tendsto (fun k => legalMenuCompacts (source (subsequence k))) atTop (𝓝 menu) ∧
      Tendsto (fun k => chartLaw (source (subsequence k))) atTop (𝓝 marginals) ∧
      (∀ i, (marginals i : Measure unitInterval) ≤
        (Fintype.card ι : NNReal) • (base : Measure unitInterval)) ∧
      (∑ i, (marginals i : Measure unitInterval)) =
        (Fintype.card ι : NNReal) • (base : Measure unitInterval) ∧
      (menu : Set ℝ) ⊆ Icc 0 (limit.cutoff : ℝ) ∧
      (limit.cutoff : ℝ) ∈ menu ∧
      ∀ t ∈ menu, ∃ dates : ℕ → ℕ,
        (∀ k, some (dates k) ∈ quittingFiniteOpponentAtomGapReplyMenu
          (quittingFiniteStoppingCalendar (source (subsequence k)))) ∧
        Tendsto (fun k => mark (source (subsequence k)) (dates k)) atTop (𝓝 t) := by
  let boundedSets : Set (NonemptyCompacts ℝ) := {s | (s : Set ℝ) ⊆ Icc 0 1}
  have hcompactSets : IsCompact boundedSets :=
    NonemptyCompacts.isCompact_subsets_of_isCompact isCompact_Icc
  let data (k : ℕ) : NonemptyCompacts ℝ × NonemptyCompacts ℝ × unitInterval ×
      (ι → ProbabilityMeasure unitInterval) :=
    ((calendar (source k)).endpoints, legalMenuCompacts (source k),
      cutoff (source k), chartLaw (source k))
  have hcompact : IsCompact (boundedSets ×ˢ boundedSets ×ˢ
      (univ : Set unitInterval) ×ˢ (univ : Set (ι → ProbabilityMeasure unitInterval))) :=
    hcompactSets.prod (hcompactSets.prod (isCompact_univ.prod isCompact_univ))
  have hmem (k : ℕ) : data k ∈ boundedSets ×ˢ boundedSets ×ˢ
      (univ : Set unitInterval) ×ˢ (univ : Set (ι → ProbabilityMeasure unitInterval)) :=
    ⟨(calendar (source k)).endpoints_subset, legalMenuCompacts_subset (source k),
      mem_univ _, mem_univ _⟩
  obtain ⟨point, hpoint, subsequence, hmono, hdata⟩ := hcompact.tendsto_subseq hmem
  have hE : Tendsto (fun k => (calendar (source (subsequence k))).endpoints)
      atTop (𝓝 point.1) := hdata.fst_nhds
  have hT : Tendsto (fun k => legalMenuCompacts (source (subsequence k)))
      atTop (𝓝 point.2.1) := hdata.snd_nhds.fst_nhds
  have hc : Tendsto (fun k => cutoff (source (subsequence k)))
      atTop (𝓝 point.2.2.1) := hdata.snd_nhds.snd_nhds.fst_nhds
  have hμ : Tendsto (fun k => chartLaw (source (subsequence k)))
      atTop (𝓝 point.2.2.2) := hdata.snd_nhds.snd_nhds.snd_nhds
  have hcReal : Tendsto (fun k => (cutoff (source (subsequence k)) : ℝ))
      atTop (𝓝 (point.2.2.1 : ℝ)) := continuous_subtype_val.continuousAt.tendsto.comp hc
  let limit : MathUE.MarkedCalendar.Calendar :=
    { endpoints := point.1
      cutoff := point.2.2.1
      endpoints_subset := hpoint.1
      zero_mem := Math.Topology.mem_limit_of_nonemptyCompacts_tendsto hE tendsto_const_nhds
        (Eventually.of_forall fun k => (calendar (source (subsequence k))).zero_mem)
      one_mem := Math.Topology.mem_limit_of_nonemptyCompacts_tendsto hE tendsto_const_nhds
        (Eventually.of_forall fun k => (calendar (source (subsequence k))).one_mem)
      cutoff_mem := Math.Topology.mem_limit_of_nonemptyCompacts_tendsto hE hcReal
        (Eventually.of_forall fun k => (calendar (source (subsequence k))).cutoff_mem) }
  refine ⟨subsequence, limit, point.2.1, point.2.2.2, hmono, hE, hc, hT, hμ, ?_,
    sum_limit_chartLaws source subsequence hμ, ?_, ?_, ?_⟩
  · intro i
    exact ProbabilityMeasure.le_of_tendsto_of_le_measure _ (hμ.apply_nhds i)
      (Eventually.of_forall fun k => chartLaw_le (source (subsequence k)) i)
  · intro t ht
    obtain ⟨dates, _, hdates⟩ := exists_legal_reply_dates_tendsto source subsequence hT ht
    refine ⟨le_of_tendsto_of_tendsto tendsto_const_nhds hdates
      (Eventually.of_forall fun k => mark_nonneg (source (subsequence k)) (dates k)), ?_⟩
    exact le_of_tendsto_of_tendsto hdates hcReal
      (Eventually.of_forall fun k => mark_le_cutoff (source (subsequence k)) (dates k))
  · exact Math.Topology.mem_limit_of_nonemptyCompacts_tendsto hT hcReal
      (Eventually.of_forall fun k => cutoff_mem_legalFiniteMenu (source (subsequence k)))
  · intro t ht
    exact exists_legal_reply_dates_tendsto source subsequence hT ht

attribute [local instance] outcomeMeasurableSpace outcomeMeasurableSingletonClass

omit [Nonempty ι] in
private theorem integral_outcomeLaw_eq_expect (law : FinDist (QuittingTerminalOutcome ι))
    (reward : QuittingTerminalOutcome ι → ℝ) :
    (∫ outcome, reward outcome ∂law.toMeasure) = law.expect reward := by
  classical
  rw [integral_fintype (Integrable.of_finite), FinDist.expect_eq_sum]
  simp only [FinDist.toMeasure_real_singleton, smul_eq_mul]

/-- The unchanged reference kernel integrates to the actual replacement terminal law. -/
theorem integral_payoffKernel_referenceProduct (laws : ι → FinDist (Option ℕ))
    (p : ι → FinDist (Cell laws)) (reward : Finset ι → ℝ) :
    (∫ sample, MathUE.MarkedCalendar.payoffKernel (calendar laws) reward sample
      ∂(ProbabilityMeasure.pi (fun i => referenceLaw laws (p i)) :
        Measure (ι → unitInterval))) =
      ((FinDist.pi (fun i => referenceOriginalLaw laws (p i))).map
        quittingFirstStoppingOutcome).expect
        (fun outcome => reward (outcomeLabelsEquiv outcome)) := by
  change (∫ sample, MathUE.MarkedCalendar.payoffKernel (calendar laws) reward sample
    ∂Measure.pi (fun i => referenceMeasure laws (p i))) = _
  have hreward : StronglyMeasurable (fun outcome : QuittingTerminalOutcome ι =>
      reward (outcomeLabelsEquiv outcome)) :=
    (measurable_of_countable _).stronglyMeasurable
  have h := integral_map_of_stronglyMeasurable
    (μ := Measure.pi (fun i => referenceMeasure laws (p i)))
    (measurable_chartOutcome laws) hreward
  rw [referenceProduct_map_outcome, integral_outcomeLaw_eq_expect] at h
  simpa only [chartOutcome, Equiv.apply_symm_apply, MathUE.MarkedCalendar.payoffKernel] using h.symm

/-- The original chart is the source-cell specialization of the reference dictionary. -/
theorem integral_payoffKernel_chartProduct (laws : ι → FinDist (Option ℕ))
    (reward : Finset ι → ℝ) :
    (∫ sample, MathUE.MarkedCalendar.payoffKernel (calendar laws) reward sample
      ∂(ProbabilityMeasure.pi (chartLaw laws) : Measure (ι → unitInterval))) =
      ((FinDist.pi laws).map quittingFirstStoppingOutcome).expect
        (fun outcome => reward (outcomeLabelsEquiv outcome)) := by
  change (∫ sample, MathUE.MarkedCalendar.payoffKernel (calendar laws) reward sample
    ∂(ProbabilityMeasure.pi (fun i => referenceLaw laws (cellLaw laws i)) :
      Measure (ι → unitInterval))) = _
  simpa only [referenceOriginalLaw_cellLaw] using
    integral_payoffKernel_referenceProduct laws (cellLaw laws) reward

section ResponseIntegrals

variable [DecidableEq ι]

/-- Every original reply has its exact replacement-law expectation on the old reference chart,
including unsupported deadlines and literal Never. -/
theorem integral_responsePayoffKernel_referenceOpponents (laws : ι → FinDist (Option ℕ))
    (p : ι → FinDist (Cell laws))
    (who : ι) (choice : Option ℕ) (reward : Finset ι → ℝ) :
    (∫ sample, MathUE.MarkedCalendar.responsePayoffKernel (calendar laws) who
      (markedClock laws (quittingStoppingTimeValue choice)) reward sample
      ∂(ProbabilityMeasure.pi (fun j : {j : ι // j ≠ who} => referenceLaw laws (p j.val)) :
        Measure ({j : ι // j ≠ who} → unitInterval))) =
      ((FinDist.pi (Function.update (fun i => referenceOriginalLaw laws (p i))
        who (FinDist.pure choice))).map quittingFirstStoppingOutcome).expect
          (fun outcome => reward (outcomeLabelsEquiv outcome)) := by
  change (∫ sample, MathUE.MarkedCalendar.responsePayoffKernel (calendar laws) who
    (markedClock laws (quittingStoppingTimeValue choice)) reward sample
    ∂Measure.pi (fun j : {j : ι // j ≠ who} => referenceMeasure laws (p j.val))) = _
  have hreward : StronglyMeasurable (fun outcome : QuittingTerminalOutcome ι =>
      reward (outcomeLabelsEquiv outcome)) :=
    (measurable_of_countable _).stronglyMeasurable
  have h := integral_map_of_stronglyMeasurable
    (μ := Measure.pi (fun j : {j : ι // j ≠ who} => referenceMeasure laws (p j.val)))
    (measurable_chartResponseOutcome laws who choice) hreward
  rw [referenceOpponentProduct_map_responseOutcome_update, integral_outcomeLaw_eq_expect] at h
  simpa only [chartResponseOutcome, Equiv.apply_symm_apply,
    MathUE.MarkedCalendar.responsePayoffKernel] using h.symm

/-- Every original reply, including Never, has its exact source expectation in the fixed chart. -/
theorem integral_responsePayoffKernel_chartOpponents (laws : ι → FinDist (Option ℕ))
    (who : ι) (choice : Option ℕ) (reward : Finset ι → ℝ) :
    (∫ sample, MathUE.MarkedCalendar.responsePayoffKernel (calendar laws) who
      (markedClock laws (quittingStoppingTimeValue choice)) reward sample
      ∂(ProbabilityMeasure.pi (fun j : {j : ι // j ≠ who} => chartLaw laws j.val) :
        Measure ({j : ι // j ≠ who} → unitInterval))) =
      ((FinDist.pi (Function.update laws who (FinDist.pure choice))).map
        quittingFirstStoppingOutcome).expect
          (fun outcome => reward (outcomeLabelsEquiv outcome)) := by
  simpa only [chartLaw, referenceOriginalLaw_cellLaw] using
    integral_responsePayoffKernel_referenceOpponents laws (cellLaw laws) who choice reward

end ResponseIntegrals

private instance base_nullSingleton : NullSingletonClass (base : Measure unitInterval) :=
  inferInstanceAs (NullSingletonClass (volume : Measure unitInterval))

/-- Actual moving outcome kernels converge under the same weakly converging source chart laws. -/
theorem tendsto_source_outcome_expect
    (source : ℕ → ι → FinDist (Option ℕ)) (subsequence : ℕ → ℕ)
    {limit : MathUE.MarkedCalendar.Calendar} {marginals : ι → ProbabilityMeasure unitInterval}
    (hE : Tendsto (fun k => (calendar (source (subsequence k))).endpoints) atTop
      (𝓝 limit.endpoints))
    (hc : Tendsto (fun k => cutoff (source (subsequence k))) atTop (𝓝 limit.cutoff))
    (hlaws : Tendsto (fun k => chartLaw (source (subsequence k))) atTop (𝓝 marginals))
    (reward : Finset ι → ℝ) :
    Tendsto (fun k => ((FinDist.pi (source (subsequence k))).map
      quittingFirstStoppingOutcome).expect (fun outcome => reward (outcomeLabelsEquiv outcome)))
      atTop (𝓝 (∫ sample, MathUE.MarkedCalendar.payoffKernel limit reward sample
        ∂(ProbabilityMeasure.pi marginals : Measure (ι → unitInterval)))) := by
  have hproduct := ProbabilityMeasure.continuous_pi.continuousAt.tendsto.comp hlaws
  have hbound (k : ℕ) := ProbabilityMeasure.pi_le_smul_pi_of_le
    (fun _ : ι => base) (chartLaw (source (subsequence k)))
    (fun _ : ι => (Fintype.card ι : NNReal)) (chartLaw_le (source (subsequence k)))
  have h := ProbabilityMeasure.tendsto_integral_moving_test_of_tendsto_of_le_smul
    (ProbabilityMeasure.pi (fun _ : ι => base)) (∏ _ : ι, (Fintype.card ι : NNReal))
    hproduct (Eventually.of_forall hbound) (MathUE.MarkedCalendar.payoffKernel limit reward)
    (MathUE.MarkedCalendar.integrable_payoffKernel limit reward _)
    (fun k => MathUE.MarkedCalendar.payoffKernel (calendar (source (subsequence k))) reward)
    (Eventually.of_forall fun k => MathUE.MarkedCalendar.integrable_payoffKernel
      (calendar (source (subsequence k))) reward _)
    (MathUE.MarkedCalendar.tendsto_integral_norm_payoffKernel_sub base hE hc reward)
  simpa only [Function.comp_def, integral_payoffKernel_chartProduct] using h

section ResponseLimits

variable [DecidableEq ι]

/-- Arbitrary original finite dates are allowed; their actual marks, not their indices, converge. -/
theorem tendsto_source_finite_reply_expect
    (source : ℕ → ι → FinDist (Option ℕ)) (subsequence : ℕ → ℕ)
    {limit : MathUE.MarkedCalendar.Calendar} {marginals : ι → ProbabilityMeasure unitInterval}
    (hE : Tendsto (fun k => (calendar (source (subsequence k))).endpoints) atTop
      (𝓝 limit.endpoints))
    (hc : Tendsto (fun k => cutoff (source (subsequence k))) atTop (𝓝 limit.cutoff))
    (hlaws : Tendsto (fun k => chartLaw (source (subsequence k))) atTop (𝓝 marginals))
    (who : ι) (reward : Finset ι → ℝ) (dates : ℕ → ℕ) {t : ℝ}
    (ht : Tendsto (fun k => mark (source (subsequence k)) (dates k)) atTop (𝓝 t)) :
    Tendsto (fun k => ((FinDist.pi (Function.update (source (subsequence k)) who
      (FinDist.pure (some (dates k))))).map quittingFirstStoppingOutcome).expect
        (fun outcome => reward (outcomeLabelsEquiv outcome))) atTop
      (𝓝 (∫ sample, MathUE.MarkedCalendar.responsePayoffKernel limit who (t : WithTop ℝ)
        reward sample ∂(ProbabilityMeasure.pi (fun j : {j : ι // j ≠ who} => marginals j.val) :
          Measure ({j : ι // j ≠ who} → unitInterval)))) := by
  have hopponents : Tendsto
      (fun k => fun j : {j : ι // j ≠ who} => chartLaw (source (subsequence k)) j.val)
      atTop (𝓝 (fun j : {j : ι // j ≠ who} => marginals j.val)) :=
    tendsto_pi_nhds.mpr fun j => hlaws.apply_nhds j.val
  have hproduct := ProbabilityMeasure.continuous_pi.continuousAt.tendsto.comp hopponents
  have hbound (k : ℕ) := ProbabilityMeasure.pi_le_smul_pi_of_le
    (fun _ : {j : ι // j ≠ who} => base)
    (fun j : {j : ι // j ≠ who} => chartLaw (source (subsequence k)) j.val)
    (fun _ : {j : ι // j ≠ who} => (Fintype.card ι : NNReal))
    (fun j => chartLaw_le (source (subsequence k)) j.val)
  have h := ProbabilityMeasure.tendsto_integral_moving_test_of_tendsto_of_le_smul
    (ProbabilityMeasure.pi (fun _ : {j : ι // j ≠ who} => base))
    (∏ _ : {j : ι // j ≠ who}, (Fintype.card ι : NNReal)) hproduct
    (Eventually.of_forall hbound)
    (MathUE.MarkedCalendar.responsePayoffKernel limit who (t : WithTop ℝ) reward)
    (MathUE.MarkedCalendar.integrable_responsePayoffKernel limit who _ reward _)
    (fun k => MathUE.MarkedCalendar.responsePayoffKernel (calendar (source (subsequence k)))
      who (mark (source (subsequence k)) (dates k) : WithTop ℝ) reward)
    (Eventually.of_forall fun k => MathUE.MarkedCalendar.integrable_responsePayoffKernel
      (calendar (source (subsequence k))) who _ reward _)
    (MathUE.MarkedCalendar.tendsto_integral_norm_responsePayoffKernel_sub base hE hc ht
      (fun k => atomCompatible_mark (source (subsequence k)) (dates k)) who reward)
  exact h.congr' (Eventually.of_forall fun k =>
    integral_responsePayoffKernel_chartOpponents
      (source (subsequence k)) who (some (dates k)) reward)

/-- Literal Never has its own response limit, not the finite cutoff response. -/
theorem tendsto_source_never_reply_expect
    (source : ℕ → ι → FinDist (Option ℕ)) (subsequence : ℕ → ℕ)
    {limit : MathUE.MarkedCalendar.Calendar} {marginals : ι → ProbabilityMeasure unitInterval}
    (hE : Tendsto (fun k => (calendar (source (subsequence k))).endpoints) atTop
      (𝓝 limit.endpoints))
    (hc : Tendsto (fun k => cutoff (source (subsequence k))) atTop (𝓝 limit.cutoff))
    (hlaws : Tendsto (fun k => chartLaw (source (subsequence k))) atTop (𝓝 marginals))
    (who : ι) (reward : Finset ι → ℝ) :
    Tendsto (fun k => ((FinDist.pi (Function.update (source (subsequence k)) who
      (FinDist.pure none))).map quittingFirstStoppingOutcome).expect
        (fun outcome => reward (outcomeLabelsEquiv outcome))) atTop
      (𝓝 (∫ sample, MathUE.MarkedCalendar.responsePayoffKernel limit who ⊤ reward sample
        ∂(ProbabilityMeasure.pi (fun j : {j : ι // j ≠ who} => marginals j.val) :
          Measure ({j : ι // j ≠ who} → unitInterval)))) := by
  have hopponents : Tendsto
      (fun k => fun j : {j : ι // j ≠ who} => chartLaw (source (subsequence k)) j.val)
      atTop (𝓝 (fun j : {j : ι // j ≠ who} => marginals j.val)) :=
    tendsto_pi_nhds.mpr fun j => hlaws.apply_nhds j.val
  have hproduct := ProbabilityMeasure.continuous_pi.continuousAt.tendsto.comp hopponents
  have hbound (k : ℕ) := ProbabilityMeasure.pi_le_smul_pi_of_le
    (fun _ : {j : ι // j ≠ who} => base)
    (fun j : {j : ι // j ≠ who} => chartLaw (source (subsequence k)) j.val)
    (fun _ : {j : ι // j ≠ who} => (Fintype.card ι : NNReal))
    (fun j => chartLaw_le (source (subsequence k)) j.val)
  have h := ProbabilityMeasure.tendsto_integral_moving_test_of_tendsto_of_le_smul
    (ProbabilityMeasure.pi (fun _ : {j : ι // j ≠ who} => base))
    (∏ _ : {j : ι // j ≠ who}, (Fintype.card ι : NNReal)) hproduct
    (Eventually.of_forall hbound) (MathUE.MarkedCalendar.responsePayoffKernel limit who ⊤ reward)
    (MathUE.MarkedCalendar.integrable_responsePayoffKernel limit who _ reward _)
    (fun k => MathUE.MarkedCalendar.responsePayoffKernel (calendar (source (subsequence k)))
      who ⊤ reward)
    (Eventually.of_forall fun k => MathUE.MarkedCalendar.integrable_responsePayoffKernel
      (calendar (source (subsequence k))) who _ reward _)
    (MathUE.MarkedCalendar.tendsto_integral_norm_never_responsePayoffKernel_sub base hE hc
      who reward)
  have hsource (k : ℕ) := integral_responsePayoffKernel_chartOpponents
    (source (subsequence k)) who none reward
  simp only [quittingStoppingTimeValue, markedClock, WithTop.map_top] at hsource
  simpa only [Function.comp_def, hsource] using h

/-- The actual source subsequence precedes all rewards, players, and reply sequences.
Kernel L¹ convergence and product domination are derived, not supplied as hypotheses. -/
theorem exists_chart_compactification_expectation_limits
    (source : ℕ → ι → FinDist (Option ℕ)) :
    ∃ (subsequence : ℕ → ℕ) (limit : MathUE.MarkedCalendar.Calendar)
      (menu : NonemptyCompacts ℝ) (marginals : ι → ProbabilityMeasure unitInterval),
      StrictMono subsequence ∧
      Tendsto (fun k => (calendar (source (subsequence k))).endpoints) atTop
        (𝓝 limit.endpoints) ∧
      Tendsto (fun k => cutoff (source (subsequence k))) atTop (𝓝 limit.cutoff) ∧
      Tendsto (fun k => legalMenuCompacts (source (subsequence k))) atTop (𝓝 menu) ∧
      Tendsto (fun k => chartLaw (source (subsequence k))) atTop (𝓝 marginals) ∧
      (∀ i, (marginals i : Measure unitInterval) ≤
        (Fintype.card ι : NNReal) • (base : Measure unitInterval)) ∧
      (∑ i, (marginals i : Measure unitInterval)) =
        (Fintype.card ι : NNReal) • (base : Measure unitInterval) ∧
      (menu : Set ℝ) ⊆ Icc 0 (limit.cutoff : ℝ) ∧
      (limit.cutoff : ℝ) ∈ menu ∧
      (∀ t ∈ menu, ∃ dates : ℕ → ℕ,
        (∀ k, some (dates k) ∈ quittingFiniteOpponentAtomGapReplyMenu
          (quittingFiniteStoppingCalendar (source (subsequence k)))) ∧
        Tendsto (fun k => mark (source (subsequence k)) (dates k)) atTop (𝓝 t)) ∧
      (∀ reward : Finset ι → ℝ,
        Tendsto (fun k => ((FinDist.pi (source (subsequence k))).map
          quittingFirstStoppingOutcome).expect
            (fun outcome => reward (outcomeLabelsEquiv outcome))) atTop
          (𝓝 (∫ sample, MathUE.MarkedCalendar.payoffKernel limit reward sample
            ∂(ProbabilityMeasure.pi marginals : Measure (ι → unitInterval))))) ∧
      (∀ (who : ι) (reward : Finset ι → ℝ) (dates : ℕ → ℕ) (t : ℝ),
        Tendsto (fun k => mark (source (subsequence k)) (dates k)) atTop (𝓝 t) →
        Tendsto (fun k => ((FinDist.pi (Function.update (source (subsequence k)) who
          (FinDist.pure (some (dates k))))).map quittingFirstStoppingOutcome).expect
            (fun outcome => reward (outcomeLabelsEquiv outcome))) atTop
          (𝓝 (∫ sample, MathUE.MarkedCalendar.responsePayoffKernel limit who (t : WithTop ℝ)
            reward sample
            ∂(ProbabilityMeasure.pi (fun j : {j : ι // j ≠ who} => marginals j.val) :
              Measure ({j : ι // j ≠ who} → unitInterval))))) ∧
      ∀ (who : ι) (reward : Finset ι → ℝ),
        Tendsto (fun k => ((FinDist.pi (Function.update (source (subsequence k)) who
          (FinDist.pure none))).map quittingFirstStoppingOutcome).expect
            (fun outcome => reward (outcomeLabelsEquiv outcome))) atTop
          (𝓝 (∫ sample, MathUE.MarkedCalendar.responsePayoffKernel limit who ⊤ reward sample
            ∂(ProbabilityMeasure.pi (fun j : {j : ι // j ≠ who} => marginals j.val) :
              Measure ({j : ι // j ≠ who} → unitInterval)))) := by
  obtain ⟨subsequence, limit, menu, marginals, hmono, hE, hc, hT, hμ, hbound,
    hsum, hsubset, hcutoff, hdates⟩ := exists_chart_compactification source
  refine ⟨subsequence, limit, menu, marginals, hmono, hE, hc, hT, hμ, hbound,
    hsum, hsubset, hcutoff, hdates, ?_, ?_, ?_⟩
  · intro reward
    exact tendsto_source_outcome_expect source subsequence hE hc hμ reward
  · intro who reward dates t ht
    exact tendsto_source_finite_reply_expect source subsequence hE hc hμ who reward dates ht
  · intro who reward
    exact tendsto_source_never_reply_expect source subsequence hE hc hμ who reward

end ResponseLimits

end GameTheory.MarkedCalendarChart
