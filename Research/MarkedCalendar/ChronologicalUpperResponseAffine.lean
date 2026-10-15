import Research.MarkedCalendar.UpperResponseCapStability
import Research.MarkedCalendar.ChronologicalCellSemanticVariation

/-! # One affine law for all marked upper responses

Actual partial-active late conditionals on the unchanged source charts have
one limiting positive multiplier and one Never-anchored additive constant
before all upper legal tests. Source endpoint selectors precede the parameters
and rewards. Inactive owners require no late mass, and empty activity is the
identity. All probability and moving-response limits are derived from the
actual source, not supplied as affine-law certificates.

This is an open-upper response identity. It does not supply the closed seam
identity, compact lower-region cap stability, or an endpoint minimum.
-/

noncomputable section

open Set Filter MeasureTheory TopologicalSpace GameTheory.Math.Probability
open scoped Topology BigOperators

namespace GameTheory.MarkedCalendarChart

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]

def partialSignedLateMarginals (marginals : ι → ProbabilityMeasure unitInterval)
    (active : Finset ι) (cut : ℝ)
    (hmasses : ∀ i : {i // i ∈ active},
      0 < (marginals i.1 : Measure unitInterval).real (rawCutEvent .after cut))
    (parameters : ι → ℝ)
    (hparameters : ∀ i : {i // i ∈ active},
      |parameters i.1| ≤ cutSignedRadius (marginals i.1) .after cut) :
    ι → ProbabilityMeasure unitInterval :=
  signedChronologicalMarginals marginals active (fun _ => .after) (fun _ => cut)
    hmasses (fun i => parameters i.1) hparameters

/-- Only active opponents contribute a nontrivial multiplier. -/
def partialSignedLateLimitMultiplier (marginals : ι → ProbabilityMeasure unitInterval)
    (who : ι) (active : Finset ι) (cut : ℝ) (parameters : ι → ℝ) : ℝ :=
  ∏ j : {j : ι // j ≠ who}, if j.val ∈ active then
    (1 - parameters j.val) + parameters j.val /
      (marginals j.val : Measure unitInterval).real (rawCutEvent .after cut) else 1

omit [Nonempty ι] in
theorem partialSignedLateLimitMultiplier_pos
    (marginals : ι → ProbabilityMeasure unitInterval) (who : ι)
    (active : Finset ι) (cut : ℝ)
    (hmasses : ∀ i : {i // i ∈ active},
      0 < (marginals i.1 : Measure unitInterval).real (rawCutEvent .after cut))
    (parameters : ι → ℝ)
    (hparameters : ∀ i : {i // i ∈ active},
      |parameters i.1| ≤ cutSignedRadius (marginals i.1) .after cut) :
    0 < partialSignedLateLimitMultiplier marginals who active cut parameters := by
  unfold partialSignedLateLimitMultiplier
  apply Finset.prod_pos
  intro j _
  by_cases hj : j.val ∈ active
  · rw [ite_eq_left hj]
    have hlegal := (hparameters ⟨j.val, hj⟩).trans
      (cutSignedRadius_le_signedCondRadius (marginals j.val) .after cut)
    have hbound := _root_.Math.Probability.signedConditioningLikelihood_bounds
      _ (hmasses ⟨j.val, hj⟩) measureReal_le_one (parameters j.val) hlegal True
    simp only [ite_true] at hbound
    linarith [hbound.1]
  · simp only [ite_eq_right hj, zero_lt_one]

private theorem partialSignedLateCellLaw_eq_chronological
    (source : ℕ → ι → FinDist (Option ℕ)) (subsequence : ℕ → ℕ)
    (active : Finset ι) (cuts : ℕ → ℝ) (parameters : ι → ℝ) (k : ℕ) (i : ι) :
    partialSignedLateCellLaw (source (subsequence k)) active (cuts k) parameters i =
      signedChronologicalReplacement source subsequence active (fun _ => .after)
        (fun _ => cuts) (fun i => parameters i.1) k i := by
  by_cases hi : i ∈ active
  · simp only [partialSignedLateCellLaw, signedChronologicalReplacement,
      ite_eq_left hi, dite_eq_left hi]
  · simp only [partialSignedLateCellLaw, signedChronologicalReplacement,
      ite_eq_right hi, dite_eq_right hi]

/-- The opponent-only observable is the same canonical original pure-reply expectation. -/
private theorem expect_upperCellReplyPayoff (laws : ι → FinDist (Option ℕ))
    (p : ι → FinDist (Cell laws)) (who : ι) (choice : Option ℕ) (reward : Finset ι → ℝ) :
    (FinDist.pi (fun j : {j : ι // j ≠ who} => p j.val)).expect
      (upperCellReplyPayoff laws who choice reward) =
      (FinDist.pi p).expect (referenceCellReplyPayoff laws who choice reward) := by
  rw [expect_referenceCellReplyPayoff, pi_update_pure_eq_map_opponents,
    FinDist.map_comp, FinDist.expect_map, ← referenceCellProduct_map_originalChoice,
    FinDist.expect_map]
  rfl

private theorem tendsto_partialSignedLateResponseMultiplier
    (source : ℕ → ι → FinDist (Option ℕ)) (subsequence : ℕ → ℕ)
    {marginals : ι → ProbabilityMeasure unitInterval}
    (hlaws : Tendsto (fun k => chartLaw (source (subsequence k))) atTop (𝓝 marginals))
    (cuts : ℕ → ℝ) (hmem : ∀ k, cuts k ∈ (calendar (source (subsequence k))).endpoints)
    {cut : ℝ} (hcuts : Tendsto cuts atTop (𝓝 cut)) (who : ι) (active : Finset ι)
    (hmasses : ∀ i : {i // i ∈ active},
      0 < (marginals i.1 : Measure unitInterval).real (rawCutEvent .after cut))
    (parameters : ι → ℝ) :
    Tendsto (fun k => partialSignedLateResponseMultiplier
      (source (subsequence k)) who active (cuts k) parameters) atTop
      (𝓝 (partialSignedLateLimitMultiplier marginals who active cut parameters)) := by
  unfold partialSignedLateResponseMultiplier partialSignedLateLimitMultiplier
  apply tendsto_finsetProd
  intro j _
  by_cases hj : j.val ∈ active
  · simp only [ite_eq_left hj]
    exact tendsto_const_nhds.add (tendsto_const_nhds.div
      (tendsto_probOf_cellCutEvent source subsequence cuts hmem hcuts .after j.val
        ((tendsto_pi_nhds.mp hlaws) j.val)) (hmasses ⟨j.val, hj⟩).ne')
  · simpa only [ite_eq_right hj] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1))

omit [DecidableEq ι] in
private theorem cut_lt_one_of_positive_limit_late_mass
    (source : ℕ → ι → FinDist (Option ℕ)) (subsequence : ℕ → ℕ)
    (i : ι) {law : ProbabilityMeasure unitInterval}
    (hlaw : Tendsto (fun k => chartLaw (source (subsequence k)) i) atTop (𝓝 law))
    {cut : ℝ} (hmass : 0 < (law : Measure unitInterval).real (rawCutEvent .after cut)) :
    cut < 1 := by
  have hbound : (law : Measure unitInterval) ≤
      (Fintype.card ι : NNReal) • (base : Measure unitInterval) :=
    ProbabilityMeasure.le_of_tendsto_of_le_measure _ hlaw
      (Eventually.of_forall fun k => chartLaw_le (source (subsequence k)) i)
  have habs : (law : Measure unitInterval) ≪ volume :=
    Measure.absolutelyContinuous_of_le_smul hbound
  by_contra hnot
  have hge := le_of_not_gt hnot
  have hsubset : rawCutEvent .after cut ⊆ ({1} : Set unitInterval) := by
    intro x hx
    change cut ≤ (x : ℝ) at hx
    change x = (1 : unitInterval)
    apply Subtype.ext
    exact le_antisymm x.property.2 (hge.trans hx)
  have hzero : (law : Measure unitInterval) (rawCutEvent .after cut) = 0 :=
    measure_mono_null hsubset (habs (measure_singleton _))
  rw [measureReal_def, hzero, ENNReal.toReal_zero] at hmass
  exact (lt_irrefl 0) hmass

private def lateSignedBound : ι → NNReal :=
  fun _ => ⟨(3 / 2 : ℝ) * Fintype.card ι, by positivity⟩

/-- One actual source cut precedes every legal parameter vector and every reward. For each
owner one Never-anchored constant works on the entire open upper legal response family. -/
theorem exists_partialSignedLate_limitReplyValue_affine
    (source : ℕ → ι → FinDist (Option ℕ)) (subsequence : ℕ → ℕ)
    {limit : MathUE.MarkedCalendar.Calendar} {menu : NonemptyCompacts ℝ}
    {marginals : ι → ProbabilityMeasure unitInterval}
    (hE : Tendsto (fun k => (calendar (source (subsequence k))).endpoints) atTop
      (𝓝 limit.endpoints))
    (hc : Tendsto (fun k => cutoff (source (subsequence k))) atTop (𝓝 limit.cutoff))
    (hT : Tendsto (fun k => legalMenuCompacts (source (subsequence k))) atTop (𝓝 menu))
    (hlaws : Tendsto (fun k => chartLaw (source (subsequence k))) atTop (𝓝 marginals))
    (cut : ℝ) (hcut : cut ∈ limit.endpoints) (active : Finset ι)
    (hmasses : ∀ i : {i // i ∈ active},
      0 < (marginals i.1 : Measure unitInterval).real (rawCutEvent .after cut)) :
    ∃ cuts : ℕ → ℝ,
      (∀ k, cuts k ∈ (calendar (source (subsequence k))).endpoints) ∧
      Tendsto cuts atTop (𝓝 cut) ∧
      ∀ (parameters : ι → ℝ)
        (hparameters : ∀ i : {i // i ∈ active},
          |parameters i.1| ≤ cutSignedRadius (marginals i.1) .after cut)
        (who : ι) (reward : Finset ι → ℝ),
        0 < partialSignedLateLimitMultiplier marginals who active cut parameters ∧
        ∃ constant : ℝ, ∀ reply : LimitReply menu,
          (cut : WithTop ℝ) < limitReplyClock menu reply →
          limitReplyValue limit menu
            (partialSignedLateMarginals marginals active cut hmasses parameters hparameters)
            who reward reply =
          partialSignedLateLimitMultiplier marginals who active cut parameters *
            limitReplyValue limit menu marginals who reward reply + constant := by
  classical
  obtain ⟨cuts, hmem, hcuts, _⟩ :=
    exists_chronological_signed_variation_of_mem_limit_endpoints source subsequence hE hcut
  refine ⟨cuts, hmem, hcuts, ?_⟩
  intro parameters hparameters who reward
  refine ⟨partialSignedLateLimitMultiplier_pos marginals who active cut
    hmasses parameters hparameters, ?_⟩
  by_cases hactive : active = ∅
  · subst active
    have hnew : partialSignedLateMarginals marginals ∅ cut hmasses parameters hparameters =
        marginals := by
      exact signedChronologicalMarginals_empty ..
    refine ⟨0, ?_⟩
    intro reply _
    rw [hnew]
    simp only [partialSignedLateLimitMultiplier, Finset.notMem_empty, ite_false,
      Finset.prod_const_one, one_mul, add_zero]
  obtain ⟨i, hi⟩ := Finset.nonempty_iff_ne_empty.mpr hactive
  have hcutOne := cut_lt_one_of_positive_limit_late_mass source subsequence i
    ((tendsto_pi_nhds.mp hlaws) i) (hmasses ⟨i, hi⟩)
  have hcutoff : ∀ᶠ k in atTop, cuts k ≤ (cutoff (source (subsequence k)) : ℝ) := by
    filter_upwards [hcuts.eventually (gt_mem_nhds hcutOne)] with k hk
    exact (endpoint_le_cutoff_or_eq_one (source (subsequence k)) (hmem k)).resolve_right
      (ne_of_lt hk)
  have hvalid : ∀ᶠ k in atTop, ∀ j : {j // j ∈ active},
      0 < (cellLaw (source (subsequence k)) j.val).probOf
          (cellCutEvent (source (subsequence k)) .after (cuts k)) ∧
        |parameters j.val| ≤ (cellLaw (source (subsequence k)) j.val).signedCondRadius
          (cellCutEvent (source (subsequence k)) .after (cuts k)) := by
    apply eventually_all.mpr
    intro j
    exact (eventually_signedCutCellLaw_valid source subsequence cuts hmem hcuts .after j.val
      ((tendsto_pi_nhds.mp hlaws) j.val) (hmasses j)).mono
      (fun k hk => hk (parameters j.val) (hparameters j))
  let replacement (k : ℕ) :=
    partialSignedLateCellLaw (source (subsequence k)) active (cuts k) parameters
  let changed := partialSignedLateMarginals marginals active cut hmasses parameters hparameters
  let original (k : ℕ) (choice : Option ℕ) :=
    (FinDist.pi (fun j : {j : ι // j ≠ who} => cellLaw (source (subsequence k)) j.val)).expect
      (upperCellReplyPayoff (source (subsequence k)) who choice reward)
  let modified (k : ℕ) (choice : Option ℕ) :=
    (FinDist.pi (fun j : {j : ι // j ≠ who} => replacement k j.val)).expect
      (upperCellReplyPayoff (source (subsequence k)) who choice reward)
  have hweights : ∀ᶠ k in atTop, ∀ j cell,
      (replacement k j).prob cell ≤
        (lateSignedBound j : ℝ) * weight (source (subsequence k)) cell := by
    apply Eventually.of_forall
    intro k j cell
    dsimp only [replacement]
    rw [partialSignedLateCellLaw_eq_chronological]
    exact prob_signedChronologicalReplacement_le source subsequence active (fun _ => .after)
      (fun _ => cuts) (fun j => parameters j.1) k j cell
  have hchanged : Tendsto (fun k j => referenceLaw (source (subsequence k)) (replacement k j))
      atTop (𝓝 changed) := by
    simpa only [replacement, changed, partialSignedLateCellLaw_eq_chronological,
      partialSignedLateMarginals] using
      tendsto_referenceLaw_signedChronologicalReplacement source subsequence hlaws
        active (fun _ => .after) (fun _ => cut) (fun _ => cuts)
        (fun _ => hmem) (fun _ => hcuts) hmasses (fun j => parameters j.1) hparameters
  have hfactor := tendsto_partialSignedLateResponseMultiplier source subsequence hlaws
    cuts hmem hcuts who active hmasses parameters
  have hnewNever : Tendsto (fun k => modified k none) atTop
      (𝓝 (responseValue limit changed who reward ⊤)) := by
    simpa only [modified, expect_upperCellReplyPayoff, expect_referenceCellReplyPayoff,
      id_eq, responseValue] using
      tendsto_reference_never_reply_expect (fun k => source (subsequence k)) replacement id
        hE hc lateSignedBound hweights hchanged who reward
  have holdNever : Tendsto (fun k => original k none) atTop
      (𝓝 (responseValue limit marginals who reward ⊤)) := by
    simpa only [original, expect_upperCellReplyPayoff, expect_referenceCellReplyPayoff,
      referenceOriginalLaw_cellLaw, responseValue] using
      tendsto_source_never_reply_expect source subsequence hE hc hlaws who reward
  let factor := partialSignedLateLimitMultiplier marginals who active cut parameters
  refine ⟨responseValue limit changed who reward ⊤ -
    factor * responseValue limit marginals who reward ⊤, ?_⟩
  intro reply hupper
  rcases reply with t | _
  · have ht : cut < (t : ℝ) := WithTop.coe_lt_coe.mp hupper
    obtain ⟨dates, _, hdates⟩ := exists_legal_reply_dates_tendsto source subsequence hT t.property
    have hnew : Tendsto (fun k => modified k (some (dates k))) atTop
        (𝓝 (responseValue limit changed who reward (t : WithTop ℝ))) := by
      simpa only [modified, expect_upperCellReplyPayoff, expect_referenceCellReplyPayoff,
        id_eq, responseValue] using
        tendsto_reference_finite_reply_expect (fun k => source (subsequence k)) replacement id
          hE hc lateSignedBound hweights hchanged who reward dates hdates
    have hold : Tendsto (fun k => original k (some (dates k))) atTop
        (𝓝 (responseValue limit marginals who reward (t : WithTop ℝ))) := by
      simpa only [original, expect_upperCellReplyPayoff, expect_referenceCellReplyPayoff,
        referenceOriginalLaw_cellLaw, responseValue] using
        tendsto_source_finite_reply_expect source subsequence hE hc hlaws who reward dates hdates
    have hidentity : ∀ᶠ k in atTop,
        modified k (some (dates k)) - modified k none =
          partialSignedLateResponseMultiplier (source (subsequence k)) who active (cuts k)
            parameters * (original k (some (dates k)) - original k none) := by
      filter_upwards [hcutoff, hvalid, hcuts.eventually_lt hdates ht] with k hk hv hu
      have hfirst : (cuts k : WithTop ℝ) ≤
          markedClock (source (subsequence k)) (quittingStoppingTimeValue (some (dates k))) := by
        change (cuts k : WithTop ℝ) ≤ (mark (source (subsequence k)) (dates k) : WithTop ℝ)
        exact WithTop.coe_le_coe.mpr hu.le
      have hnever : (cuts k : WithTop ℝ) ≤
          markedClock (source (subsequence k)) (quittingStoppingTimeValue none) := by
        simp only [quittingStoppingTimeValue, markedClock, WithTop.map_top, le_top]
      exact expect_partialSignedLate_upperCellReplyPayoff_sub (source (subsequence k))
        who active (cuts k) (hmem k) hk parameters
        (fun j hj => (hv ⟨j.val, hj⟩).1) (fun j hj => (hv ⟨j.val, hj⟩).2)
        (some (dates k)) none hfirst hnever reward
    have heq := tendsto_nhds_unique (hnew.sub hnewNever)
      ((hfactor.mul (hold.sub holdNever)).congr'
        (hidentity.mono fun _ h => h.symm))
    change responseValue limit changed who reward (t : WithTop ℝ) =
      factor * responseValue limit marginals who reward (t : WithTop ℝ) + _
    change responseValue limit changed who reward (t : WithTop ℝ) -
        responseValue limit changed who reward ⊤ =
      factor * (responseValue limit marginals who reward (t : WithTop ℝ) -
        responseValue limit marginals who reward ⊤) at heq
    linarith
  · change responseValue limit changed who reward ⊤ =
      factor * responseValue limit marginals who reward ⊤ + _
    ring

end GameTheory.MarkedCalendarChart
