import Research.MarkedCalendar.ChronologicalCellSemanticVariation
import Research.MarkedCalendar.ChronologicalCellSemanticConditioning
import MathUE.Probability.BooleanEndpointExpectation

/-! # Actual chronological payoff interpolation

Original laws and ordinary whole-cell conditionals form one Boolean endpoint
family on the same old charts and cut selectors. Actual legal signed laws have
the corresponding Boolean expectation at finite source indices eventually,
and hence at the marked limit. Inactive coordinates admit arbitrary weights.
The final facade produces all old-endpoint selectors before weights and tests.

The identities concern prescribed payoff and selected finite or Never replies.
They do not identify full caps, minima, or the safe signed constructor at one.
The all-one algebraic value is the ordinary endpoint's selected payoff only.
-/

noncomputable section

open Set Filter MeasureTheory TopologicalSpace GameTheory.Math.Probability
open scoped Topology BigOperators

namespace GameTheory.MarkedCalendarChart

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]

/-- Boolean endpoints use actual ordinary conditioning, independently of signed parameters. -/
def chronologicalEndpointReplacement (source : ℕ → ι → FinDist (Option ℕ))
    (subsequence : ℕ → ℕ) (active : Finset ι)
    (sides : {i // i ∈ active} → ChronologicalSide)
    (cuts : {i // i ∈ active} → ℕ → ℝ) (vertex : ι → Bool) (k : ℕ) (i : ι) :
    FinDist (Cell (source (subsequence k))) :=
  if vertex i then conditionalChronologicalReplacement source subsequence active sides cuts k i
  else cellLaw (source (subsequence k)) i

def chronologicalEndpointMarginals (marginals : ι → ProbabilityMeasure unitInterval)
    (active : Finset ι) (sides : {i // i ∈ active} → ChronologicalSide)
    (limitCuts : {i // i ∈ active} → ℝ)
    (hmasses : ∀ i, 0 < (marginals i.1 : Measure unitInterval).real
      (rawCutEvent (sides i) (limitCuts i))) (vertex : ι → Bool) (i : ι) :
    ProbabilityMeasure unitInterval :=
  if vertex i then conditionalChronologicalMarginals marginals active sides limitCuts hmasses i
  else marginals i

private def chronologicalEndpointBound (marginals : ι → ProbabilityMeasure unitInterval)
    (active : Finset ι) (sides : {i // i ∈ active} → ChronologicalSide)
    (limitCuts : {i // i ∈ active} → ℝ)
    (hmasses : ∀ i, 0 < (marginals i.1 : Measure unitInterval).real
      (rawCutEvent (sides i) (limitCuts i))) (i : ι) : NNReal :=
  max (Fintype.card ι) (conditionalChronologicalEnvelope marginals active sides limitCuts hmasses i)

private theorem eventually_chronological_affine
    (source : ℕ → ι → FinDist (Option ℕ)) (subsequence : ℕ → ℕ)
    {marginals : ι → ProbabilityMeasure unitInterval}
    (hlaws : Tendsto (fun k => chartLaw (source (subsequence k))) atTop (𝓝 marginals))
    (active : Finset ι) (sides : {i // i ∈ active} → ChronologicalSide)
    (limitCuts : {i // i ∈ active} → ℝ) (cuts : {i // i ∈ active} → ℕ → ℝ)
    (hmem : ∀ i k, cuts i k ∈ (calendar (source (subsequence k))).endpoints)
    (hcuts : ∀ i, Tendsto (cuts i) atTop (𝓝 (limitCuts i)))
    (hmasses : ∀ i, 0 < (marginals i.1 : Measure unitInterval).real
      (rawCutEvent (sides i) (limitCuts i)))
    (parameters : ι → ℝ)
    (hparameters : ∀ i : {i // i ∈ active}, |parameters i.1| ≤
      cutSignedRadius (marginals i.1) (sides i) (limitCuts i)) :
    ∀ᶠ k in atTop, ∀ i cell,
      (signedChronologicalReplacement source subsequence active sides cuts
        (fun i => parameters i.1) k i).prob cell =
      (1 - parameters i) * (chronologicalEndpointReplacement source subsequence active sides
        cuts (fun _ => false) k i).prob cell +
      parameters i * (chronologicalEndpointReplacement source subsequence active sides
        cuts (fun _ => true) k i).prob cell := by
  apply eventually_all.mpr
  intro i
  by_cases hi : i ∈ active
  · have hvalid := eventually_signedCutCellLaw_valid source subsequence (cuts ⟨i, hi⟩)
      (hmem ⟨i, hi⟩) (hcuts ⟨i, hi⟩) (sides ⟨i, hi⟩) i
      ((tendsto_pi_nhds.mp hlaws) i) (hmasses ⟨i, hi⟩)
    filter_upwards [hvalid] with k hk
    intro cell
    obtain ⟨hpositive, hlegal⟩ := hk (parameters i) (hparameters ⟨i, hi⟩)
    simp only [signedChronologicalReplacement, chronologicalEndpointReplacement,
      conditionalChronologicalReplacement, dite_eq_left hi, Bool.false_eq_true, ite_false,
      ite_true, signedCutCellLaw, conditionalCutCellLaw]
    rw [FinDist.signedCondOrSelf_eq_signedCond _ _ hpositive _ hlegal,
      conditionalCellLaw, dite_eq_left hpositive]
    exact FinDist.prob_signedCond_eq_affine ..
  · exact Eventually.of_forall fun k cell => by
      simp only [signedChronologicalReplacement, chronologicalEndpointReplacement,
        conditionalChronologicalReplacement, dite_eq_right hi, Bool.false_eq_true,
        ite_false, ite_true]
      ring

/-- Actual source laws, not algebraically signed distributions, satisfy the finite identity. -/
theorem eventually_expect_signedChronologicalReplacement_eq_booleanEndpointInterpolant
    (source : ℕ → ι → FinDist (Option ℕ)) (subsequence : ℕ → ℕ)
    {marginals : ι → ProbabilityMeasure unitInterval}
    (hlaws : Tendsto (fun k => chartLaw (source (subsequence k))) atTop (𝓝 marginals))
    (active : Finset ι) (sides : {i // i ∈ active} → ChronologicalSide)
    (limitCuts : {i // i ∈ active} → ℝ) (cuts : {i // i ∈ active} → ℕ → ℝ)
    (hmem : ∀ i k, cuts i k ∈ (calendar (source (subsequence k))).endpoints)
    (hcuts : ∀ i, Tendsto (cuts i) atTop (𝓝 (limitCuts i)))
    (hmasses : ∀ i, 0 < (marginals i.1 : Measure unitInterval).real
      (rawCutEvent (sides i) (limitCuts i)))
    (parameters : ι → ℝ)
    (hparameters : ∀ i : {i // i ∈ active}, |parameters i.1| ≤
      cutSignedRadius (marginals i.1) (sides i) (limitCuts i)) :
    ∀ᶠ k in atTop, ∀ test : (ι → Cell (source (subsequence k))) → ℝ,
      (FinDist.pi (signedChronologicalReplacement source subsequence active sides cuts
        (fun i => parameters i.1) k)).expect test =
      _root_.Math.booleanEndpointInterpolant (fun vertex =>
        (FinDist.pi (chronologicalEndpointReplacement source subsequence active sides cuts
          vertex k)).expect test) parameters := by
  filter_upwards [eventually_chronological_affine source subsequence hlaws active sides
    limitCuts cuts hmem hcuts hmasses parameters hparameters] with k hk
  intro test
  apply FinDist.expect_pi_eq_booleanEndpointInterpolant_of_affine_prob
    (endpoints := fun i bit => chronologicalEndpointReplacement source subsequence active sides
      cuts (fun _ => bit) k i)
  exact hk

private theorem tendsto_chronologicalEndpointMarginals
    (source : ℕ → ι → FinDist (Option ℕ)) (subsequence : ℕ → ℕ)
    {marginals : ι → ProbabilityMeasure unitInterval}
    (hlaws : Tendsto (fun k => chartLaw (source (subsequence k))) atTop (𝓝 marginals))
    (active : Finset ι) (sides : {i // i ∈ active} → ChronologicalSide)
    (limitCuts : {i // i ∈ active} → ℝ) (cuts : {i // i ∈ active} → ℕ → ℝ)
    (hmem : ∀ i k, cuts i k ∈ (calendar (source (subsequence k))).endpoints)
    (hcuts : ∀ i, Tendsto (cuts i) atTop (𝓝 (limitCuts i)))
    (hmasses : ∀ i, 0 < (marginals i.1 : Measure unitInterval).real
      (rawCutEvent (sides i) (limitCuts i))) (vertex : ι → Bool) :
    Tendsto (fun k i => referenceLaw (source (subsequence k))
      (chronologicalEndpointReplacement source subsequence active sides cuts vertex k i))
      atTop (𝓝 (chronologicalEndpointMarginals marginals active sides limitCuts
        hmasses vertex)) := by
  have hconditional := tendsto_referenceLaw_conditionalChronologicalReplacement source subsequence
    hlaws active sides limitCuts cuts hmem hcuts hmasses
  apply tendsto_pi_nhds.mpr
  intro i
  cases hv : vertex i
  · simpa only [chronologicalEndpointReplacement, chronologicalEndpointMarginals,
      hv, Bool.false_eq_true, ite_false, chartLaw] using (tendsto_pi_nhds.mp hlaws) i
  · simpa only [chronologicalEndpointReplacement, chronologicalEndpointMarginals,
      hv, ite_true] using (tendsto_pi_nhds.mp hconditional) i

private theorem eventually_chronologicalEndpoint_weights
    (source : ℕ → ι → FinDist (Option ℕ)) (subsequence : ℕ → ℕ)
    {marginals : ι → ProbabilityMeasure unitInterval}
    (hlaws : Tendsto (fun k => chartLaw (source (subsequence k))) atTop (𝓝 marginals))
    (active : Finset ι) (sides : {i // i ∈ active} → ChronologicalSide)
    (limitCuts : {i // i ∈ active} → ℝ) (cuts : {i // i ∈ active} → ℕ → ℝ)
    (hmem : ∀ i k, cuts i k ∈ (calendar (source (subsequence k))).endpoints)
    (hcuts : ∀ i, Tendsto (cuts i) atTop (𝓝 (limitCuts i)))
    (hmasses : ∀ i, 0 < (marginals i.1 : Measure unitInterval).real
      (rawCutEvent (sides i) (limitCuts i))) :
    ∀ᶠ k in atTop, ∀ vertex i cell,
      (chronologicalEndpointReplacement source subsequence active sides cuts vertex k i).prob cell ≤
        (chronologicalEndpointBound marginals active sides limitCuts hmasses i : ℝ) *
          weight (source (subsequence k)) cell := by
  filter_upwards [eventually_conditionalChronologicalReplacement_le source subsequence hlaws
    active sides limitCuts cuts hmem hcuts hmasses] with k hk
  intro vertex i cell
  have hnonneg := (weight_pos (source (subsequence k)) cell).le
  have hbound :
      (chronologicalEndpointBound marginals active sides limitCuts hmasses i : ℝ) =
        max (Fintype.card ι : ℝ)
          (conditionalChronologicalEnvelope marginals active sides limitCuts hmasses i : ℝ) := by
    simp [chronologicalEndpointBound]
  rw [hbound]
  cases hv : vertex i
  · simp only [chronologicalEndpointReplacement, hv, Bool.false_eq_true, ite_false, cellLaw_prob]
    exact (ownWeight_le _ i cell).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) hnonneg)
  · simp only [chronologicalEndpointReplacement, hv, ite_true]
    exact (hk i cell).trans (mul_le_mul_of_nonneg_right (le_max_right _ _) hnonneg)

private def chronologicalSignedBound : ι → NNReal :=
  fun _ => ⟨(3 / 2 : ℝ) * Fintype.card ι, by positivity⟩

/-- Prescribed payoff uses the same actual ordinary Boolean endpoint family. -/
theorem signedChronological_payoff_eq_booleanEndpointInterpolant
    (source : ℕ → ι → FinDist (Option ℕ)) (subsequence : ℕ → ℕ)
    {limit : MathUE.MarkedCalendar.Calendar}
    {marginals : ι → ProbabilityMeasure unitInterval}
    (hE : Tendsto (fun k => (calendar (source (subsequence k))).endpoints) atTop
      (𝓝 limit.endpoints))
    (hc : Tendsto (fun k => cutoff (source (subsequence k))) atTop (𝓝 limit.cutoff))
    (hlaws : Tendsto (fun k => chartLaw (source (subsequence k))) atTop (𝓝 marginals))
    (active : Finset ι) (sides : {i // i ∈ active} → ChronologicalSide)
    (limitCuts : {i // i ∈ active} → ℝ) (cuts : {i // i ∈ active} → ℕ → ℝ)
    (hmem : ∀ i k, cuts i k ∈ (calendar (source (subsequence k))).endpoints)
    (hcuts : ∀ i, Tendsto (cuts i) atTop (𝓝 (limitCuts i)))
    (hmasses : ∀ i, 0 < (marginals i.1 : Measure unitInterval).real
      (rawCutEvent (sides i) (limitCuts i)))
    (parameters : ι → ℝ)
    (hparameters : ∀ i : {i // i ∈ active}, |parameters i.1| ≤
      cutSignedRadius (marginals i.1) (sides i) (limitCuts i))
    (reward : Finset ι → ℝ) :
    (∫ sample, MathUE.MarkedCalendar.payoffKernel limit reward sample
      ∂(ProbabilityMeasure.pi (signedChronologicalMarginals marginals active sides limitCuts
        hmasses (fun i => parameters i.1) hparameters) : Measure (ι → unitInterval))) =
      _root_.Math.booleanEndpointInterpolant (fun vertex =>
        ∫ sample, MathUE.MarkedCalendar.payoffKernel limit reward sample
          ∂(ProbabilityMeasure.pi
            (chronologicalEndpointMarginals marginals active sides limitCuts hmasses vertex) :
              Measure (ι → unitInterval))) parameters := by
  let replacement := signedChronologicalReplacement source subsequence active sides cuts
    (fun i => parameters i.1)
  have hfinite := eventually_expect_signedChronologicalReplacement_eq_booleanEndpointInterpolant
    source subsequence hlaws active sides limitCuts cuts hmem hcuts hmasses parameters hparameters
  have hweights : ∀ᶠ k in atTop, ∀ i cell,
      (replacement k i).prob cell ≤
        (chronologicalSignedBound i : ℝ) * weight (source (subsequence k)) cell :=
    Eventually.of_forall fun k i cell =>
      prob_signedChronologicalReplacement_le source subsequence active sides cuts
        (fun i => parameters i.1) k i cell
  have hlaw := tendsto_referenceLaw_signedChronologicalReplacement source subsequence hlaws
    active sides limitCuts cuts hmem hcuts hmasses (fun i => parameters i.1) hparameters
  have hvalue := tendsto_reference_outcome_expect (fun k => source (subsequence k)) replacement id
    hE hc chronologicalSignedBound hweights hlaw reward
  refine _root_.Math.eq_booleanEndpointInterpolant_of_tendsto parameters _ (fun k vertex =>
    ((FinDist.pi (fun i => referenceOriginalLaw (source (subsequence k))
      (chronologicalEndpointReplacement source subsequence active sides cuts vertex k i))).map
        quittingFirstStoppingOutcome).expect
      (fun outcome => reward (outcomeLabelsEquiv outcome))) _ _ ?_ hvalue ?_
  · filter_upwards [hfinite] with k hk
    simpa only [replacement, id_eq, expect_referenceCellPayoff] using
      hk (referenceCellPayoff (source (subsequence k)) reward)
  · intro vertex
    exact tendsto_reference_outcome_expect (fun k => source (subsequence k))
      (chronologicalEndpointReplacement source subsequence active sides cuts vertex) id hE hc
      (chronologicalEndpointBound marginals active sides limitCuts hmasses)
      ((eventually_chronologicalEndpoint_weights source subsequence hlaws active sides
        limitCuts cuts hmem hcuts hmasses).mono fun k hk => hk vertex)
      (tendsto_chronologicalEndpointMarginals source subsequence hlaws active sides
        limitCuts cuts hmem hcuts hmasses vertex) reward

/-- Every selected moving finite reply has the ordinary endpoint interpolation.
This does not identify the full cap. -/
theorem signedChronological_finite_reply_eq_booleanEndpointInterpolant
    (source : ℕ → ι → FinDist (Option ℕ)) (subsequence : ℕ → ℕ)
    {limit : MathUE.MarkedCalendar.Calendar}
    {marginals : ι → ProbabilityMeasure unitInterval}
    (hE : Tendsto (fun k => (calendar (source (subsequence k))).endpoints) atTop
      (𝓝 limit.endpoints))
    (hc : Tendsto (fun k => cutoff (source (subsequence k))) atTop (𝓝 limit.cutoff))
    (hlaws : Tendsto (fun k => chartLaw (source (subsequence k))) atTop (𝓝 marginals))
    (active : Finset ι) (sides : {i // i ∈ active} → ChronologicalSide)
    (limitCuts : {i // i ∈ active} → ℝ) (cuts : {i // i ∈ active} → ℕ → ℝ)
    (hmem : ∀ i k, cuts i k ∈ (calendar (source (subsequence k))).endpoints)
    (hcuts : ∀ i, Tendsto (cuts i) atTop (𝓝 (limitCuts i)))
    (hmasses : ∀ i, 0 < (marginals i.1 : Measure unitInterval).real
      (rawCutEvent (sides i) (limitCuts i)))
    (parameters : ι → ℝ)
    (hparameters : ∀ i : {i // i ∈ active}, |parameters i.1| ≤
      cutSignedRadius (marginals i.1) (sides i) (limitCuts i))
    (who : ι) (reward : Finset ι → ℝ) (dates : ℕ → ℕ) {t : ℝ}
    (ht : Tendsto (fun k => mark (source (subsequence k)) (dates k)) atTop (𝓝 t)) :
    (∫ sample, MathUE.MarkedCalendar.responsePayoffKernel limit who (t : WithTop ℝ)
      reward sample ∂(ProbabilityMeasure.pi (fun j : {j : ι // j ≠ who} =>
        signedChronologicalMarginals marginals active sides limitCuts hmasses
          (fun i => parameters i.1) hparameters j.1) :
            Measure ({j : ι // j ≠ who} → unitInterval))) =
      _root_.Math.booleanEndpointInterpolant (fun vertex =>
        ∫ sample, MathUE.MarkedCalendar.responsePayoffKernel limit who (t : WithTop ℝ)
          reward sample ∂(ProbabilityMeasure.pi (fun j : {j : ι // j ≠ who} =>
            chronologicalEndpointMarginals marginals active sides limitCuts hmasses vertex j.1) :
              Measure ({j : ι // j ≠ who} → unitInterval))) parameters := by
  let replacement := signedChronologicalReplacement source subsequence active sides cuts
    (fun i => parameters i.1)
  have hfinite := eventually_expect_signedChronologicalReplacement_eq_booleanEndpointInterpolant
    source subsequence hlaws active sides limitCuts cuts hmem hcuts hmasses parameters hparameters
  have hweights : ∀ᶠ k in atTop, ∀ i cell,
      (replacement k i).prob cell ≤
        (chronologicalSignedBound i : ℝ) * weight (source (subsequence k)) cell :=
    Eventually.of_forall fun k i cell =>
      prob_signedChronologicalReplacement_le source subsequence active sides cuts
        (fun i => parameters i.1) k i cell
  have hlaw := tendsto_referenceLaw_signedChronologicalReplacement source subsequence hlaws
    active sides limitCuts cuts hmem hcuts hmasses (fun i => parameters i.1) hparameters
  have hvalue := tendsto_reference_finite_reply_expect
    (fun k => source (subsequence k)) replacement id
    hE hc chronologicalSignedBound hweights hlaw who reward dates ht
  refine _root_.Math.eq_booleanEndpointInterpolant_of_tendsto parameters _ (fun k vertex =>
    ((FinDist.pi (Function.update (fun i => referenceOriginalLaw (source (subsequence k))
      (chronologicalEndpointReplacement source subsequence active sides cuts vertex k i))
        who (FinDist.pure (some (dates k))))).map quittingFirstStoppingOutcome).expect
      (fun outcome => reward (outcomeLabelsEquiv outcome))) _ _ ?_ hvalue ?_
  · filter_upwards [hfinite] with k hk
    simpa only [replacement, id_eq, expect_referenceCellReplyPayoff] using
      hk (referenceCellReplyPayoff (source (subsequence k)) who (some (dates k)) reward)
  · intro vertex
    exact tendsto_reference_finite_reply_expect (fun k => source (subsequence k))
      (chronologicalEndpointReplacement source subsequence active sides cuts vertex) id hE hc
      (chronologicalEndpointBound marginals active sides limitCuts hmasses)
      ((eventually_chronologicalEndpoint_weights source subsequence hlaws active sides
        limitCuts cuts hmem hcuts hmasses).mono fun k hk => hk vertex)
      (tendsto_chronologicalEndpointMarginals source subsequence hlaws active sides
        limitCuts cuts hmem hcuts hmasses vertex) who reward dates ht

/-- Literal Never has the same endpoint coefficients and remains distinct from the finite cutoff. -/
theorem signedChronological_never_reply_eq_booleanEndpointInterpolant
    (source : ℕ → ι → FinDist (Option ℕ)) (subsequence : ℕ → ℕ)
    {limit : MathUE.MarkedCalendar.Calendar}
    {marginals : ι → ProbabilityMeasure unitInterval}
    (hE : Tendsto (fun k => (calendar (source (subsequence k))).endpoints) atTop
      (𝓝 limit.endpoints))
    (hc : Tendsto (fun k => cutoff (source (subsequence k))) atTop (𝓝 limit.cutoff))
    (hlaws : Tendsto (fun k => chartLaw (source (subsequence k))) atTop (𝓝 marginals))
    (active : Finset ι) (sides : {i // i ∈ active} → ChronologicalSide)
    (limitCuts : {i // i ∈ active} → ℝ) (cuts : {i // i ∈ active} → ℕ → ℝ)
    (hmem : ∀ i k, cuts i k ∈ (calendar (source (subsequence k))).endpoints)
    (hcuts : ∀ i, Tendsto (cuts i) atTop (𝓝 (limitCuts i)))
    (hmasses : ∀ i, 0 < (marginals i.1 : Measure unitInterval).real
      (rawCutEvent (sides i) (limitCuts i)))
    (parameters : ι → ℝ)
    (hparameters : ∀ i : {i // i ∈ active}, |parameters i.1| ≤
      cutSignedRadius (marginals i.1) (sides i) (limitCuts i))
    (who : ι) (reward : Finset ι → ℝ) :
    (∫ sample, MathUE.MarkedCalendar.responsePayoffKernel limit who ⊤
      reward sample ∂(ProbabilityMeasure.pi (fun j : {j : ι // j ≠ who} =>
        signedChronologicalMarginals marginals active sides limitCuts hmasses
          (fun i => parameters i.1) hparameters j.1) :
            Measure ({j : ι // j ≠ who} → unitInterval))) =
      _root_.Math.booleanEndpointInterpolant (fun vertex =>
        ∫ sample, MathUE.MarkedCalendar.responsePayoffKernel limit who ⊤
          reward sample ∂(ProbabilityMeasure.pi (fun j : {j : ι // j ≠ who} =>
            chronologicalEndpointMarginals marginals active sides limitCuts hmasses vertex j.1) :
              Measure ({j : ι // j ≠ who} → unitInterval))) parameters := by
  let replacement := signedChronologicalReplacement source subsequence active sides cuts
    (fun i => parameters i.1)
  have hfinite := eventually_expect_signedChronologicalReplacement_eq_booleanEndpointInterpolant
    source subsequence hlaws active sides limitCuts cuts hmem hcuts hmasses parameters hparameters
  have hweights : ∀ᶠ k in atTop, ∀ i cell,
      (replacement k i).prob cell ≤
        (chronologicalSignedBound i : ℝ) * weight (source (subsequence k)) cell :=
    Eventually.of_forall fun k i cell =>
      prob_signedChronologicalReplacement_le source subsequence active sides cuts
        (fun i => parameters i.1) k i cell
  have hlaw := tendsto_referenceLaw_signedChronologicalReplacement source subsequence hlaws
    active sides limitCuts cuts hmem hcuts hmasses (fun i => parameters i.1) hparameters
  have hvalue := tendsto_reference_never_reply_expect
    (fun k => source (subsequence k)) replacement id
    hE hc chronologicalSignedBound hweights hlaw who reward
  refine _root_.Math.eq_booleanEndpointInterpolant_of_tendsto parameters _ (fun k vertex =>
    ((FinDist.pi (Function.update (fun i => referenceOriginalLaw (source (subsequence k))
      (chronologicalEndpointReplacement source subsequence active sides cuts vertex k i))
        who (FinDist.pure none))).map quittingFirstStoppingOutcome).expect
      (fun outcome => reward (outcomeLabelsEquiv outcome))) _ _ ?_ hvalue ?_
  · filter_upwards [hfinite] with k hk
    simpa only [replacement, id_eq, expect_referenceCellReplyPayoff] using
      hk (referenceCellReplyPayoff (source (subsequence k)) who none reward)
  · intro vertex
    exact tendsto_reference_never_reply_expect (fun k => source (subsequence k))
      (chronologicalEndpointReplacement source subsequence active sides cuts vertex) id hE hc
      (chronologicalEndpointBound marginals active sides limitCuts hmasses)
      ((eventually_chronologicalEndpoint_weights source subsequence hlaws active sides
        limitCuts cuts hmem hcuts hmasses).mono fun k hk => hk vertex)
      (tendsto_chronologicalEndpointMarginals source subsequence hlaws active sides
        limitCuts cuts hmem hcuts hmasses vertex) who reward

/-- Actual limiting endpoints produce one source-faithful cut family before all legal
weights, all observables and rewards, and every selected finite or Never response.
No cut-convergence certificate is supplied and no new source subsequence is extracted. -/
theorem exists_chronological_payoff_interpolation
    (source : ℕ → ι → FinDist (Option ℕ)) (subsequence : ℕ → ℕ)
    {limit : MathUE.MarkedCalendar.Calendar}
    {marginals : ι → ProbabilityMeasure unitInterval}
    (hE : Tendsto (fun k => (calendar (source (subsequence k))).endpoints) atTop
      (𝓝 limit.endpoints))
    (hc : Tendsto (fun k => cutoff (source (subsequence k))) atTop (𝓝 limit.cutoff))
    (hlaws : Tendsto (fun k => chartLaw (source (subsequence k))) atTop (𝓝 marginals))
    (active : Finset ι) (sides : {i // i ∈ active} → ChronologicalSide)
    (limitCuts : {i // i ∈ active} → ℝ)
    (hendpoints : ∀ i, limitCuts i ∈ limit.endpoints)
    (hmasses : ∀ i, 0 < (marginals i.1 : Measure unitInterval).real
      (rawCutEvent (sides i) (limitCuts i))) :
    ∃ cuts : {i // i ∈ active} → ℕ → ℝ,
      (∀ i k, cuts i k ∈ (calendar (source (subsequence k))).endpoints) ∧
      (∀ i, Tendsto (cuts i) atTop (𝓝 (limitCuts i))) ∧
      (∀ i, 0 < cutSignedRadius (marginals i.1) (sides i) (limitCuts i)) ∧
      ∀ (parameters : ι → ℝ)
        (hparameters : ∀ i : {i // i ∈ active}, |parameters i.1| ≤
          cutSignedRadius (marginals i.1) (sides i) (limitCuts i)),
        (∀ᶠ k in atTop, ∀ test : (ι → Cell (source (subsequence k))) → ℝ,
          (FinDist.pi (signedChronologicalReplacement source subsequence active sides cuts
            (fun i => parameters i.1) k)).expect test =
          _root_.Math.booleanEndpointInterpolant (fun vertex =>
            (FinDist.pi (chronologicalEndpointReplacement source subsequence active sides cuts
              vertex k)).expect test) parameters) ∧
        ∀ reward : Finset ι → ℝ,
          (∫ sample, MathUE.MarkedCalendar.payoffKernel limit reward sample
            ∂(ProbabilityMeasure.pi (signedChronologicalMarginals marginals active sides limitCuts
              hmasses (fun i => parameters i.1) hparameters) : Measure (ι → unitInterval))) =
            _root_.Math.booleanEndpointInterpolant (fun vertex =>
              ∫ sample, MathUE.MarkedCalendar.payoffKernel limit reward sample
                ∂(ProbabilityMeasure.pi
                  (chronologicalEndpointMarginals marginals active sides limitCuts hmasses vertex) :
                    Measure (ι → unitInterval))) parameters ∧
          ∀ who : ι,
            (∫ sample, MathUE.MarkedCalendar.responsePayoffKernel limit who ⊤
              reward sample ∂(ProbabilityMeasure.pi (fun j : {j : ι // j ≠ who} =>
                signedChronologicalMarginals marginals active sides limitCuts hmasses
                  (fun i => parameters i.1) hparameters j.1) :
                    Measure ({j : ι // j ≠ who} → unitInterval))) =
              _root_.Math.booleanEndpointInterpolant (fun vertex =>
                ∫ sample, MathUE.MarkedCalendar.responsePayoffKernel limit who ⊤
                  reward sample ∂(ProbabilityMeasure.pi (fun j : {j : ι // j ≠ who} =>
                    chronologicalEndpointMarginals marginals active sides limitCuts
                      hmasses vertex j.1) :
                      Measure ({j : ι // j ≠ who} → unitInterval))) parameters ∧
            ∀ (dates : ℕ → ℕ) (t : ℝ),
              Tendsto (fun k => mark (source (subsequence k)) (dates k)) atTop (𝓝 t) →
              (∫ sample, MathUE.MarkedCalendar.responsePayoffKernel limit who (t : WithTop ℝ)
                reward sample ∂(ProbabilityMeasure.pi (fun j : {j : ι // j ≠ who} =>
                  signedChronologicalMarginals marginals active sides limitCuts hmasses
                    (fun i => parameters i.1) hparameters j.1) :
                      Measure ({j : ι // j ≠ who} → unitInterval))) =
                _root_.Math.booleanEndpointInterpolant (fun vertex =>
                  ∫ sample, MathUE.MarkedCalendar.responsePayoffKernel limit who (t : WithTop ℝ)
                    reward sample ∂(ProbabilityMeasure.pi (fun j : {j : ι // j ≠ who} =>
                      chronologicalEndpointMarginals marginals active sides limitCuts
                        hmasses vertex j.1) :
                        Measure ({j : ι // j ≠ who} → unitInterval))) parameters := by
  classical
  have hselect : ∀ i : {i // i ∈ active}, ∃ points : ℕ → ℝ,
      (∀ k, points k ∈ (calendar (source (subsequence k))).endpoints) ∧
        Tendsto points atTop (𝓝 (limitCuts i)) := by
    intro i
    obtain ⟨points, hpoints, htendsto, _⟩ :=
      exists_chronological_signed_variation_of_mem_limit_endpoints source subsequence
        hE (hendpoints i)
    exact ⟨points, hpoints, htendsto⟩
  choose cuts hmem hcuts using hselect
  refine ⟨cuts, hmem, hcuts, fun i =>
    cutSignedRadius_pos (marginals i.1) (sides i) (limitCuts i) (hmasses i), ?_⟩
  intro parameters hparameters
  refine ⟨eventually_expect_signedChronologicalReplacement_eq_booleanEndpointInterpolant
    source subsequence hlaws active sides limitCuts cuts hmem hcuts hmasses
    parameters hparameters, ?_⟩
  intro reward
  refine ⟨signedChronological_payoff_eq_booleanEndpointInterpolant source subsequence
    hE hc hlaws active sides limitCuts cuts hmem hcuts hmasses parameters hparameters reward, ?_⟩
  intro who
  refine ⟨signedChronological_never_reply_eq_booleanEndpointInterpolant source subsequence
    hE hc hlaws active sides limitCuts cuts hmem hcuts hmasses parameters hparameters
    who reward, ?_⟩
  intro dates t ht
  exact signedChronological_finite_reply_eq_booleanEndpointInterpolant source subsequence
    hE hc hlaws active sides limitCuts cuts hmem hcuts hmasses parameters hparameters
    who reward dates ht

end GameTheory.MarkedCalendarChart
