import Research.MarkedCalendar.ChronologicalCellConditioning
import Research.MarkedCalendar.FiniteLawSemanticMinimum

/-! # Partial ordinary chronological conditioning in the original carrier

One old-endpoint sequence for each active owner is chosen before every reward.
The actual whole-cell conditional is used when its finite event has positive
mass; the original finite law is retained at exceptional zero-mass indices.
Positive limiting raw-event mass is required only for active owners.

The ordinary conditional weak limits and eventual two-over-mass envelopes are
derived on the supplied source subsequence. They yield original unrestricted
payoff/full-cap convergence, carrier membership, and the canonical SUM floor.
Empty activity is the original family. This is ordinary conditioning, not an
evaluation of the safe signed family at parameter one, and no resulting pair
is asserted to minimize debt.
-/

noncomputable section

open Set Filter MeasureTheory TopologicalSpace GameTheory.Math.Probability
open scoped Topology

namespace GameTheory.MarkedCalendarChart

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]

def conditionalChronologicalReplacement (source : ℕ → ι → FinDist (Option ℕ))
    (subsequence : ℕ → ℕ) (active : Finset ι)
    (sides : {i // i ∈ active} → ChronologicalSide)
    (cuts : {i // i ∈ active} → ℕ → ℝ) (k : ℕ) (i : ι) :
    FinDist (Cell (source (subsequence k))) :=
  if hi : i ∈ active then conditionalCutCellLaw (source (subsequence k))
    (sides ⟨i, hi⟩) (cuts ⟨i, hi⟩ k) i
  else cellLaw (source (subsequence k)) i

def conditionalChronologicalMarginals (marginals : ι → ProbabilityMeasure unitInterval)
    (active : Finset ι) (sides : {i // i ∈ active} → ChronologicalSide)
    (cuts : {i // i ∈ active} → ℝ)
    (hmasses : ∀ i, 0 < (marginals i.1 : Measure unitInterval).real
      (rawCutEvent (sides i) (cuts i))) (i : ι) : ProbabilityMeasure unitInterval :=
  if hi : i ∈ active then cutConditionalLaw (marginals i) (sides ⟨i, hi⟩)
    (cuts ⟨i, hi⟩) (hmasses ⟨i, hi⟩)
  else marginals i

/-- The active coefficient is derived from the actual limiting event mass. -/
def conditionalChronologicalEnvelope (marginals : ι → ProbabilityMeasure unitInterval)
    (active : Finset ι) (sides : {i // i ∈ active} → ChronologicalSide)
    (cuts : {i // i ∈ active} → ℝ)
    (hmasses : ∀ i, 0 < (marginals i.1 : Measure unitInterval).real
      (rawCutEvent (sides i) (cuts i))) (i : ι) : NNReal :=
  if hi : i ∈ active then
    ⟨(2 / (marginals i : Measure unitInterval).real
      (rawCutEvent (sides ⟨i, hi⟩) (cuts ⟨i, hi⟩))) * Fintype.card ι,
      mul_nonneg (div_nonneg (by norm_num) (hmasses ⟨i, hi⟩).le) (Nat.cast_nonneg _)⟩
  else Fintype.card ι

theorem conditionalChronologicalReplacement_empty (source : ℕ → ι → FinDist (Option ℕ))
    (subsequence : ℕ → ℕ) (sides : {i // i ∈ (∅ : Finset ι)} → ChronologicalSide)
    (cuts : {i // i ∈ (∅ : Finset ι)} → ℕ → ℝ) :
    conditionalChronologicalReplacement source subsequence ∅ sides cuts =
      fun k => cellLaw (source (subsequence k)) := by
  funext k i
  simp only [conditionalChronologicalReplacement, Finset.notMem_empty, dite_false]

omit [Fintype ι] [Nonempty ι] in
theorem conditionalChronologicalMarginals_empty
    (marginals : ι → ProbabilityMeasure unitInterval)
    (sides : {i // i ∈ (∅ : Finset ι)} → ChronologicalSide)
    (cuts : {i // i ∈ (∅ : Finset ι)} → ℝ)
    (hmasses : ∀ i, 0 < (marginals i.1 : Measure unitInterval).real
      (rawCutEvent (sides i) (cuts i))) :
    conditionalChronologicalMarginals marginals ∅ sides cuts hmasses = marginals := by
  funext i
  simp only [conditionalChronologicalMarginals, Finset.notMem_empty, dite_false]

/-- Finite many owners share one eventual reference bound, including zero-mass fallback indices. -/
theorem eventually_conditionalChronologicalReplacement_le
    (source : ℕ → ι → FinDist (Option ℕ)) (subsequence : ℕ → ℕ)
    {marginals : ι → ProbabilityMeasure unitInterval}
    (hlaws : Tendsto (fun k => chartLaw (source (subsequence k))) atTop (𝓝 marginals))
    (active : Finset ι) (sides : {i // i ∈ active} → ChronologicalSide)
    (limitCuts : {i // i ∈ active} → ℝ) (cuts : {i // i ∈ active} → ℕ → ℝ)
    (hmem : ∀ i k, cuts i k ∈ (calendar (source (subsequence k))).endpoints)
    (hcuts : ∀ i, Tendsto (cuts i) atTop (𝓝 (limitCuts i)))
    (hmasses : ∀ i, 0 < (marginals i.1 : Measure unitInterval).real
      (rawCutEvent (sides i) (limitCuts i))) :
    ∀ᶠ k in atTop, ∀ i (cell : Cell (source (subsequence k))),
      (conditionalChronologicalReplacement source subsequence active sides cuts k i).prob cell ≤
        (conditionalChronologicalEnvelope marginals active sides limitCuts hmasses i : ℝ) *
          weight (source (subsequence k)) cell := by
  apply eventually_all.mpr
  intro i
  by_cases hi : i ∈ active
  · have h := eventually_conditionalCutCellLaw_le source subsequence (cuts ⟨i, hi⟩)
      (hmem ⟨i, hi⟩) (hcuts ⟨i, hi⟩) (sides ⟨i, hi⟩) i
      ((tendsto_pi_nhds.mp hlaws) i) (hmasses ⟨i, hi⟩)
    have hbound :
        (conditionalChronologicalEnvelope marginals active sides limitCuts hmasses i : ℝ) =
          (2 / (marginals i : Measure unitInterval).real
            (rawCutEvent (sides ⟨i, hi⟩) (limitCuts ⟨i, hi⟩))) * Fintype.card ι := by
      simp [conditionalChronologicalEnvelope, hi]
      rfl
    rw [hbound]
    simpa only [conditionalChronologicalReplacement, dite_eq_left hi] using h
  · have hbound :
        (conditionalChronologicalEnvelope marginals active sides limitCuts hmasses i : ℝ) =
          Fintype.card ι := by
      simp [conditionalChronologicalEnvelope, hi]
    rw [hbound]
    exact Eventually.of_forall fun k cell => by
      simpa only [conditionalChronologicalReplacement, dite_eq_right hi, cellLaw_prob] using
        ownWeight_le (source (subsequence k)) i cell

/-- Ordinary whole-cell conditioning converges to the actual raw-event conditionals. -/
theorem tendsto_referenceLaw_conditionalChronologicalReplacement
    (source : ℕ → ι → FinDist (Option ℕ)) (subsequence : ℕ → ℕ)
    {marginals : ι → ProbabilityMeasure unitInterval}
    (hlaws : Tendsto (fun k => chartLaw (source (subsequence k))) atTop (𝓝 marginals))
    (active : Finset ι) (sides : {i // i ∈ active} → ChronologicalSide)
    (limitCuts : {i // i ∈ active} → ℝ) (cuts : {i // i ∈ active} → ℕ → ℝ)
    (hmem : ∀ i k, cuts i k ∈ (calendar (source (subsequence k))).endpoints)
    (hcuts : ∀ i, Tendsto (cuts i) atTop (𝓝 (limitCuts i)))
    (hmasses : ∀ i, 0 < (marginals i.1 : Measure unitInterval).real
      (rawCutEvent (sides i) (limitCuts i))) :
    Tendsto (fun k i => referenceLaw (source (subsequence k))
      (conditionalChronologicalReplacement source subsequence active sides cuts k i))
      atTop (𝓝 (conditionalChronologicalMarginals marginals active sides limitCuts hmasses)) := by
  apply tendsto_pi_nhds.mpr
  intro i
  have hiLaw := (tendsto_pi_nhds.mp hlaws) i
  by_cases hi : i ∈ active
  · have h := tendsto_referenceLaw_conditionalCutCellLaw source subsequence (cuts ⟨i, hi⟩)
      (hmem ⟨i, hi⟩) (hcuts ⟨i, hi⟩) (sides ⟨i, hi⟩) i hiLaw (hmasses ⟨i, hi⟩)
    simpa only [conditionalChronologicalReplacement, conditionalChronologicalMarginals,
      dite_eq_left hi] using h
  · simpa only [conditionalChronologicalReplacement, conditionalChronologicalMarginals,
      dite_eq_right hi, chartLaw] using hiLaw

/-- Actual old endpoints determine a partial ordinary conditional family before every reward.
Its full original semantic limit lies in the carrier and is bounded below by the SUM infimum. -/
theorem exists_chronological_semantic_conditioning
    (source : ℕ → ι → FinDist (Option ℕ)) (subsequence : ℕ → ℕ)
    {limit : MathUE.MarkedCalendar.Calendar} {menu : NonemptyCompacts ℝ}
    {marginals : ι → ProbabilityMeasure unitInterval}
    (hE : Tendsto (fun k => (calendar (source (subsequence k))).endpoints) atTop
      (𝓝 limit.endpoints))
    (hc : Tendsto (fun k => cutoff (source (subsequence k))) atTop (𝓝 limit.cutoff))
    (hT : Tendsto (fun k => legalMenuCompacts (source (subsequence k))) atTop (𝓝 menu))
    (hlaws : Tendsto (fun k => chartLaw (source (subsequence k))) atTop (𝓝 marginals))
    (active : Finset ι) (sides : {i // i ∈ active} → ChronologicalSide)
    (limitCuts : {i // i ∈ active} → ℝ)
    (hendpoints : ∀ i, limitCuts i ∈ limit.endpoints)
    (hmasses : ∀ i, 0 < (marginals i.1 : Measure unitInterval).real
      (rawCutEvent (sides i) (limitCuts i))) :
    ∃ cuts : {i // i ∈ active} → ℕ → ℝ,
      (∀ i k, cuts i k ∈ (calendar (source (subsequence k))).endpoints) ∧
      (∀ i, Tendsto (cuts i) atTop (𝓝 (limitCuts i))) ∧
      (∀ᶠ k in atTop, ∀ i (cell : Cell (source (subsequence k))),
        (conditionalChronologicalReplacement source subsequence active sides cuts k i).prob cell ≤
          (conditionalChronologicalEnvelope marginals active sides limitCuts hmasses i : ℝ) *
            weight (source (subsequence k)) cell) ∧
      Tendsto (fun k i => referenceLaw (source (subsequence k))
        (conditionalChronologicalReplacement source subsequence active sides cuts k i))
        atTop (𝓝 (conditionalChronologicalMarginals marginals active sides limitCuts hmasses)) ∧
      ∀ reward : {S : Finset ι // S.Nonempty} → Payoff ι,
        Tendsto (fun k => quittingTerminalSemanticPair reward
          (quittingStoppingLawProfile reward (fun i =>
            (referenceOriginalLaw (source (subsequence k))
              (conditionalChronologicalReplacement source subsequence active sides
                cuts k i)).toPMF)))
          atTop (𝓝 (limitSemanticPair limit menu
            (conditionalChronologicalMarginals marginals active sides limitCuts hmasses) reward)) ∧
        limitSemanticPair limit menu
          (conditionalChronologicalMarginals marginals active sides limitCuts hmasses) reward ∈
            quittingTerminalSemanticCarrier reward ∧
        quittingTerminalDebtSumInf reward ≤ quittingTerminalSemanticDebtSum
          (limitSemanticPair limit menu
            (conditionalChronologicalMarginals marginals active sides limitCuts hmasses)
            reward) := by
  classical
  choose cuts hmem hcuts using fun i : {i // i ∈ active} =>
    Math.Topology.exists_mem_tendsto_of_nonemptyCompacts_tendsto hE (hendpoints i)
  have hweights := eventually_conditionalChronologicalReplacement_le source subsequence hlaws
    active sides limitCuts cuts hmem hcuts hmasses
  have hlimit := tendsto_referenceLaw_conditionalChronologicalReplacement source subsequence hlaws
    active sides limitCuts cuts hmem hcuts hmasses
  refine ⟨cuts, hmem, hcuts, hweights, hlimit, ?_⟩
  intro reward
  exact ⟨tendsto_referenceSemanticPair (fun k => source (subsequence k))
      (conditionalChronologicalReplacement source subsequence active sides cuts) id hE hc hT
      (conditionalChronologicalEnvelope marginals active sides limitCuts hmasses)
      hweights hlimit reward,
    referenceLimitSemanticPair_mem_carrier (fun k => source (subsequence k))
      (conditionalChronologicalReplacement source subsequence active sides cuts) id hE hc hT
      (conditionalChronologicalEnvelope marginals active sides limitCuts hmasses)
      hweights hlimit reward,
    debtSumInf_le_referenceLimitSemanticPair (fun k => source (subsequence k))
      (conditionalChronologicalReplacement source subsequence active sides cuts) id hE hc hT
      (conditionalChronologicalEnvelope marginals active sides limitCuts hmasses)
      hweights hlimit reward⟩

end GameTheory.MarkedCalendarChart
