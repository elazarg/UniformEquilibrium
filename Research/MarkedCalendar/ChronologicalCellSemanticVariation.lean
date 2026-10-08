import Research.MarkedCalendar.ChronologicalCellSignedVariation
import Research.MarkedCalendar.FiniteLawSemanticMinimum

/-! # Partial joint chronological signed families in the original carrier

Actual limiting endpoints choose one old-endpoint sequence per active owner
before every signed parameter vector and reward table. Positivity is required
only for the active raw events; inactive owners keep their original laws.

The source is literally reindexed by the supplied subsequence, with no new
extraction or injectivity assumption. Actual marginal limits and a derived
three-halves envelope feed the existing original payoff/full-cap convergence,
carrier membership, and SUM-floor theorems. Empty activity and zero parameters
give the original family. No variation is asserted to be a minimum, and the
ordinary conditioning endpoint is not obtained by evaluating this safe signed
family at parameter one.
-/

noncomputable section

open Set Filter MeasureTheory TopologicalSpace GameTheory.Math.Probability
open scoped Topology

namespace GameTheory.MarkedCalendarChart

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]

/-- The old source is reindexed, not replaced by a newly averaged chart. -/
def signedChronologicalReplacement (source : ℕ → ι → FinDist (Option ℕ))
    (subsequence : ℕ → ℕ) (active : Finset ι)
    (sides : {i // i ∈ active} → ChronologicalSide)
    (cuts : {i // i ∈ active} → ℕ → ℝ)
    (parameters : {i // i ∈ active} → ℝ) (k : ℕ) (i : ι) :
    FinDist (Cell (source (subsequence k))) :=
  if hi : i ∈ active then signedCutCellLaw (source (subsequence k))
    (sides ⟨i, hi⟩) (cuts ⟨i, hi⟩ k) i (parameters ⟨i, hi⟩)
  else cellLaw (source (subsequence k)) i

def signedChronologicalMarginals (marginals : ι → ProbabilityMeasure unitInterval)
    (active : Finset ι) (sides : {i // i ∈ active} → ChronologicalSide)
    (cuts : {i // i ∈ active} → ℝ)
    (hmasses : ∀ i, 0 < (marginals i.1 : Measure unitInterval).real
      (rawCutEvent (sides i) (cuts i)))
    (parameters : {i // i ∈ active} → ℝ)
    (hparameters : ∀ i, |parameters i| ≤ cutSignedRadius (marginals i.1) (sides i) (cuts i))
    (i : ι) : ProbabilityMeasure unitInterval :=
  if hi : i ∈ active then cutSignedLaw (marginals i) (sides ⟨i, hi⟩) (cuts ⟨i, hi⟩)
    (hmasses ⟨i, hi⟩) (parameters ⟨i, hi⟩) (hparameters ⟨i, hi⟩)
  else marginals i

theorem signedChronologicalReplacement_empty (source : ℕ → ι → FinDist (Option ℕ))
    (subsequence : ℕ → ℕ) (sides : {i // i ∈ (∅ : Finset ι)} → ChronologicalSide)
    (cuts : {i // i ∈ (∅ : Finset ι)} → ℕ → ℝ)
    (parameters : {i // i ∈ (∅ : Finset ι)} → ℝ) :
    signedChronologicalReplacement source subsequence ∅ sides cuts parameters =
      fun k => cellLaw (source (subsequence k)) := by
  funext k i
  simp only [signedChronologicalReplacement, Finset.notMem_empty, dite_false]

omit [Fintype ι] [Nonempty ι] in
theorem signedChronologicalMarginals_empty (marginals : ι → ProbabilityMeasure unitInterval)
    (sides : {i // i ∈ (∅ : Finset ι)} → ChronologicalSide)
    (cuts : {i // i ∈ (∅ : Finset ι)} → ℝ)
    (hmasses : ∀ i, 0 < (marginals i.1 : Measure unitInterval).real
      (rawCutEvent (sides i) (cuts i)))
    (parameters : {i // i ∈ (∅ : Finset ι)} → ℝ)
    (hparameters : ∀ i, |parameters i| ≤ cutSignedRadius (marginals i.1) (sides i) (cuts i)) :
    signedChronologicalMarginals marginals ∅ sides cuts hmasses parameters hparameters =
      marginals := by
  funext i
  simp only [signedChronologicalMarginals, Finset.notMem_empty, dite_false]

theorem signedChronologicalReplacement_zero (source : ℕ → ι → FinDist (Option ℕ))
    (subsequence : ℕ → ℕ) (active : Finset ι)
    (sides : {i // i ∈ active} → ChronologicalSide)
    (cuts : {i // i ∈ active} → ℕ → ℝ) :
    signedChronologicalReplacement source subsequence active sides cuts (fun _ => 0) =
      fun k => cellLaw (source (subsequence k)) := by
  funext k i
  by_cases hi : i ∈ active
  · simp only [signedChronologicalReplacement, dite_eq_left hi, signedCutCellLaw_zero]
  · simp only [signedChronologicalReplacement, dite_eq_right hi]

omit [Fintype ι] [Nonempty ι] in
theorem signedChronologicalMarginals_zero (marginals : ι → ProbabilityMeasure unitInterval)
    (active : Finset ι) (sides : {i // i ∈ active} → ChronologicalSide)
    (cuts : {i // i ∈ active} → ℝ)
    (hmasses : ∀ i, 0 < (marginals i.1 : Measure unitInterval).real
      (rawCutEvent (sides i) (cuts i))) :
    signedChronologicalMarginals marginals active sides cuts hmasses (fun _ => 0)
      (fun i => by
        simpa only [abs_zero] using
          (cutSignedRadius_pos (marginals i.1) (sides i) (cuts i) (hmasses i)).le) =
      marginals := by
  funext i
  by_cases hi : i ∈ active
  · simp only [signedChronologicalMarginals, dite_eq_left hi, cutSignedLaw_zero]
  · simp only [signedChronologicalMarginals, dite_eq_right hi]

/-- Active and inactive owners share an internally derived all-index reference envelope. -/
theorem prob_signedChronologicalReplacement_le (source : ℕ → ι → FinDist (Option ℕ))
    (subsequence : ℕ → ℕ) (active : Finset ι)
    (sides : {i // i ∈ active} → ChronologicalSide)
    (cuts : {i // i ∈ active} → ℕ → ℝ)
    (parameters : {i // i ∈ active} → ℝ) (k : ℕ) (i : ι)
    (cell : Cell (source (subsequence k))) :
    (signedChronologicalReplacement source subsequence active sides cuts parameters k i).prob cell ≤
      ((3 / 2 : ℝ) * Fintype.card ι) * weight (source (subsequence k)) cell := by
  by_cases hi : i ∈ active
  · simpa only [signedChronologicalReplacement, dite_eq_left hi] using
      prob_signedCutCellLaw_le (source (subsequence k)) (sides ⟨i, hi⟩)
        (cuts ⟨i, hi⟩ k) i (parameters ⟨i, hi⟩) cell
  · rw [signedChronologicalReplacement, dite_eq_right hi, cellLaw_prob]
    have hown := ownWeight_le (source (subsequence k)) i cell
    have hnonneg := ownWeight_nonneg (source (subsequence k)) i cell
    nlinarith

/-- Per-owner cut limits assemble on the same reindexed source, without a parameter-dependent
subsequence or any supplied replacement-law convergence. -/
theorem tendsto_referenceLaw_signedChronologicalReplacement
    (source : ℕ → ι → FinDist (Option ℕ)) (subsequence : ℕ → ℕ)
    {marginals : ι → ProbabilityMeasure unitInterval}
    (hlaws : Tendsto (fun k => chartLaw (source (subsequence k))) atTop (𝓝 marginals))
    (active : Finset ι) (sides : {i // i ∈ active} → ChronologicalSide)
    (limitCuts : {i // i ∈ active} → ℝ) (cuts : {i // i ∈ active} → ℕ → ℝ)
    (hmem : ∀ i k, cuts i k ∈ (calendar (source (subsequence k))).endpoints)
    (hcuts : ∀ i, Tendsto (cuts i) atTop (𝓝 (limitCuts i)))
    (hmasses : ∀ i, 0 < (marginals i.1 : Measure unitInterval).real
      (rawCutEvent (sides i) (limitCuts i)))
    (parameters : {i // i ∈ active} → ℝ)
    (hparameters : ∀ i, |parameters i| ≤
      cutSignedRadius (marginals i.1) (sides i) (limitCuts i)) :
    Tendsto (fun k i => referenceLaw (source (subsequence k))
      (signedChronologicalReplacement source subsequence active sides cuts parameters k i))
      atTop (𝓝 (signedChronologicalMarginals marginals active sides limitCuts
        hmasses parameters hparameters)) := by
  apply tendsto_pi_nhds.mpr
  intro i
  have hiLaw := (tendsto_pi_nhds.mp hlaws) i
  by_cases hi : i ∈ active
  · have h := tendsto_referenceLaw_signedCutCellLaw source subsequence (cuts ⟨i, hi⟩)
      (hmem ⟨i, hi⟩) (hcuts ⟨i, hi⟩) (sides ⟨i, hi⟩) i hiLaw (hmasses ⟨i, hi⟩)
      (parameters ⟨i, hi⟩) (hparameters ⟨i, hi⟩)
    simpa only [signedChronologicalReplacement, signedChronologicalMarginals,
      dite_eq_left hi] using h
  · simpa only [signedChronologicalReplacement, signedChronologicalMarginals,
      dite_eq_right hi, chartLaw] using hiLaw

/-- One actual old-endpoint family precedes all legal signed vectors and all rewards. The
limiting pair is attained in the original closed carrier and obeys its canonical SUM floor. -/
theorem exists_chronological_semantic_variation
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
      (∀ i, 0 < cutSignedRadius (marginals i.1) (sides i) (limitCuts i)) ∧
      ∀ (parameters : {i // i ∈ active} → ℝ)
        (hparameters : ∀ i, |parameters i| ≤
          cutSignedRadius (marginals i.1) (sides i) (limitCuts i)),
        Tendsto (fun k i => referenceLaw (source (subsequence k))
          (signedChronologicalReplacement source subsequence active sides cuts parameters k i))
          atTop (𝓝 (signedChronologicalMarginals marginals active sides limitCuts
            hmasses parameters hparameters)) ∧
        ∀ reward : {S : Finset ι // S.Nonempty} → Payoff ι,
          Tendsto (fun k => quittingTerminalSemanticPair reward
            (quittingStoppingLawProfile reward (fun i =>
              (referenceOriginalLaw (source (subsequence k))
                (signedChronologicalReplacement source subsequence active sides cuts
                  parameters k i)).toPMF))) atTop
            (𝓝 (limitSemanticPair limit menu
              (signedChronologicalMarginals marginals active sides limitCuts
                hmasses parameters hparameters) reward)) ∧
          limitSemanticPair limit menu
            (signedChronologicalMarginals marginals active sides limitCuts
              hmasses parameters hparameters) reward ∈ quittingTerminalSemanticCarrier reward ∧
          quittingTerminalDebtSumInf reward ≤ quittingTerminalSemanticDebtSum
            (limitSemanticPair limit menu
              (signedChronologicalMarginals marginals active sides limitCuts
                hmasses parameters hparameters) reward) := by
  classical
  choose cuts hmem hcuts using fun i : {i // i ∈ active} =>
    Math.Topology.exists_mem_tendsto_of_nonemptyCompacts_tendsto hE (hendpoints i)
  refine ⟨cuts, hmem, hcuts, fun i =>
    cutSignedRadius_pos (marginals i.1) (sides i) (limitCuts i) (hmasses i), ?_⟩
  intro parameters hparameters
  have hlimit := tendsto_referenceLaw_signedChronologicalReplacement source subsequence hlaws
    active sides limitCuts cuts hmem hcuts hmasses parameters hparameters
  refine ⟨hlimit, ?_⟩
  intro reward
  let C : ι → NNReal := fun _ => (3 / 2 : NNReal) * Fintype.card ι
  have hweights : ∀ᶠ k in atTop, ∀ i (cell : Cell (source (subsequence k))),
      (signedChronologicalReplacement source subsequence active sides cuts
        parameters k i).prob cell ≤
        (C i : ℝ) * weight (source (subsequence k)) cell := by
    apply Eventually.of_forall
    intro k i cell
    simpa [C] using prob_signedChronologicalReplacement_le
      source subsequence active sides cuts parameters k i cell
  exact ⟨tendsto_referenceSemanticPair (fun k => source (subsequence k))
      (signedChronologicalReplacement source subsequence active sides cuts parameters) id
      hE hc hT C hweights hlimit reward,
    referenceLimitSemanticPair_mem_carrier (fun k => source (subsequence k))
      (signedChronologicalReplacement source subsequence active sides cuts parameters) id
      hE hc hT C hweights hlimit reward,
    debtSumInf_le_referenceLimitSemanticPair (fun k => source (subsequence k))
      (signedChronologicalReplacement source subsequence active sides cuts parameters) id
      hE hc hT C hweights hlimit reward⟩

end GameTheory.MarkedCalendarChart
