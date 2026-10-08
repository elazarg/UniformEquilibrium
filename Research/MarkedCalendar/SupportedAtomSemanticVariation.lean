import Research.MarkedCalendar.SupportedAtomVariation
import Research.MarkedCalendar.FiniteLawSemanticMinimum

/-! # Partial joint signed variations at actual supported atoms

Positive own atoms only on the active owners determine raw gaps and selectors
before every signed parameter vector and reward table. Inactive owners retain
their original laws. The all-index finite replacements use the unchanged old
reference calendars, including the safe original-law fallback.

The actual marginal limits, three-halves density envelope, mapped reset identities,
original full-cap semantic convergence, carrier membership, and SUM floor are
derived. No new subsequence or replacement-law convergence oracle is supplied.
The empty active set and the zero vector are identities. Variations are not
asserted to be minima, and parameter one is not identified with the signed
fallback. Ordinary conditioning and chronological cuts remain separate.
-/

noncomputable section

open Set Filter MeasureTheory TopologicalSpace GameTheory.Math.Probability
open scoped Topology

namespace GameTheory.MarkedCalendarChart

/-- Geometric data for one actual supported atom. There is no convergence or cap field. -/
structure SupportedAtomDirection (limit : MathUE.MarkedCalendar.Calendar)
    (law : ProbabilityMeasure unitInterval) (atom : WithTop ℝ) where
  first : ℝ
  last : ℝ
  gap : Math.Topology.IsGap limit.endpoints first last
  mass_pos : 0 < (law : Measure unitInterval).real
    {x | first < (x : ℝ) ∧ (x : ℝ) < last}
  mass_eq : (law : Measure unitInterval).real {x | first < (x : ℝ) ∧ (x : ℝ) < last} =
    ((law : Measure unitInterval).map limit.collapseClock).real {atom}
  shape : (last ≤ (limit.cutoff : ℝ) ∧ atom = (((first + last) / 2 : ℝ) : WithTop ℝ)) ∨
    (first = (limit.cutoff : ℝ) ∧ last = 1 ∧ atom = ⊤)

namespace SupportedAtomDirection

variable {limit : MathUE.MarkedCalendar.Calendar} {law : ProbabilityMeasure unitInterval}
  {atom : WithTop ℝ}

def event (direction : SupportedAtomDirection limit law atom) : Set unitInterval :=
  {x | direction.first < (x : ℝ) ∧ (x : ℝ) < direction.last}

theorem measurableSet_event (direction : SupportedAtomDirection limit law atom) :
    MeasurableSet direction.event :=
  measurableSet_Ioo.preimage measurable_subtype_coe

/-- This selector depends on the gap, never on a parameter or reward table. -/
def selector (direction : SupportedAtomDirection limit law atom) : unitInterval :=
  ⟨(direction.first + direction.last) / 2, by
    have ha := limit.endpoints_subset direction.gap.1
    have hb := limit.endpoints_subset direction.gap.2.1
    constructor <;> linarith [ha.1, hb.2, direction.gap.2.2.1]⟩

theorem first_lt_selector (direction : SupportedAtomDirection limit law atom) :
    direction.first < (direction.selector : ℝ) := by
  change direction.first < (direction.first + direction.last) / 2
  linarith [direction.gap.2.2.1]

theorem selector_lt_last (direction : SupportedAtomDirection limit law atom) :
    (direction.selector : ℝ) < direction.last := by
  change (direction.first + direction.last) / 2 < direction.last
  linarith [direction.gap.2.2.1]

def radius (direction : SupportedAtomDirection limit law atom) : ℝ :=
  min (1 / 2 : ℝ) ((law : Measure unitInterval).real direction.event / 4)

theorem radius_pos (direction : SupportedAtomDirection limit law atom) : 0 < direction.radius :=
  lt_min (by norm_num) (div_pos direction.mass_pos (by norm_num))

theorem parameter_le_signedCondRadius (direction : SupportedAtomDirection limit law atom)
    (parameter : ℝ) (hparameter : |parameter| ≤ direction.radius) :
    |parameter| ≤ law.signedCondRadius direction.event := by
  refine le_min (hparameter.trans (min_le_left _ _)) ?_
  have hsmall := hparameter.trans (min_le_right _ _)
  have hpositive := direction.mass_pos
  change |parameter| ≤ (law : Measure unitInterval).real direction.event / 4 at hsmall
  change 0 < (law : Measure unitInterval).real direction.event at hpositive
  linarith

def limitLaw (direction : SupportedAtomDirection limit law atom)
    (parameter : ℝ) (hparameter : |parameter| ≤ direction.radius) :
    ProbabilityMeasure unitInterval :=
  law.signedCond direction.event direction.measurableSet_event direction.mass_pos parameter
    (direction.parameter_le_signedCondRadius parameter hparameter)

theorem limitLaw_zero (direction : SupportedAtomDirection limit law atom) :
    direction.limitLaw 0 (by simpa only [abs_zero] using direction.radius_pos.le) = law :=
  ProbabilityMeasure.signedCond_zero law direction.event direction.measurableSet_event
    direction.mass_pos

open Classical in
/-- Both geometric cases delegate the checked mapped-reset identities. -/
theorem map_limitLaw_real (direction : SupportedAtomDirection limit law atom)
    (parameter : ℝ) (hparameter : |parameter| ≤ direction.radius)
    (target : Set (WithTop ℝ)) (htarget : MeasurableSet target) :
    ((direction.limitLaw parameter hparameter : Measure unitInterval).map
      limit.collapseClock).real target =
      (1 - parameter) * ((law : Measure unitInterval).map limit.collapseClock).real target +
        parameter * (if atom ∈ target then (1 : ℝ) else 0) := by
  rcases direction.shape with ⟨hb, hatom⟩ | ⟨ha, hb, hatom⟩
  · have h := map_signedCond_gap_real limit law direction.gap hb direction.mass_pos parameter
      (direction.parameter_le_signedCondRadius parameter hparameter) target htarget
    exact h.trans (by simp only [hatom])
  · have hmass : 0 < (law : Measure unitInterval).real
        {x | (limit.cutoff : ℝ) < (x : ℝ) ∧ (x : ℝ) < 1} := by
      simpa only [ha, hb] using direction.mass_pos
    have hradius : |parameter| ≤ law.signedCondRadius
        {x | (limit.cutoff : ℝ) < (x : ℝ) ∧ (x : ℝ) < 1} := by
      simpa only [event, ha, hb] using
        direction.parameter_le_signedCondRadius parameter hparameter
    simpa only [limitLaw, event, ha, hb, hatom] using
      map_signedCond_neverGap_real limit law hmass parameter hradius target htarget

end SupportedAtomDirection

variable {ι : Type} [Fintype ι] [Nonempty ι]

/-- The direction is produced from the original marginal's actual atom, including Never. -/
theorem nonempty_supportedAtomDirection
    (source : ℕ → ι → FinDist (Option ℕ)) (subsequence : ℕ → ℕ)
    {limit : MathUE.MarkedCalendar.Calendar}
    (hE : Tendsto (fun k => (calendar (source (subsequence k))).endpoints) atTop
      (𝓝 limit.endpoints))
    (hc : Tendsto (fun k => cutoff (source (subsequence k))) atTop (𝓝 limit.cutoff))
    (i : ι) {law : ProbabilityMeasure unitInterval}
    (hlaw : Tendsto (fun k => chartLaw (source (subsequence k)) i) atTop (𝓝 law))
    (atom : WithTop ℝ)
    (hatom : 0 < ((law : Measure unitInterval).map limit.collapseClock).real {atom}) :
    Nonempty (SupportedAtomDirection limit law atom) := by
  by_cases htop : atom = ⊤
  · subst atom
    obtain ⟨_, hgap, _, hmassEq⟩ :=
      limit_never_gap_of_positive_own_atom source subsequence hE hc i hlaw hatom
    refine ⟨⟨(limit.cutoff : ℝ), 1, hgap, ?_, hmassEq, Or.inr ⟨rfl, rfl, rfl⟩⟩⟩
    rw [hmassEq]
    exact hatom
  · obtain ⟨t, rfl⟩ := WithTop.ne_top_iff_exists.mp htop
    obtain ⟨a, b, hgap, hb, ht, _, _, hmassEq⟩ :=
      exists_limit_gap_of_positive_finite_own_atom source subsequence limit i hlaw hatom
    refine ⟨⟨a, b, hgap, ?_, hmassEq, Or.inl ⟨hb, congrArg WithTop.some ht⟩⟩⟩
    rw [hmassEq]
    exact hatom

variable [DecidableEq ι]

/-- Literal finite replacements on the old reference cells, with inactive owners unchanged. -/
def signedAtomReplacement (source : ℕ → ι → FinDist (Option ℕ))
    {limit : MathUE.MarkedCalendar.Calendar} {marginals : ι → ProbabilityMeasure unitInterval}
    (active : Finset ι) (atoms : {i // i ∈ active} → WithTop ℝ)
    (directions : ∀ i, SupportedAtomDirection limit (marginals i.1) (atoms i))
    (parameters : {i // i ∈ active} → ℝ) (n : ℕ) (i : ι) : FinDist (Cell (source n)) :=
  if hi : i ∈ active then
    signedSelectedCellLaw (source n) i (directions ⟨i, hi⟩).selector (parameters ⟨i, hi⟩)
  else cellLaw (source n) i

def signedAtomMarginals
    {limit : MathUE.MarkedCalendar.Calendar} {marginals : ι → ProbabilityMeasure unitInterval}
    (active : Finset ι) (atoms : {i // i ∈ active} → WithTop ℝ)
    (directions : ∀ i, SupportedAtomDirection limit (marginals i.1) (atoms i))
    (parameters : {i // i ∈ active} → ℝ)
    (hparameters : ∀ i, |parameters i| ≤ (directions i).radius)
    (i : ι) : ProbabilityMeasure unitInterval :=
  if hi : i ∈ active then
    (directions ⟨i, hi⟩).limitLaw (parameters ⟨i, hi⟩) (hparameters ⟨i, hi⟩)
  else marginals i

theorem signedAtomReplacement_empty (source : ℕ → ι → FinDist (Option ℕ))
    {limit : MathUE.MarkedCalendar.Calendar} {marginals : ι → ProbabilityMeasure unitInterval}
    (atoms : {i // i ∈ (∅ : Finset ι)} → WithTop ℝ)
    (directions : ∀ i, SupportedAtomDirection limit (marginals i.1) (atoms i))
    (parameters : {i // i ∈ (∅ : Finset ι)} → ℝ) :
    signedAtomReplacement source ∅ atoms directions parameters = fun n => cellLaw (source n) := by
  funext n i
  simp only [signedAtomReplacement, Finset.notMem_empty, dite_false]

omit [Fintype ι] [Nonempty ι] in
theorem signedAtomMarginals_empty
    {limit : MathUE.MarkedCalendar.Calendar} {marginals : ι → ProbabilityMeasure unitInterval}
    (atoms : {i // i ∈ (∅ : Finset ι)} → WithTop ℝ)
    (directions : ∀ i, SupportedAtomDirection limit (marginals i.1) (atoms i))
    (parameters : {i // i ∈ (∅ : Finset ι)} → ℝ)
    (hparameters : ∀ i, |parameters i| ≤ (directions i).radius) :
    signedAtomMarginals ∅ atoms directions parameters hparameters = marginals := by
  funext i
  simp only [signedAtomMarginals, Finset.notMem_empty, dite_false]

theorem signedAtomReplacement_zero (source : ℕ → ι → FinDist (Option ℕ))
    {limit : MathUE.MarkedCalendar.Calendar} {marginals : ι → ProbabilityMeasure unitInterval}
    (active : Finset ι) (atoms : {i // i ∈ active} → WithTop ℝ)
    (directions : ∀ i, SupportedAtomDirection limit (marginals i.1) (atoms i)) :
    signedAtomReplacement source active atoms directions (fun _ => 0) =
      fun n => cellLaw (source n) := by
  funext n i
  by_cases hi : i ∈ active
  · simp only [signedAtomReplacement, dite_eq_left hi, signedSelectedCellLaw_zero]
  · simp only [signedAtomReplacement, dite_eq_right hi]

omit [Fintype ι] [Nonempty ι] in
theorem signedAtomMarginals_zero
    {limit : MathUE.MarkedCalendar.Calendar} {marginals : ι → ProbabilityMeasure unitInterval}
    (active : Finset ι) (atoms : {i // i ∈ active} → WithTop ℝ)
    (directions : ∀ i, SupportedAtomDirection limit (marginals i.1) (atoms i)) :
    signedAtomMarginals active atoms directions (fun _ => 0)
      (fun i => by simpa only [abs_zero] using (directions i).radius_pos.le) = marginals := by
  funext i
  by_cases hi : i ∈ active
  · simp only [signedAtomMarginals, dite_eq_left hi, SupportedAtomDirection.limitLaw_zero]
  · simp only [signedAtomMarginals, dite_eq_right hi]

/-- The envelope holds at every source index, even where the original-law fallback is used. -/
theorem prob_signedAtomReplacement_le (source : ℕ → ι → FinDist (Option ℕ))
    {limit : MathUE.MarkedCalendar.Calendar} {marginals : ι → ProbabilityMeasure unitInterval}
    (active : Finset ι) (atoms : {i // i ∈ active} → WithTop ℝ)
    (directions : ∀ i, SupportedAtomDirection limit (marginals i.1) (atoms i))
    (parameters : {i // i ∈ active} → ℝ) (n : ℕ) (i : ι) (a : Cell (source n)) :
    (signedAtomReplacement source active atoms directions parameters n i).prob a ≤
      ((3 / 2 : ℝ) * Fintype.card ι) * weight (source n) a := by
  have hown := ownWeight_le (source n) i a
  have hnonneg := ownWeight_nonneg (source n) i a
  by_cases hi : i ∈ active
  · rw [signedAtomReplacement, dite_eq_left hi]
    have hbound := (prob_signedSelectedCellLaw_bounds (source n) i
      (directions ⟨i, hi⟩).selector (parameters ⟨i, hi⟩) a).2
    rw [cellLaw_prob] at hbound
    nlinarith
  · rw [signedAtomReplacement, dite_eq_right hi, cellLaw_prob]
    nlinarith

/-- All active marginal limits use the same supplied source subsequence. -/
theorem tendsto_referenceLaw_signedAtomReplacement
    (source : ℕ → ι → FinDist (Option ℕ)) (subsequence : ℕ → ℕ)
    {limit : MathUE.MarkedCalendar.Calendar} {marginals : ι → ProbabilityMeasure unitInterval}
    (hE : Tendsto (fun k => (calendar (source (subsequence k))).endpoints) atTop
      (𝓝 limit.endpoints))
    (hlaws : Tendsto (fun k => chartLaw (source (subsequence k))) atTop (𝓝 marginals))
    (active : Finset ι) (atoms : {i // i ∈ active} → WithTop ℝ)
    (directions : ∀ i, SupportedAtomDirection limit (marginals i.1) (atoms i))
    (parameters : {i // i ∈ active} → ℝ)
    (hparameters : ∀ i, |parameters i| ≤ (directions i).radius) :
    Tendsto (fun k i => referenceLaw (source (subsequence k))
      (signedAtomReplacement source active atoms directions parameters (subsequence k) i))
      atTop (𝓝 (signedAtomMarginals active atoms directions parameters hparameters)) := by
  apply tendsto_pi_nhds.mpr
  intro i
  have hiLaw := (tendsto_pi_nhds.mp hlaws) i
  by_cases hi : i ∈ active
  · have h := tendsto_referenceLaw_signedSelectedCellLaw source subsequence hE i hiLaw
      (directions ⟨i, hi⟩).gap (directions ⟨i, hi⟩).first_lt_selector
      (directions ⟨i, hi⟩).selector_lt_last (directions ⟨i, hi⟩).mass_pos
      (parameters ⟨i, hi⟩) (hparameters ⟨i, hi⟩)
    simpa only [signedAtomReplacement, signedAtomMarginals, dite_eq_left hi,
      SupportedAtomDirection.limitLaw, SupportedAtomDirection.event] using h
  · simpa only [signedAtomReplacement, signedAtomMarginals, dite_eq_right hi, chartLaw] using hiLaw

open Classical in
/-- Actual atoms on any subset of owners produce one joint signed box before all parameters and
rewards, with exact original full caps, carrier membership, and the canonical SUM floor. -/
theorem exists_supportedAtom_semantic_variation
    (source : ℕ → ι → FinDist (Option ℕ)) (subsequence : ℕ → ℕ)
    {limit : MathUE.MarkedCalendar.Calendar} {menu : NonemptyCompacts ℝ}
    {marginals : ι → ProbabilityMeasure unitInterval}
    (hE : Tendsto (fun k => (calendar (source (subsequence k))).endpoints) atTop
      (𝓝 limit.endpoints))
    (hc : Tendsto (fun k => cutoff (source (subsequence k))) atTop (𝓝 limit.cutoff))
    (hT : Tendsto (fun k => legalMenuCompacts (source (subsequence k))) atTop (𝓝 menu))
    (hlaws : Tendsto (fun k => chartLaw (source (subsequence k))) atTop (𝓝 marginals))
    (active : Finset ι) (atoms : {i // i ∈ active} → WithTop ℝ)
    (hatoms : ∀ i, 0 < ((marginals i.1 : Measure unitInterval).map
      limit.collapseClock).real {atoms i}) :
    ∃ directions : ∀ i, SupportedAtomDirection limit (marginals i.1) (atoms i),
      (∀ i, 0 < (directions i).radius) ∧
      ∀ (parameters : {i // i ∈ active} → ℝ)
        (hparameters : ∀ i, |parameters i| ≤ (directions i).radius),
        Tendsto (fun k i => referenceLaw (source (subsequence k))
          (signedAtomReplacement source active atoms directions parameters (subsequence k) i))
          atTop (𝓝 (signedAtomMarginals active atoms directions parameters hparameters)) ∧
        (∀ i (target : Set (WithTop ℝ)), MeasurableSet target →
          (((signedAtomMarginals active atoms directions parameters hparameters) i.1 :
            Measure unitInterval).map limit.collapseClock).real target =
            (1 - parameters i) * ((marginals i.1 : Measure unitInterval).map
              limit.collapseClock).real target +
                parameters i * (if atoms i ∈ target then (1 : ℝ) else 0)) ∧
        ∀ reward : {S : Finset ι // S.Nonempty} → Payoff ι,
          Tendsto (fun k => quittingTerminalSemanticPair reward
            (quittingStoppingLawProfile reward (fun i =>
              (referenceOriginalLaw (source (subsequence k))
                (signedAtomReplacement source active atoms directions parameters
                  (subsequence k) i)).toPMF))) atTop
            (𝓝 (limitSemanticPair limit menu
              (signedAtomMarginals active atoms directions parameters hparameters) reward)) ∧
          limitSemanticPair limit menu
            (signedAtomMarginals active atoms directions parameters hparameters) reward ∈
              quittingTerminalSemanticCarrier reward ∧
          quittingTerminalDebtSumInf reward ≤ quittingTerminalSemanticDebtSum
            (limitSemanticPair limit menu
              (signedAtomMarginals active atoms directions parameters hparameters) reward) := by
  let directions : ∀ i, SupportedAtomDirection limit (marginals i.1) (atoms i) := fun i =>
    Classical.choice (nonempty_supportedAtomDirection source subsequence hE hc i.1
      ((tendsto_pi_nhds.mp hlaws) i.1) (atoms i) (hatoms i))
  refine ⟨directions, fun i => (directions i).radius_pos, ?_⟩
  intro parameters hparameters
  have hlimit := tendsto_referenceLaw_signedAtomReplacement source subsequence hE hlaws
    active atoms directions parameters hparameters
  refine ⟨hlimit, ?_, ?_⟩
  · intro i target htarget
    simpa only [signedAtomMarginals, dite_eq_left i.property] using
      (directions i).map_limitLaw_real (parameters i) (hparameters i) target htarget
  · intro reward
    let C : ι → NNReal := fun _ => (3 / 2 : NNReal) * Fintype.card ι
    have hweights : ∀ᶠ k in atTop, ∀ i (a : Cell (source (subsequence k))),
        (signedAtomReplacement source active atoms directions parameters (subsequence k) i).prob a ≤
          (C i : ℝ) * weight (source (subsequence k)) a := by
      apply Eventually.of_forall
      intro k i a
      simpa [C] using
        prob_signedAtomReplacement_le source active atoms directions parameters (subsequence k) i a
    exact ⟨tendsto_referenceSemanticPair source
        (signedAtomReplacement source active atoms directions parameters) subsequence
        hE hc hT C hweights hlimit reward,
      referenceLimitSemanticPair_mem_carrier source
        (signedAtomReplacement source active atoms directions parameters) subsequence
        hE hc hT C hweights hlimit reward,
      debtSumInf_le_referenceLimitSemanticPair source
        (signedAtomReplacement source active atoms directions parameters) subsequence
        hE hc hT C hweights hlimit reward⟩

end GameTheory.MarkedCalendarChart
