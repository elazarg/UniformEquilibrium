import Research.MarkedCalendar.SupportedAtomSemanticVariation
import Research.MarkedCalendar.SupportedAtomConditioning
import MathUE.Probability.BooleanEndpointExpectation

/-! # Actual supported-atom payoff interpolation

Boolean endpoints are original laws or ordinary conditional laws, chosen before
parameters and rewards. The actual legal signed family has their Boolean payoff
interpolant on the same marked source subsequence. Prescribed payoff and selected
finite and Never responses use the same endpoints.

These are selected payoff identities, not full-cap identities. Parameter one in
the algebraic interpolant refers to ordinary conditioning, not to the signed
constructor's fallback. Cap stability, the common additive constant for upper
response families, and the final conditional full-cap bound remain separate.
No interpolation identity alone asserts a minimum or a source classification.
-/

noncomputable section

open Set Filter MeasureTheory TopologicalSpace GameTheory.Math.Probability
open scoped Topology BigOperators

namespace GameTheory.MarkedCalendarChart

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
  {limit : MathUE.MarkedCalendar.Calendar}
  {marginals : ι → ProbabilityMeasure unitInterval}

/-- The ordinary Boolean endpoints; inactive owners retain their original laws. -/
def atomEndpointReplacement (source : ℕ → ι → FinDist (Option ℕ))
    (active : Finset ι) (atoms : {i // i ∈ active} → WithTop ℝ)
    (directions : ∀ i, SupportedAtomDirection limit (marginals i.1) (atoms i))
    (vertex : ι → Bool) (n : ℕ) (i : ι) : FinDist (Cell (source n)) :=
  if hi : i ∈ active then
    if vertex i then conditionalSelectedCellLaw (source n) i (directions ⟨i, hi⟩).selector
    else cellLaw (source n) i
  else cellLaw (source n) i

/-- Actual ordinary limiting endpoints, not an evaluation of the signed fallback at one. -/
def atomEndpointMarginals (active : Finset ι) (atoms : {i // i ∈ active} → WithTop ℝ)
    (directions : ∀ i, SupportedAtomDirection limit (marginals i.1) (atoms i))
    (vertex : ι → Bool) (i : ι) : ProbabilityMeasure unitInterval :=
  if hi : i ∈ active then
    if vertex i then gapConditionalLaw (marginals i)
      (directions ⟨i, hi⟩).first (directions ⟨i, hi⟩).last (directions ⟨i, hi⟩).mass_pos
    else marginals i
  else marginals i

omit [DecidableEq ι] in
private theorem conditionalSelectedCellLaw_eq_pure
    (laws : ι → FinDist (Option ℕ)) (i : ι) (x : unitInterval)
    (hpositive : 0 < (cellLaw laws i).prob (decodeCell laws x)) :
    conditionalSelectedCellLaw laws i x = FinDist.pure (decodeCell laws x) := by
  classical
  have hevent : 0 < (cellLaw laws i).probOf {decodeCell laws x} := by
    simpa only [FinDist.probOf_singleton] using hpositive
  rw [conditionalSelectedCellLaw, conditionalCellLaw, dite_eq_left hevent]
  apply FinDist.ext_of_prob
  intro cell
  rw [FinDist.prob_condOn, FinDist.probOf_singleton, FinDist.prob_pure_eq_ite]
  by_cases hcell : cell = decodeCell laws x
  · subst cell
    simp only [mem_singleton_iff, ite_true, div_self hpositive.ne']
  · simp only [mem_singleton_iff, hcell, ite_false]

private theorem eventually_atom_affine
    (source : ℕ → ι → FinDist (Option ℕ)) (subsequence : ℕ → ℕ)
    (hE : Tendsto (fun k => (calendar (source (subsequence k))).endpoints) atTop
      (𝓝 limit.endpoints))
    (hlaws : Tendsto (fun k => chartLaw (source (subsequence k))) atTop (𝓝 marginals))
    (active : Finset ι) (atoms : {i // i ∈ active} → WithTop ℝ)
    (directions : ∀ i, SupportedAtomDirection limit (marginals i.1) (atoms i))
    (parameters : ι → ℝ)
    (hparameters : ∀ i : {i // i ∈ active}, |parameters i.1| ≤ (directions i).radius) :
    ∀ᶠ k in atTop, ∀ i cell,
      (signedAtomReplacement source active atoms directions
        (fun i => parameters i.1) (subsequence k) i).prob cell =
      (1 - parameters i) * (atomEndpointReplacement source active atoms directions
        (fun _ => false) (subsequence k) i).prob cell +
      parameters i * (atomEndpointReplacement source active atoms directions
        (fun _ => true) (subsequence k) i).prob cell := by
  classical
  apply eventually_all.mpr
  intro i
  by_cases hi : i ∈ active
  · let direction := directions ⟨i, hi⟩
    have hweak := (tendsto_pi_nhds.mp hlaws) i
    have haffine := (eventually_signedSelectedCellLaw_affine_of_limit_gap source subsequence
      hE i hweak direction.gap direction.first_lt_selector direction.selector_lt_last
      direction.mass_pos).2
    have hmass := tendsto_decodeCell_ownMass_of_limit_gap source subsequence hE i hweak
      direction.gap direction.first_lt_selector direction.selector_lt_last
    filter_upwards [haffine, hmass.eventually (lt_mem_nhds direction.mass_pos)] with k hk hm
    intro cell
    simp only [signedAtomReplacement, atomEndpointReplacement, dite_eq_left hi,
      ite_true]
    rw [conditionalSelectedCellLaw_eq_pure _ i direction.selector hm]
    exact hk (parameters i) (hparameters ⟨i, hi⟩) cell
  · exact Eventually.of_forall fun k cell => by
      simp only [signedAtomReplacement, atomEndpointReplacement, dite_eq_right hi]
      ring

/-- The actual finite source identity derives its affine probabilities internally. -/
theorem eventually_expect_signedAtomReplacement_eq_booleanEndpointInterpolant
    (source : ℕ → ι → FinDist (Option ℕ)) (subsequence : ℕ → ℕ)
    (hE : Tendsto (fun k => (calendar (source (subsequence k))).endpoints) atTop
      (𝓝 limit.endpoints))
    (hlaws : Tendsto (fun k => chartLaw (source (subsequence k))) atTop (𝓝 marginals))
    (active : Finset ι) (atoms : {i // i ∈ active} → WithTop ℝ)
    (directions : ∀ i, SupportedAtomDirection limit (marginals i.1) (atoms i))
    (parameters : ι → ℝ)
    (hparameters : ∀ i : {i // i ∈ active}, |parameters i.1| ≤ (directions i).radius) :
    ∀ᶠ k in atTop, ∀ test : (ι → Cell (source (subsequence k))) → ℝ,
      (FinDist.pi (signedAtomReplacement source active atoms directions
        (fun i => parameters i.1) (subsequence k))).expect test =
      _root_.Math.booleanEndpointInterpolant (fun vertex =>
        (FinDist.pi (atomEndpointReplacement source active atoms directions
          vertex (subsequence k))).expect test) parameters := by
  filter_upwards [eventually_atom_affine source subsequence hE hlaws
    active atoms directions parameters hparameters] with k hk
  intro test
  apply FinDist.expect_pi_eq_booleanEndpointInterpolant_of_affine_prob
    (endpoints := fun i bit => atomEndpointReplacement source active atoms directions
      (fun _ => bit) (subsequence k) i)
  exact hk

private theorem tendsto_atomEndpointMarginals
    (source : ℕ → ι → FinDist (Option ℕ)) (subsequence : ℕ → ℕ)
    (hE : Tendsto (fun k => (calendar (source (subsequence k))).endpoints) atTop
      (𝓝 limit.endpoints))
    (hlaws : Tendsto (fun k => chartLaw (source (subsequence k))) atTop (𝓝 marginals))
    (active : Finset ι) (atoms : {i // i ∈ active} → WithTop ℝ)
    (directions : ∀ i, SupportedAtomDirection limit (marginals i.1) (atoms i))
    (vertex : ι → Bool) :
    Tendsto (fun k i => referenceLaw (source (subsequence k))
      (atomEndpointReplacement source active atoms directions vertex (subsequence k) i))
      atTop (𝓝 (atomEndpointMarginals active atoms directions vertex)) := by
  classical
  apply tendsto_pi_nhds.mpr
  intro i
  have hweak := (tendsto_pi_nhds.mp hlaws) i
  by_cases hi : i ∈ active
  · cases hv : vertex i
    · simpa only [atomEndpointReplacement, atomEndpointMarginals, dite_eq_left hi,
        hv, Bool.false_eq_true, ite_false, chartLaw] using hweak
    · simpa only [atomEndpointReplacement, atomEndpointMarginals, dite_eq_left hi,
        hv, ite_true] using tendsto_referenceLaw_conditionalSelectedCellLaw source
        subsequence hE i hweak (directions ⟨i, hi⟩).gap
        (directions ⟨i, hi⟩).first_lt_selector (directions ⟨i, hi⟩).selector_lt_last
        (directions ⟨i, hi⟩).mass_pos
  · simpa only [atomEndpointReplacement, atomEndpointMarginals, dite_eq_right hi,
      chartLaw] using hweak

private def atomEndpointBound (active : Finset ι)
    (atoms : {i // i ∈ active} → WithTop ℝ)
    (directions : ∀ i, SupportedAtomDirection limit (marginals i.1) (atoms i))
    (i : ι) : NNReal :=
  if hi : i ∈ active then
    ⟨max (Fintype.card ι : ℝ)
      ((2 / (marginals i : Measure unitInterval).real (directions ⟨i, hi⟩).event) *
        Fintype.card ι), le_max_of_le_left (Nat.cast_nonneg _)⟩
  else ⟨Fintype.card ι, Nat.cast_nonneg _⟩

private theorem eventually_atomEndpoint_weights
    (source : ℕ → ι → FinDist (Option ℕ)) (subsequence : ℕ → ℕ)
    (hE : Tendsto (fun k => (calendar (source (subsequence k))).endpoints) atTop
      (𝓝 limit.endpoints))
    (hlaws : Tendsto (fun k => chartLaw (source (subsequence k))) atTop (𝓝 marginals))
    (active : Finset ι) (atoms : {i // i ∈ active} → WithTop ℝ)
    (directions : ∀ i, SupportedAtomDirection limit (marginals i.1) (atoms i)) :
    ∀ᶠ k in atTop, ∀ vertex i cell,
      (atomEndpointReplacement source active atoms directions vertex (subsequence k) i).prob
        cell ≤ (atomEndpointBound active atoms directions i : ℝ) *
          weight (source (subsequence k)) cell := by
  classical
  have howner : ∀ i, ∀ᶠ k in atTop, ∀ vertex cell,
      (atomEndpointReplacement source active atoms directions vertex (subsequence k) i).prob
        cell ≤ (atomEndpointBound active atoms directions i : ℝ) *
          weight (source (subsequence k)) cell := by
    intro i
    by_cases hi : i ∈ active
    · have hconditional := eventually_conditionalSelectedCellLaw_le source subsequence hE i
        ((tendsto_pi_nhds.mp hlaws) i) (directions ⟨i, hi⟩).gap
        (directions ⟨i, hi⟩).first_lt_selector (directions ⟨i, hi⟩).selector_lt_last
        (directions ⟨i, hi⟩).mass_pos
      filter_upwards [hconditional] with k hk
      intro vertex cell
      have hnonneg := (weight_pos (source (subsequence k)) cell).le
      have hbound : (atomEndpointBound active atoms directions i : ℝ) =
          max (Fintype.card ι : ℝ)
            ((2 / (marginals i : Measure unitInterval).real (directions ⟨i, hi⟩).event) *
              Fintype.card ι) := by
        simp [atomEndpointBound, hi]
        rfl
      rw [hbound]
      cases hv : vertex i
      · simp only [atomEndpointReplacement, dite_eq_left hi,
          hv, Bool.false_eq_true, ite_false, cellLaw_prob]
        exact (ownWeight_le _ i _).trans
          (mul_le_mul_of_nonneg_right (le_max_left _ _) hnonneg)
      · simp only [atomEndpointReplacement, dite_eq_left hi, hv, ite_true]
        exact (hk cell).trans
          (mul_le_mul_of_nonneg_right (le_max_right _ _) hnonneg)
    · exact Eventually.of_forall fun k vertex cell => by
        have hbound : (atomEndpointBound active atoms directions i : ℝ) = Fintype.card ι := by
          simp [atomEndpointBound, hi]
          rfl
        rw [hbound]
        simpa only [atomEndpointReplacement, dite_eq_right hi, cellLaw_prob] using
          ownWeight_le (source (subsequence k)) i cell
  filter_upwards [eventually_all.mpr howner] with k hk
  exact fun vertex i cell => hk i vertex cell

private def cellPayoff (laws : ι → FinDist (Option ℕ)) (reward : Finset ι → ℝ)
    (sample : ι → Cell laws) : ℝ :=
  reward (outcomeLabelsEquiv
    (quittingFirstStoppingOutcome (fun i => originalChoice (sample i))))

private def cellReplyPayoff (laws : ι → FinDist (Option ℕ)) (who : ι)
    (choice : Option ℕ) (reward : Finset ι → ℝ) (sample : ι → Cell laws) : ℝ :=
  reward (outcomeLabelsEquiv (quittingFirstStoppingOutcome
    (Function.update (fun i => originalChoice (sample i)) who choice)))

omit [DecidableEq ι] in
private theorem expect_cellPayoff (laws : ι → FinDist (Option ℕ))
    (p : ι → FinDist (Cell laws)) (reward : Finset ι → ℝ) :
    (FinDist.pi p).expect (cellPayoff laws reward) =
      ((FinDist.pi (fun i => referenceOriginalLaw laws (p i))).map
        quittingFirstStoppingOutcome).expect
        (fun outcome => reward (outcomeLabelsEquiv outcome)) := by
  rw [← referenceCellProduct_map_originalChoice, FinDist.map_comp, FinDist.expect_map]
  rfl

private theorem referenceCellProduct_map_update (laws : ι → FinDist (Option ℕ))
    (p : ι → FinDist (Cell laws)) (who : ι) (choice : Option ℕ) :
    (FinDist.pi p).map (fun sample =>
      Function.update (fun i => originalChoice (sample i)) who choice) =
      FinDist.pi (Function.update (fun i => referenceOriginalLaw laws (p i))
        who (FinDist.pure choice)) := by
  classical
  let read := fun i (cell : Cell laws) => if i = who then choice else originalChoice cell
  have hread : (fun sample : ι → Cell laws =>
      Function.update (fun i => originalChoice (sample i)) who choice) =
      (fun (sample : ι → Cell laws) i => read i (sample i)) := by
    funext sample i
    simp only [read, Function.update_apply]
  rw [hread, ← FinDist.pi_map]
  apply congrArg FinDist.pi
  funext i
  by_cases hi : i = who
  · subst i
    simp only [read, ite_true, Function.update_self, FinDist.map_const]
  · simp only [read, hi, ite_false, Function.update_of_ne hi, referenceOriginalLaw]

private theorem expect_cellReplyPayoff (laws : ι → FinDist (Option ℕ))
    (p : ι → FinDist (Cell laws)) (who : ι) (choice : Option ℕ)
    (reward : Finset ι → ℝ) :
    (FinDist.pi p).expect (cellReplyPayoff laws who choice reward) =
      ((FinDist.pi (Function.update (fun i => referenceOriginalLaw laws (p i))
        who (FinDist.pure choice))).map quittingFirstStoppingOutcome).expect
        (fun outcome => reward (outcomeLabelsEquiv outcome)) := by
  rw [← referenceCellProduct_map_update, FinDist.map_comp, FinDist.expect_map]
  rfl

omit [DecidableEq ι] [Nonempty ι] in
private theorem interpolation_of_source_limits (parameters : ι → ℝ)
    (values : ℕ → ℝ) (coefficients : ℕ → (ι → Bool) → ℝ)
    (value : ℝ) (endpoint : (ι → Bool) → ℝ)
    (hidentity : ∀ᶠ k in atTop,
      values k = _root_.Math.booleanEndpointInterpolant (coefficients k) parameters)
    (hvalue : Tendsto values atTop (𝓝 value))
    (hendpoints : ∀ vertex, Tendsto (fun k => coefficients k vertex) atTop
      (𝓝 (endpoint vertex))) :
    value = _root_.Math.booleanEndpointInterpolant endpoint parameters := by
  classical
  have hpoly : Tendsto
      (fun k => _root_.Math.booleanEndpointInterpolant (coefficients k) parameters) atTop
      (𝓝 (_root_.Math.booleanEndpointInterpolant endpoint parameters)) := by
    unfold _root_.Math.booleanEndpointInterpolant
    exact tendsto_finsetSum Finset.univ fun vertex _ =>
      (hendpoints vertex).mul_const (_root_.Math.booleanEndpointWeight vertex parameters)
  exact tendsto_nhds_unique hvalue (hpoly.congr' (hidentity.mono fun _ h => h.symm))

private def signedAtomBound : ι → NNReal :=
  fun _ => ⟨(3 / 2 : ℝ) * Fintype.card ι, by positivity⟩

/-- Literal prescribed payoff of the actual limiting legal signed family. The endpoint
coefficients use the same actual ordinary conditioning, including an empty active set. -/
theorem signedAtom_payoff_eq_booleanEndpointInterpolant
    (source : ℕ → ι → FinDist (Option ℕ)) (subsequence : ℕ → ℕ)
    (hE : Tendsto (fun k => (calendar (source (subsequence k))).endpoints) atTop
      (𝓝 limit.endpoints))
    (hc : Tendsto (fun k => cutoff (source (subsequence k))) atTop (𝓝 limit.cutoff))
    (hlaws : Tendsto (fun k => chartLaw (source (subsequence k))) atTop (𝓝 marginals))
    (active : Finset ι) (atoms : {i // i ∈ active} → WithTop ℝ)
    (directions : ∀ i, SupportedAtomDirection limit (marginals i.1) (atoms i))
    (parameters : ι → ℝ)
    (hparameters : ∀ i : {i // i ∈ active}, |parameters i.1| ≤ (directions i).radius)
    (reward : Finset ι → ℝ) :
    (∫ sample, MathUE.MarkedCalendar.payoffKernel limit reward sample
      ∂(ProbabilityMeasure.pi (signedAtomMarginals active atoms directions
        (fun i => parameters i.1) hparameters) : Measure (ι → unitInterval))) =
      _root_.Math.booleanEndpointInterpolant (fun vertex =>
        ∫ sample, MathUE.MarkedCalendar.payoffKernel limit reward sample
          ∂(ProbabilityMeasure.pi (atomEndpointMarginals active atoms directions vertex) :
            Measure (ι → unitInterval))) parameters := by
  let replacement := signedAtomReplacement source active atoms directions
    (fun i => parameters i.1)
  have hfinite := eventually_expect_signedAtomReplacement_eq_booleanEndpointInterpolant
    source subsequence hE hlaws active atoms directions parameters hparameters
  have hweights : ∀ᶠ k in atTop, ∀ i cell,
      (replacement (subsequence k) i).prob cell ≤
        (signedAtomBound i : ℝ) * weight (source (subsequence k)) cell :=
    Eventually.of_forall fun k i cell =>
      prob_signedAtomReplacement_le source active atoms directions
        (fun i => parameters i.1) (subsequence k) i cell
  have hvalue := tendsto_reference_outcome_expect source replacement subsequence hE hc
    signedAtomBound hweights (tendsto_referenceLaw_signedAtomReplacement source subsequence
      hE hlaws active atoms directions (fun i => parameters i.1) hparameters) reward
  refine interpolation_of_source_limits parameters _ (fun k vertex =>
    ((FinDist.pi (fun i => referenceOriginalLaw (source (subsequence k))
      (atomEndpointReplacement source active atoms directions vertex (subsequence k) i))).map
        quittingFirstStoppingOutcome).expect
      (fun outcome => reward (outcomeLabelsEquiv outcome))) _ _ ?_ hvalue ?_
  · filter_upwards [hfinite] with k hk
    simpa only [expect_cellPayoff] using hk (cellPayoff (source (subsequence k)) reward)
  · intro vertex
    exact tendsto_reference_outcome_expect source
      (atomEndpointReplacement source active atoms directions vertex) subsequence hE hc
      (atomEndpointBound active atoms directions)
      ((eventually_atomEndpoint_weights source subsequence hE hlaws active atoms directions).mono
        fun k hk => hk vertex)
      (tendsto_atomEndpointMarginals source subsequence hE hlaws active atoms directions vertex)
      reward

/-- Every selected finite response whose actual old-chart marks converge has the same
ordinary endpoint interpolation. This does not identify a maximizing response or a cap. -/
theorem signedAtom_finite_reply_eq_booleanEndpointInterpolant
    (source : ℕ → ι → FinDist (Option ℕ)) (subsequence : ℕ → ℕ)
    (hE : Tendsto (fun k => (calendar (source (subsequence k))).endpoints) atTop
      (𝓝 limit.endpoints))
    (hc : Tendsto (fun k => cutoff (source (subsequence k))) atTop (𝓝 limit.cutoff))
    (hlaws : Tendsto (fun k => chartLaw (source (subsequence k))) atTop (𝓝 marginals))
    (active : Finset ι) (atoms : {i // i ∈ active} → WithTop ℝ)
    (directions : ∀ i, SupportedAtomDirection limit (marginals i.1) (atoms i))
    (parameters : ι → ℝ)
    (hparameters : ∀ i : {i // i ∈ active}, |parameters i.1| ≤ (directions i).radius)
    (who : ι) (reward : Finset ι → ℝ) (dates : ℕ → ℕ) {t : ℝ}
    (ht : Tendsto (fun k => mark (source (subsequence k)) (dates k)) atTop (𝓝 t)) :
    (∫ sample, MathUE.MarkedCalendar.responsePayoffKernel limit who (t : WithTop ℝ)
      reward sample ∂(ProbabilityMeasure.pi (fun j : {j : ι // j ≠ who} =>
        signedAtomMarginals active atoms directions (fun i => parameters i.1) hparameters j.1) :
          Measure ({j : ι // j ≠ who} → unitInterval))) =
      _root_.Math.booleanEndpointInterpolant (fun vertex =>
        ∫ sample, MathUE.MarkedCalendar.responsePayoffKernel limit who (t : WithTop ℝ)
          reward sample ∂(ProbabilityMeasure.pi (fun j : {j : ι // j ≠ who} =>
            atomEndpointMarginals active atoms directions vertex j.1) :
              Measure ({j : ι // j ≠ who} → unitInterval))) parameters := by
  let replacement := signedAtomReplacement source active atoms directions
    (fun i => parameters i.1)
  have hfinite := eventually_expect_signedAtomReplacement_eq_booleanEndpointInterpolant
    source subsequence hE hlaws active atoms directions parameters hparameters
  have hweights : ∀ᶠ k in atTop, ∀ i cell,
      (replacement (subsequence k) i).prob cell ≤
        (signedAtomBound i : ℝ) * weight (source (subsequence k)) cell :=
    Eventually.of_forall fun k i cell =>
      prob_signedAtomReplacement_le source active atoms directions
        (fun i => parameters i.1) (subsequence k) i cell
  have hvalue := tendsto_reference_finite_reply_expect source replacement subsequence hE hc
    signedAtomBound hweights (tendsto_referenceLaw_signedAtomReplacement source subsequence
      hE hlaws active atoms directions (fun i => parameters i.1) hparameters) who reward dates ht
  refine interpolation_of_source_limits parameters _ (fun k vertex =>
    ((FinDist.pi (Function.update (fun i => referenceOriginalLaw (source (subsequence k))
      (atomEndpointReplacement source active atoms directions vertex (subsequence k) i))
        who (FinDist.pure (some (dates k))))).map quittingFirstStoppingOutcome).expect
      (fun outcome => reward (outcomeLabelsEquiv outcome))) _ _ ?_ hvalue ?_
  · filter_upwards [hfinite] with k hk
    simpa only [expect_cellReplyPayoff] using
      hk (cellReplyPayoff (source (subsequence k)) who (some (dates k)) reward)
  · intro vertex
    exact tendsto_reference_finite_reply_expect source
      (atomEndpointReplacement source active atoms directions vertex) subsequence hE hc
      (atomEndpointBound active atoms directions)
      ((eventually_atomEndpoint_weights source subsequence hE hlaws active atoms directions).mono
        fun k hk => hk vertex)
      (tendsto_atomEndpointMarginals source subsequence hE hlaws active atoms directions vertex)
      who reward dates ht

/-- Literal Never is separate from the finite cutoff and has the same ordinary endpoint
coefficients. The algebraic all-one response is selected, not an actual full cap. -/
theorem signedAtom_never_reply_eq_booleanEndpointInterpolant
    (source : ℕ → ι → FinDist (Option ℕ)) (subsequence : ℕ → ℕ)
    (hE : Tendsto (fun k => (calendar (source (subsequence k))).endpoints) atTop
      (𝓝 limit.endpoints))
    (hc : Tendsto (fun k => cutoff (source (subsequence k))) atTop (𝓝 limit.cutoff))
    (hlaws : Tendsto (fun k => chartLaw (source (subsequence k))) atTop (𝓝 marginals))
    (active : Finset ι) (atoms : {i // i ∈ active} → WithTop ℝ)
    (directions : ∀ i, SupportedAtomDirection limit (marginals i.1) (atoms i))
    (parameters : ι → ℝ)
    (hparameters : ∀ i : {i // i ∈ active}, |parameters i.1| ≤ (directions i).radius)
    (who : ι) (reward : Finset ι → ℝ) :
    (∫ sample, MathUE.MarkedCalendar.responsePayoffKernel limit who ⊤ reward sample
      ∂(ProbabilityMeasure.pi (fun j : {j : ι // j ≠ who} =>
        signedAtomMarginals active atoms directions (fun i => parameters i.1) hparameters j.1) :
          Measure ({j : ι // j ≠ who} → unitInterval))) =
      _root_.Math.booleanEndpointInterpolant (fun vertex =>
        ∫ sample, MathUE.MarkedCalendar.responsePayoffKernel limit who ⊤ reward sample
          ∂(ProbabilityMeasure.pi (fun j : {j : ι // j ≠ who} =>
            atomEndpointMarginals active atoms directions vertex j.1) :
              Measure ({j : ι // j ≠ who} → unitInterval))) parameters := by
  let replacement := signedAtomReplacement source active atoms directions
    (fun i => parameters i.1)
  have hfinite := eventually_expect_signedAtomReplacement_eq_booleanEndpointInterpolant
    source subsequence hE hlaws active atoms directions parameters hparameters
  have hweights : ∀ᶠ k in atTop, ∀ i cell,
      (replacement (subsequence k) i).prob cell ≤
        (signedAtomBound i : ℝ) * weight (source (subsequence k)) cell :=
    Eventually.of_forall fun k i cell =>
      prob_signedAtomReplacement_le source active atoms directions
        (fun i => parameters i.1) (subsequence k) i cell
  have hvalue := tendsto_reference_never_reply_expect source replacement subsequence hE hc
    signedAtomBound hweights (tendsto_referenceLaw_signedAtomReplacement source subsequence
      hE hlaws active atoms directions (fun i => parameters i.1) hparameters) who reward
  refine interpolation_of_source_limits parameters _ (fun k vertex =>
    ((FinDist.pi (Function.update (fun i => referenceOriginalLaw (source (subsequence k))
      (atomEndpointReplacement source active atoms directions vertex (subsequence k) i))
        who (FinDist.pure none))).map quittingFirstStoppingOutcome).expect
      (fun outcome => reward (outcomeLabelsEquiv outcome))) _ _ ?_ hvalue ?_
  · filter_upwards [hfinite] with k hk
    simpa only [expect_cellReplyPayoff] using
      hk (cellReplyPayoff (source (subsequence k)) who none reward)
  · intro vertex
    exact tendsto_reference_never_reply_expect source
      (atomEndpointReplacement source active atoms directions vertex) subsequence hE hc
      (atomEndpointBound active atoms directions)
      ((eventually_atomEndpoint_weights source subsequence hE hlaws active atoms directions).mono
        fun k hk => hk vertex)
      (tendsto_atomEndpointMarginals source subsequence hE hlaws active atoms directions vertex)
      who reward

end GameTheory.MarkedCalendarChart
