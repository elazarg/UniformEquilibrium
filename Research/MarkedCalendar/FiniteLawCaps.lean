import Research.MarkedCalendar.FiniteLawGeometry
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Constructions.SumProd

/-! # Responses on the actual limiting marked menu

Finite replies are points of the actual limiting menu. Never is a separate
isolated summand, not the finite cutoff. The response function integrates the
actual first-coalition kernel against the independent limiting chart laws.
Its continuity and attained maximum follow from the actual source geometry,
domination, and checked moving-kernel convergence, without density constancy.
The bounded-marginal versions require no marginal convergence premise.

The source dictionary identifies this maximum with the existing unrestricted
stopping-law cap. Its reward extension assigns empty labels zero, and its clock
dictionary covers every original finite date and literal Never. Complete caps
for arbitrary finite replacement laws on the old cells also have this exact
old-menu representation; no replacement average calendar is substituted. Original caps
converge along the whole specified source subsequence. One actual-source
compactification is selected before all reward tables and players, and carries
both the original prescribed-payoff limits and these complete-cap limits.
Original semantic-carrier minima and signed old-law variations remain separate
consumers of this producer.
-/

noncomputable section

open Set Filter MeasureTheory TopologicalSpace GameTheory.Math.Probability
open scoped Topology BigOperators

namespace GameTheory.MarkedCalendarChart

/-- The finite cutoff lies in the left summand; Never is the right summand. -/
abbrev LimitReply (menu : NonemptyCompacts ℝ) := menu ⊕ Unit

def limitReplyClock (menu : NonemptyCompacts ℝ) : LimitReply menu → WithTop ℝ :=
  Sum.elim (fun t => (t.val : WithTop ℝ)) (fun _ => ⊤)

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]

def responseValue (C : MathUE.MarkedCalendar.Calendar)
    (marginals : ι → ProbabilityMeasure unitInterval) (who : ι)
    (reward : Finset ι → ℝ) (clock : WithTop ℝ) : ℝ :=
  ∫ sample, MathUE.MarkedCalendar.responsePayoffKernel C who clock reward sample
    ∂(ProbabilityMeasure.pi (fun j : {j : ι // j ≠ who} => marginals j.val) :
      Measure ({j : ι // j ≠ who} → unitInterval))

def limitReplyValue (C : MathUE.MarkedCalendar.Calendar) (menu : NonemptyCompacts ℝ)
    (marginals : ι → ProbabilityMeasure unitInterval) (who : ι)
    (reward : Finset ι → ℝ) (reply : LimitReply menu) : ℝ :=
  responseValue C marginals who reward (limitReplyClock menu reply)

def limitReplyMaximum (C : MathUE.MarkedCalendar.Calendar) (menu : NonemptyCompacts ℝ)
    (marginals : ι → ProbabilityMeasure unitInterval) (who : ι)
    (reward : Finset ι → ℝ) : ℝ :=
  sSup (Set.range (limitReplyValue C menu marginals who reward))

private instance base_nullSingleton : NullSingletonClass (base : Measure unitInterval) :=
  inferInstanceAs (NullSingletonClass (volume : Measure unitInterval))

/-- Every finite response sequence inside the actual limit menu has the correct response limit. -/
theorem continuous_responseValue_limit_menu_of_le_smul
    (source : ℕ → ι → FinDist (Option ℕ)) (subsequence : ℕ → ℕ)
    {limit : MathUE.MarkedCalendar.Calendar} {menu : NonemptyCompacts ℝ}
    {marginals : ι → ProbabilityMeasure unitInterval}
    (hE : Tendsto (fun k => (calendar (source (subsequence k))).endpoints) atTop
      (𝓝 limit.endpoints))
    (hc : Tendsto (fun k => cutoff (source (subsequence k))) atTop (𝓝 limit.cutoff))
    (hT : Tendsto (fun k => legalMenuCompacts (source (subsequence k))) atTop (𝓝 menu))
    (C : ι → NNReal) (who : ι)
    (hbound : ∀ j : {j : ι // j ≠ who},
      (marginals j.val : Measure unitInterval) ≤ C j.val • (base : Measure unitInterval))
    (reward : Finset ι → ℝ) :
    Continuous (fun t : menu => responseValue limit marginals who reward (t.val : WithTop ℝ)) := by
  have hproductBound := ProbabilityMeasure.pi_le_smul_pi_of_le
    (fun _ : {j : ι // j ≠ who} => base)
    (fun j : {j : ι // j ≠ who} => marginals j.val)
    (fun j : {j : ι // j ≠ who} => C j.val)
    hbound
  apply continuous_iff_seqContinuous.mpr
  intro tests t ht
  have htests : Tendsto (fun k => (tests k).val) atTop (𝓝 t.val) :=
    continuous_subtype_val.continuousAt.tendsto.comp ht
  have herror := MathUE.MarkedCalendar.tendsto_integral_norm_responsePayoffKernel_sub base
    (calendars := fun _ => limit) tendsto_const_nhds tendsto_const_nhds htests
    (fun k => atomCompatible_of_mem_limit_menu source subsequence hE hc hT (tests k).property)
    who reward
  have h := ProbabilityMeasure.tendsto_integral_moving_test_of_tendsto_of_le_smul
    (ProbabilityMeasure.pi (fun _ : {j : ι // j ≠ who} => base))
    (∏ j : {j : ι // j ≠ who}, C j.val)
    (laws := fun _ : ℕ => ProbabilityMeasure.pi
      (fun j : {j : ι // j ≠ who} => marginals j.val))
    tendsto_const_nhds (Eventually.of_forall fun _ => hproductBound)
    (MathUE.MarkedCalendar.responsePayoffKernel limit who (t.val : WithTop ℝ) reward)
    (MathUE.MarkedCalendar.integrable_responsePayoffKernel limit who _ reward _)
    (fun k => MathUE.MarkedCalendar.responsePayoffKernel limit who
      ((tests k).val : WithTop ℝ) reward)
    (Eventually.of_forall fun _ =>
      MathUE.MarkedCalendar.integrable_responsePayoffKernel limit who _ reward _) herror
  exact h

/-- Never is continuous as an isolated summand; no unrestricted `WithTop` isolation is used. -/
theorem continuous_limitReplyValue_of_le_smul
    (source : ℕ → ι → FinDist (Option ℕ)) (subsequence : ℕ → ℕ)
    {limit : MathUE.MarkedCalendar.Calendar} {menu : NonemptyCompacts ℝ}
    {marginals : ι → ProbabilityMeasure unitInterval}
    (hE : Tendsto (fun k => (calendar (source (subsequence k))).endpoints) atTop
      (𝓝 limit.endpoints))
    (hc : Tendsto (fun k => cutoff (source (subsequence k))) atTop (𝓝 limit.cutoff))
    (hT : Tendsto (fun k => legalMenuCompacts (source (subsequence k))) atTop (𝓝 menu))
    (C : ι → NNReal) (who : ι)
    (hbound : ∀ j : {j : ι // j ≠ who},
      (marginals j.val : Measure unitInterval) ≤ C j.val • (base : Measure unitInterval))
    (reward : Finset ι → ℝ) :
    Continuous (limitReplyValue limit menu marginals who reward) := by
  apply continuous_sum_dom.mpr
  constructor
  · exact continuous_responseValue_limit_menu_of_le_smul
      source subsequence hE hc hT C who hbound reward
  · change Continuous (fun _ : Unit => responseValue limit marginals who reward ⊤)
    exact continuous_const

/-- The actual limiting finite/Never response carrier has an attained response maximum. -/
theorem exists_limitReplyValue_eq_maximum_of_le_smul
    (source : ℕ → ι → FinDist (Option ℕ)) (subsequence : ℕ → ℕ)
    {limit : MathUE.MarkedCalendar.Calendar} {menu : NonemptyCompacts ℝ}
    {marginals : ι → ProbabilityMeasure unitInterval}
    (hE : Tendsto (fun k => (calendar (source (subsequence k))).endpoints) atTop
      (𝓝 limit.endpoints))
    (hc : Tendsto (fun k => cutoff (source (subsequence k))) atTop (𝓝 limit.cutoff))
    (hT : Tendsto (fun k => legalMenuCompacts (source (subsequence k))) atTop (𝓝 menu))
    (C : ι → NNReal) (who : ι)
    (hbound : ∀ j : {j : ι // j ≠ who},
      (marginals j.val : Measure unitInterval) ≤ C j.val • (base : Measure unitInterval))
    (reward : Finset ι → ℝ) :
    ∃ reply : LimitReply menu,
      limitReplyValue limit menu marginals who reward reply =
        limitReplyMaximum limit menu marginals who reward ∧
      ∀ other, limitReplyValue limit menu marginals who reward other ≤
        limitReplyValue limit menu marginals who reward reply := by
  obtain ⟨reply, _, hmax⟩ := isCompact_univ.exists_isMaxOn
    (s := (univ : Set (LimitReply menu))) univ_nonempty
    (continuous_limitReplyValue_of_le_smul
      source subsequence hE hc hT C who hbound reward).continuousOn
  have hgreatest : IsGreatest
      (Set.range (limitReplyValue limit menu marginals who reward))
      (limitReplyValue limit menu marginals who reward reply) := by
    refine ⟨⟨reply, rfl⟩, ?_⟩
    rintro _ ⟨other, rfl⟩
    exact hmax (mem_univ other)
  exact ⟨reply, hgreatest.csSup_eq.symm, fun other => hmax (mem_univ other)⟩

/-- Original limiting charts supply the marginal bound to the one continuity proof. -/
theorem continuous_responseValue_limit_menu
    (source : ℕ → ι → FinDist (Option ℕ)) (subsequence : ℕ → ℕ)
    {limit : MathUE.MarkedCalendar.Calendar} {menu : NonemptyCompacts ℝ}
    {marginals : ι → ProbabilityMeasure unitInterval}
    (hE : Tendsto (fun k => (calendar (source (subsequence k))).endpoints) atTop
      (𝓝 limit.endpoints))
    (hc : Tendsto (fun k => cutoff (source (subsequence k))) atTop (𝓝 limit.cutoff))
    (hT : Tendsto (fun k => legalMenuCompacts (source (subsequence k))) atTop (𝓝 menu))
    (hlaws : Tendsto (fun k => chartLaw (source (subsequence k))) atTop (𝓝 marginals))
    (who : ι) (reward : Finset ι → ℝ) :
    Continuous (fun t : menu => responseValue limit marginals who reward (t.val : WithTop ℝ)) :=
  continuous_responseValue_limit_menu_of_le_smul source subsequence hE hc hT
    (fun _ => (Fintype.card ι : NNReal)) who
    (fun j => ProbabilityMeasure.le_of_tendsto_of_le_measure _ (hlaws.apply_nhds j.val)
      (Eventually.of_forall fun k => chartLaw_le (source (subsequence k)) j.val)) reward

theorem continuous_limitReplyValue
    (source : ℕ → ι → FinDist (Option ℕ)) (subsequence : ℕ → ℕ)
    {limit : MathUE.MarkedCalendar.Calendar} {menu : NonemptyCompacts ℝ}
    {marginals : ι → ProbabilityMeasure unitInterval}
    (hE : Tendsto (fun k => (calendar (source (subsequence k))).endpoints) atTop
      (𝓝 limit.endpoints))
    (hc : Tendsto (fun k => cutoff (source (subsequence k))) atTop (𝓝 limit.cutoff))
    (hT : Tendsto (fun k => legalMenuCompacts (source (subsequence k))) atTop (𝓝 menu))
    (hlaws : Tendsto (fun k => chartLaw (source (subsequence k))) atTop (𝓝 marginals))
    (who : ι) (reward : Finset ι → ℝ) :
    Continuous (limitReplyValue limit menu marginals who reward) :=
  continuous_limitReplyValue_of_le_smul source subsequence hE hc hT
    (fun _ => (Fintype.card ι : NNReal)) who
    (fun j => ProbabilityMeasure.le_of_tendsto_of_le_measure _ (hlaws.apply_nhds j.val)
      (Eventually.of_forall fun k => chartLaw_le (source (subsequence k)) j.val)) reward

theorem exists_limitReplyValue_eq_maximum
    (source : ℕ → ι → FinDist (Option ℕ)) (subsequence : ℕ → ℕ)
    {limit : MathUE.MarkedCalendar.Calendar} {menu : NonemptyCompacts ℝ}
    {marginals : ι → ProbabilityMeasure unitInterval}
    (hE : Tendsto (fun k => (calendar (source (subsequence k))).endpoints) atTop
      (𝓝 limit.endpoints))
    (hc : Tendsto (fun k => cutoff (source (subsequence k))) atTop (𝓝 limit.cutoff))
    (hT : Tendsto (fun k => legalMenuCompacts (source (subsequence k))) atTop (𝓝 menu))
    (hlaws : Tendsto (fun k => chartLaw (source (subsequence k))) atTop (𝓝 marginals))
    (who : ι) (reward : Finset ι → ℝ) :
    ∃ reply : LimitReply menu,
      limitReplyValue limit menu marginals who reward reply =
        limitReplyMaximum limit menu marginals who reward ∧
      ∀ other, limitReplyValue limit menu marginals who reward other ≤
        limitReplyValue limit menu marginals who reward reply :=
  exists_limitReplyValue_eq_maximum_of_le_smul source subsequence hE hc hT
    (fun _ => (Fintype.card ι : NNReal)) who
    (fun j => ProbabilityMeasure.le_of_tendsto_of_le_measure _ (hlaws.apply_nhds j.val)
      (Eventually.of_forall fun k => chartLaw_le (source (subsequence k)) j.val)) reward

/-- Extend actual quitting rewards by zero at the empty labels, which encode Never. -/
def quittingLabelReward (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (who : ι) (coalition : Finset ι) : ℝ :=
  quittingTerminalOutcomeReward reward (outcomeLabelsEquiv.symm coalition) who

omit [Fintype ι] [Nonempty ι] [DecidableEq ι] in
@[simp] theorem quittingLabelReward_empty
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (who : ι) :
    quittingLabelReward reward who ∅ = 0 := by
  have hnone : outcomeLabelsEquiv.symm (∅ : Finset ι) = none := by
    apply outcomeLabelsEquiv.injective
    simp only [Equiv.apply_symm_apply, outcomeLabelsEquiv_apply, Option.elim_none]
  rw [quittingLabelReward, hnone]
  rfl

omit [DecidableEq ι] in
/-- The finite-law expectation is the original complete stopping-law payoff. -/
theorem sourceOutcome_expect_eq_stoppingLawExpectedPayoff
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (laws : ι → FinDist (Option ℕ)) (who : ι) :
    ((FinDist.pi laws).map quittingFirstStoppingOutcome).expect
        (fun outcome => quittingLabelReward reward who (outcomeLabelsEquiv outcome)) =
      quittingStoppingLawExpectedPayoff reward (fun i => (laws i).toPMF) who := by
  have hproduct : (FinDist.pi laws).toPMF =
      Math.PMFProduct.pmfPi (fun i => (laws i).toPMF) := rfl
  unfold quittingStoppingLawExpectedPayoff quittingIndependentTerminalOutcomeLaw
  rw [← hproduct, PMF.map, Function.comp_def, ← FinDist.toPMF_map]
  simp only [quittingLabelReward, Equiv.symm_apply_apply]
  rfl

/-- Every original response has its exact replacement-law payoff at the old reference mark. -/
theorem responseValue_reference_markedClock_eq_original_pureReply
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (reference : ι → FinDist (Option ℕ)) (p : ι → FinDist (Cell reference))
    (who : ι) (choice : Option ℕ) :
    responseValue (calendar reference) (fun i => referenceLaw reference (p i)) who
        (quittingLabelReward reward who)
        (markedClock reference (quittingStoppingTimeValue choice)) =
      quittingBehaviorPureTimePayoff reward
        (quittingStoppingLawProfile reward
          (fun i => (referenceOriginalLaw reference (p i)).toPMF)) who choice := by
  let laws := fun i => referenceOriginalLaw reference (p i)
  rw [responseValue, integral_responsePayoffKernel_referenceOpponents,
    sourceOutcome_expect_eq_stoppingLawExpectedPayoff]
  have hupdate : (fun i => (Function.update laws who (FinDist.pure choice) i).toPMF) =
      Function.update (fun i => (laws i).toPMF) who (PMF.pure choice) := by
    funext i
    by_cases hi : i = who
    · subst i
      simp only [Function.update_self, FinDist.toPMF_pure]
    · simp only [Function.update_of_ne hi]
  rw [hupdate, ← quittingTerminalPayoff_stoppingLawProfile_eq_expectedPayoff,
    quittingTerminalPayoff_stoppingLawProfile_update_pure_eq]
  rfl

/-- The original source laws specialize the exact old-reference response dictionary. -/
theorem responseValue_markedClock_eq_original_pureReply
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (laws : ι → FinDist (Option ℕ)) (who : ι) (choice : Option ℕ) :
    responseValue (calendar laws) (chartLaw laws) who (quittingLabelReward reward who)
        (markedClock laws (quittingStoppingTimeValue choice)) =
      quittingBehaviorPureTimePayoff reward
        (quittingStoppingLawProfile reward (fun i => (laws i).toPMF)) who choice := by
  change responseValue (calendar laws) (fun i => referenceLaw laws (cellLaw laws i)) who
    (quittingLabelReward reward who) (markedClock laws (quittingStoppingTimeValue choice)) = _
  simpa only [referenceOriginalLaw_cellLaw] using
    responseValue_reference_markedClock_eq_original_pureReply reward laws (cellLaw laws) who choice

/-- The image of every original pure response in the actual finite/Never chart carrier. -/
def sourceReply (laws : ι → FinDist (Option ℕ)) :
    Option ℕ → LimitReply (legalMenuCompacts laws)
  | none => Sum.inr ()
  | some time => Sum.inl ⟨mark laws time, by
      change mark laws time ∈ (legalFiniteMenu laws : Set ℝ)
      rw [← range_mark_eq_legalFiniteMenu]
      exact ⟨time, rfl⟩⟩

omit [DecidableEq ι] in
theorem sourceReply_clock (laws : ι → FinDist (Option ℕ)) (choice : Option ℕ) :
    limitReplyClock (legalMenuCompacts laws) (sourceReply laws choice) =
      markedClock laws (quittingStoppingTimeValue choice) := by
  cases choice <;> rfl

omit [DecidableEq ι] in
/-- No geometrically compatible but unavailable mark is added to the reply carrier. -/
theorem sourceReply_surjective (laws : ι → FinDist (Option ℕ)) :
    Function.Surjective (sourceReply laws) := by
  intro reply
  cases reply with
  | inl t =>
      have ht : t.val ∈ range (mark laws) := by
        rw [range_mark_eq_legalFiniteMenu]
        exact t.property
      obtain ⟨time, htime⟩ := ht
      refine ⟨some time, ?_⟩
      apply congrArg Sum.inl
      exact Subtype.ext htime
  | inr terminal =>
      cases terminal
      exact ⟨none, rfl⟩

theorem limitReplyValue_reference_sourceReply_eq_original_pureReply
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (reference : ι → FinDist (Option ℕ)) (p : ι → FinDist (Cell reference))
    (who : ι) (choice : Option ℕ) :
    limitReplyValue (calendar reference) (legalMenuCompacts reference)
        (fun i => referenceLaw reference (p i)) who
        (quittingLabelReward reward who) (sourceReply reference choice) =
      quittingBehaviorPureTimePayoff reward
        (quittingStoppingLawProfile reward
          (fun i => (referenceOriginalLaw reference (p i)).toPMF)) who choice := by
  rw [limitReplyValue, sourceReply_clock]
  exact responseValue_reference_markedClock_eq_original_pureReply reward reference p who choice

theorem limitReplyValue_sourceReply_eq_original_pureReply
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (laws : ι → FinDist (Option ℕ)) (who : ι) (choice : Option ℕ) :
    limitReplyValue (calendar laws) (legalMenuCompacts laws) (chartLaw laws) who
        (quittingLabelReward reward who) (sourceReply laws choice) =
      quittingBehaviorPureTimePayoff reward
        (quittingStoppingLawProfile reward (fun i => (laws i).toPMF)) who choice := by
  change limitReplyValue (calendar laws) (legalMenuCompacts laws)
    (fun i => referenceLaw laws (cellLaw laws i)) who
    (quittingLabelReward reward who) (sourceReply laws choice) = _
  simpa only [referenceOriginalLaw_cellLaw] using
    limitReplyValue_reference_sourceReply_eq_original_pureReply
      reward laws (cellLaw laws) who choice

/-- The old reference menu represents the unrestricted original cap for the actual replacement
laws. No support restriction on the deviator and no replacement-calendar equality is assumed. -/
theorem referenceFullCap_eq_replyMaximum
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (reference : ι → FinDist (Option ℕ)) (p : ι → FinDist (Cell reference)) (who : ι) :
    quittingStoppingLawReplacementPayoffCap reward
        (fun i => (referenceOriginalLaw reference (p i)).toPMF) who =
      limitReplyMaximum (calendar reference) (legalMenuCompacts reference)
        (fun i => referenceLaw reference (p i)) who
        (quittingLabelReward reward who) := by
  rw [quittingStoppingLawCap_eq_continuationBestResponseValue_stoppingLawProfile]
  change quittingBehaviorDeviationPayoffCap reward
    (quittingStoppingLawProfile reward
      (fun i => (referenceOriginalLaw reference (p i)).toPMF)) who = _
  rw [quittingBehaviorDeviationPayoffCap_eq_pureTime]
  unfold quittingBehaviorPureTimePayoffCap limitReplyMaximum
  congr 1
  ext value
  constructor
  · rintro ⟨choice, rfl⟩
    exact ⟨sourceReply reference choice,
      limitReplyValue_reference_sourceReply_eq_original_pureReply reward reference p who choice⟩
  · rintro ⟨reply, rfl⟩
    obtain ⟨choice, rfl⟩ := sourceReply_surjective reference reply
    exact ⟨choice,
      (limitReplyValue_reference_sourceReply_eq_original_pureReply
        reward reference p who choice).symm⟩

/-- The original chart maximum specializes the one unrestricted-cap dictionary. -/
theorem sourceFullCap_eq_replyMaximum
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (laws : ι → FinDist (Option ℕ)) (who : ι) :
    quittingStoppingLawReplacementPayoffCap reward (fun i => (laws i).toPMF) who =
      limitReplyMaximum (calendar laws) (legalMenuCompacts laws) (chartLaw laws) who
        (quittingLabelReward reward who) := by
  change quittingStoppingLawReplacementPayoffCap reward (fun i => (laws i).toPMF) who =
    limitReplyMaximum (calendar laws) (legalMenuCompacts laws)
      (fun i => referenceLaw laws (cellLaw laws i)) who (quittingLabelReward reward who)
  simpa only [referenceOriginalLaw_cellLaw] using
    referenceFullCap_eq_replyMaximum reward laws (cellLaw laws) who

/-- A genuine original atom-gap-menu reply attains the unrestricted source cap. -/
theorem exists_original_reply_eq_sourceFullCap
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (laws : ι → FinDist (Option ℕ)) (who : ι) :
    ∃ choice ∈ quittingFiniteOpponentAtomGapReplyMenu (quittingFiniteStoppingCalendar laws),
      quittingBehaviorPureTimePayoff reward
          (quittingStoppingLawProfile reward (fun i => (laws i).toPMF)) who choice =
        quittingStoppingLawReplacementPayoffCap reward (fun i => (laws i).toPMF) who := by
  obtain ⟨choice, hchoice, hvalue⟩ :=
    exists_mem_quittingFiniteOpponentAtomGapReplyMenu_payoff_eq_cap reward
      (fun i => (laws i).toPMF) who (quittingFiniteStoppingCalendar laws) (by
        intro player _ time htime
        exact mem_quittingFiniteStoppingCalendar_of_mem_support laws player time
          ((PMF.mem_support_iff _ _).mpr htime))
  refine ⟨choice, hchoice, ?_⟩
  rw [quittingStoppingLawCap_eq_continuationBestResponseValue_stoppingLawProfile]
  exact hvalue

private theorem source_updated_expect_eq_original_reply
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (laws : ι → FinDist (Option ℕ)) (who : ι) (choice : Option ℕ) :
    ((FinDist.pi (Function.update laws who (FinDist.pure choice))).map
      quittingFirstStoppingOutcome).expect
        (fun outcome => quittingLabelReward reward who (outcomeLabelsEquiv outcome)) =
      quittingBehaviorPureTimePayoff reward
        (quittingStoppingLawProfile reward (fun i => (laws i).toPMF)) who choice :=
  (integral_responsePayoffKernel_chartOpponents laws who choice
    (quittingLabelReward reward who)).symm.trans
      (responseValue_markedClock_eq_original_pureReply reward laws who choice)

private theorem original_reply_le_sourceFullCap
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (laws : ι → FinDist (Option ℕ)) (who : ι) (choice : Option ℕ) :
    quittingBehaviorPureTimePayoff reward
        (quittingStoppingLawProfile reward (fun i => (laws i).toPMF)) who choice ≤
      quittingStoppingLawReplacementPayoffCap reward (fun i => (laws i).toPMF) who := by
  rw [quittingStoppingLawCap_eq_continuationBestResponseValue_stoppingLawProfile]
  exact quittingTerminalPayoff_update_le_continuationBestResponseValue reward _ who _

/-- The moving finite-reply limit is literally the original behavioral payoff. -/
theorem tendsto_original_finite_reply_payoff
    (source : ℕ → ι → FinDist (Option ℕ)) (subsequence : ℕ → ℕ)
    {limit : MathUE.MarkedCalendar.Calendar} {marginals : ι → ProbabilityMeasure unitInterval}
    (hE : Tendsto (fun k => (calendar (source (subsequence k))).endpoints) atTop
      (𝓝 limit.endpoints))
    (hc : Tendsto (fun k => cutoff (source (subsequence k))) atTop (𝓝 limit.cutoff))
    (hlaws : Tendsto (fun k => chartLaw (source (subsequence k))) atTop (𝓝 marginals))
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (who : ι) (dates : ℕ → ℕ)
    {t : ℝ} (ht : Tendsto (fun k => mark (source (subsequence k)) (dates k)) atTop (𝓝 t)) :
    Tendsto (fun k => quittingBehaviorPureTimePayoff reward
      (quittingStoppingLawProfile reward (fun i => (source (subsequence k) i).toPMF))
        who (some (dates k))) atTop
      (𝓝 (responseValue limit marginals who (quittingLabelReward reward who) (t : WithTop ℝ))) :=
  (tendsto_source_finite_reply_expect source subsequence hE hc hlaws who
    (quittingLabelReward reward who) dates ht).congr' (Eventually.of_forall fun k =>
      source_updated_expect_eq_original_reply reward (source (subsequence k)) who (some (dates k)))

/-- The original Never reply retains its separate payoff limit. -/
theorem tendsto_original_never_reply_payoff
    (source : ℕ → ι → FinDist (Option ℕ)) (subsequence : ℕ → ℕ)
    {limit : MathUE.MarkedCalendar.Calendar} {marginals : ι → ProbabilityMeasure unitInterval}
    (hE : Tendsto (fun k => (calendar (source (subsequence k))).endpoints) atTop
      (𝓝 limit.endpoints))
    (hc : Tendsto (fun k => cutoff (source (subsequence k))) atTop (𝓝 limit.cutoff))
    (hlaws : Tendsto (fun k => chartLaw (source (subsequence k))) atTop (𝓝 marginals))
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (who : ι) :
    Tendsto (fun k => quittingBehaviorPureTimePayoff reward
      (quittingStoppingLawProfile reward (fun i => (source (subsequence k) i).toPMF)) who none)
      atTop (𝓝 (responseValue limit marginals who (quittingLabelReward reward who) ⊤)) :=
  (tendsto_source_never_reply_expect source subsequence hE hc hlaws who
    (quittingLabelReward reward who)).congr' (Eventually.of_forall fun k =>
      source_updated_expect_eq_original_reply reward (source (subsequence k)) who none)

/-- Complete original caps converge on the whole chosen source subsequence, for every actual
limiting menu. Maximizing replies are extracted only inside the proof of convergence. -/
theorem tendsto_sourceFullCap
    (source : ℕ → ι → FinDist (Option ℕ)) (subsequence : ℕ → ℕ)
    {limit : MathUE.MarkedCalendar.Calendar} {menu : NonemptyCompacts ℝ}
    {marginals : ι → ProbabilityMeasure unitInterval}
    (hE : Tendsto (fun k => (calendar (source (subsequence k))).endpoints) atTop
      (𝓝 limit.endpoints))
    (hc : Tendsto (fun k => cutoff (source (subsequence k))) atTop (𝓝 limit.cutoff))
    (hT : Tendsto (fun k => legalMenuCompacts (source (subsequence k))) atTop (𝓝 menu))
    (hlaws : Tendsto (fun k => chartLaw (source (subsequence k))) atTop (𝓝 marginals))
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (who : ι) :
    Tendsto (fun k => quittingStoppingLawReplacementPayoffCap reward
      (fun i => (source (subsequence k) i).toPMF) who) atTop
      (𝓝 (limitReplyMaximum limit menu marginals who (quittingLabelReward reward who))) := by
  classical
  let payoff := fun k choice => quittingBehaviorPureTimePayoff reward
    (quittingStoppingLawProfile reward (fun i => (source (subsequence k) i).toPMF)) who choice
  let caps := fun k => quittingStoppingLawReplacementPayoffCap reward
    (fun i => (source (subsequence k) i).toPMF) who
  let target := limitReplyMaximum limit menu marginals who (quittingLabelReward reward who)
  obtain ⟨reply, hreply, hmax⟩ := exists_limitReplyValue_eq_maximum
    source subsequence hE hc hT hlaws who (quittingLabelReward reward who)
  have hupper (other : LimitReply menu) :
      limitReplyValue limit menu marginals who (quittingLabelReward reward who) other ≤ target := by
    exact (hmax other).trans_eq hreply
  have hreference : ∃ choices : ℕ → Option ℕ,
      Tendsto (fun k => payoff k (choices k)) atTop (𝓝 target) := by
    cases reply with
    | inl t =>
        obtain ⟨dates, _, hdates⟩ :=
          exists_legal_reply_dates_tendsto source subsequence hT t.property
        refine ⟨fun k => some (dates k), ?_⟩
        dsimp only [target]
        rw [← hreply]
        exact tendsto_original_finite_reply_payoff source subsequence hE hc hlaws reward who
          dates hdates
    | inr terminal =>
        cases terminal
        refine ⟨fun _ => none, ?_⟩
        dsimp only [target]
        rw [← hreply]
        exact tendsto_original_never_reply_payoff source subsequence hE hc hlaws reward who
  obtain ⟨reference, href⟩ := hreference
  have identify (indexes : ℕ → ℕ) (hindexes : Tendsto indexes atTop atTop) {value : ℝ}
      (hvalue : Tendsto (fun k => caps (indexes k)) atTop (𝓝 value))
      (hvalueUpper : value ≤ target) : value = target := by
    apply hvalueUpper.antisymm
    exact le_of_tendsto_of_tendsto (href.comp hindexes) hvalue
      (Eventually.of_forall fun k => original_reply_le_sourceFullCap reward
        (source (subsequence (indexes k))) who (reference (indexes k)))
  change Tendsto caps atTop (𝓝 target)
  apply Filter.tendsto_of_subseq_tendsto
  intro indexes hindexes
  have hattains (k : ℕ) : ∃ choice ∈ quittingFiniteOpponentAtomGapReplyMenu
      (quittingFiniteStoppingCalendar (source (subsequence (indexes k)))),
      payoff (indexes k) choice = caps (indexes k) :=
    exists_original_reply_eq_sourceFullCap reward (source (subsequence (indexes k))) who
  choose choices _hchoices hcaps using hattains
  by_cases hnever : ∃ᶠ k in atTop, choices k = none
  · obtain ⟨next, hnext, hnone⟩ := exists_seq_forall_of_frequently hnever
    have hvalue : Tendsto (fun k => caps (indexes (next k))) atTop
        (𝓝 (responseValue limit marginals who (quittingLabelReward reward who) ⊤)) := by
      apply ((tendsto_original_never_reply_payoff source subsequence hE hc hlaws reward who).comp
        (hindexes.comp hnext)).congr'
      filter_upwards [] with k
      simpa only [payoff, Function.comp_def, hnone k] using hcaps (next k)
    have heq := identify (fun k => indexes (next k)) (hindexes.comp hnext) hvalue
      (hupper (Sum.inr ()))
    exact ⟨next, by simpa only [heq] using hvalue⟩
  · have hevent : ∀ᶠ k in atTop, choices k ≠ none := not_frequently.mp hnever
    obtain ⟨start, hstart⟩ := eventually_atTop.mp hevent
    let dates : ℕ → ℕ := fun k => (choices (k + start)).getD 0
    have hchoice (k : ℕ) : choices (k + start) = some (dates k) := by
      cases hk : choices (k + start) with
      | none => exact (hstart (k + start) (by omega) hk).elim
      | some time => simp only [dates, hk, Option.getD_some]
    let points : ℕ → unitInterval := fun k =>
      ⟨mark (source (subsequence (indexes (k + start)))) (dates k),
        mark_nonneg _ _, (mark_le_cutoff _ _).trans (cutoff _).property.2⟩
    obtain ⟨point, next, hnext, hpoint⟩ := CompactSpace.tendsto_subseq points
    have hindices : Tendsto (fun k => indexes (next k + start)) atTop atTop :=
      hindexes.comp ((tendsto_add_atTop_nat start).comp hnext.tendsto_atTop)
    have hmarks : Tendsto
        (fun k => mark (source (subsequence (indexes (next k + start)))) (dates (next k)))
        atTop (𝓝 (point : ℝ)) :=
      continuous_subtype_val.continuousAt.tendsto.comp hpoint
    have hmem : (point : ℝ) ∈ menu := by
      apply Math.Topology.mem_limit_of_nonemptyCompacts_tendsto (hT.comp hindices) hmarks
      apply Eventually.of_forall
      intro k
      change mark (source (subsequence (indexes (next k + start)))) (dates (next k)) ∈
        (legalFiniteMenu (source (subsequence (indexes (next k + start)))) : Set ℝ)
      rw [← range_mark_eq_legalFiniteMenu]
      exact ⟨dates (next k), rfl⟩
    have hvalue : Tendsto (fun k => caps (indexes (next k + start))) atTop
        (𝓝 (responseValue limit marginals who (quittingLabelReward reward who)
          (point.val : WithTop ℝ))) := by
      apply (tendsto_original_finite_reply_payoff source
        (fun k => subsequence (indexes (next k + start)))
        (hE.comp hindices) (hc.comp hindices) (hlaws.comp hindices) reward who
        (fun k => dates (next k)) hmarks).congr'
      filter_upwards [] with k
      simpa only [hchoice (next k)] using hcaps (next k + start)
    have heq := identify (fun k => indexes (next k + start)) hindices hvalue
      (hupper (Sum.inl ⟨point.val, hmem⟩))
    exact ⟨fun k => next k + start, by simpa only [heq] using hvalue⟩

/-- One actual-source subsequence precedes every reward table and every player's original
payoff and complete cap. No minimizing marked law or response-limit oracle is supplied. -/
theorem exists_chart_compactification_payoff_fullCap_limits
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
      ∀ (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (who : ι),
        Tendsto (fun k => quittingTerminalPayoff reward
          (quittingStoppingLawProfile reward (fun i => (source (subsequence k) i).toPMF)) who)
          atTop (𝓝 (∫ sample, MathUE.MarkedCalendar.payoffKernel limit
            (quittingLabelReward reward who) sample
            ∂(ProbabilityMeasure.pi marginals : Measure (ι → unitInterval)))) ∧
        Tendsto (fun k => quittingStoppingLawReplacementPayoffCap reward
          (fun i => (source (subsequence k) i).toPMF) who) atTop
          (𝓝 (limitReplyMaximum limit menu marginals who (quittingLabelReward reward who))) := by
  obtain ⟨subsequence, limit, menu, marginals, hmono, hE, hc, hT, hμ, hbound,
    hsum, hsubset, hcutoff, hdates, hpayoff, _, _⟩ :=
    exists_chart_compactification_expectation_limits source
  refine ⟨subsequence, limit, menu, marginals, hmono, hE, hc, hT, hμ, hbound,
    hsum, hsubset, hcutoff, hdates, ?_⟩
  intro reward who
  refine ⟨?_, tendsto_sourceFullCap source subsequence hE hc hT hμ reward who⟩
  apply (hpayoff (quittingLabelReward reward who)).congr'
  apply Eventually.of_forall
  intro k
  exact (sourceOutcome_expect_eq_stoppingLawExpectedPayoff reward
    (source (subsequence k)) who).trans
    (quittingTerminalPayoff_stoppingLawProfile_eq_expectedPayoff reward
      (fun i => (source (subsequence k) i).toPMF) who).symm

end GameTheory.MarkedCalendarChart
