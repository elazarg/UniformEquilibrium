import Research.MarkedCalendar.FiniteLawCaps
import UniformEquilibrium.Quitting.Terminal.TerminalDebtSumInf
import UniformEquilibrium.Quitting.Paths.CommonQuantileClockApproximation
import UniformEquilibrium.Quitting.Paths.FiniteCalendarPayoffClosure
import MathUE.ProbabilityMassFunction.ExactLateFiniteCensor

/-! # Actual marked limits in the original semantic carrier

The prescribed payoff and complete cap of an actual marked limit form a point
of the original closed attainable semantic carrier. Every limit of any finite
source family minimizing the original SUM debt has that same minimum value.
The compactification is selected once, before reward tables and consumers.

These statements do not assume a marked minimizer. Existing finite-clock
semantic approximation supplies an actual finite minimizing source, packaged
without changing its laws or Never mass. Identifying gap densities and
realizing signed old-law variations remain separate tasks.
-/

noncomputable section

open Set Filter MeasureTheory TopologicalSpace GameTheory.Math.Probability
open scoped Topology BigOperators

namespace GameTheory.MarkedCalendarChart

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]

/-- The actual payoff and complete-response envelope, in the original semantic carrier type. -/
def limitSemanticPair (limit : MathUE.MarkedCalendar.Calendar) (menu : NonemptyCompacts ℝ)
    (marginals : ι → ProbabilityMeasure unitInterval)
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) : QuittingTerminalSemanticPair ι :=
  (fun who => ∫ sample, MathUE.MarkedCalendar.payoffKernel limit
      (quittingLabelReward reward who) sample
      ∂(ProbabilityMeasure.pi marginals : Measure (ι → unitInterval)),
    fun who => limitReplyMaximum limit menu marginals who (quittingLabelReward reward who))

/-- Every specified actual marked limit is the limit of the original executable semantic pairs. -/
theorem tendsto_sourceSemanticPair
    (source : ℕ → ι → FinDist (Option ℕ)) (subsequence : ℕ → ℕ)
    {limit : MathUE.MarkedCalendar.Calendar} {menu : NonemptyCompacts ℝ}
    {marginals : ι → ProbabilityMeasure unitInterval}
    (hE : Tendsto (fun k => (calendar (source (subsequence k))).endpoints) atTop
      (𝓝 limit.endpoints))
    (hc : Tendsto (fun k => cutoff (source (subsequence k))) atTop (𝓝 limit.cutoff))
    (hT : Tendsto (fun k => legalMenuCompacts (source (subsequence k))) atTop (𝓝 menu))
    (hlaws : Tendsto (fun k => chartLaw (source (subsequence k))) atTop (𝓝 marginals))
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) :
    Tendsto (fun k => quittingTerminalSemanticPair reward
      (quittingStoppingLawProfile reward (fun i => (source (subsequence k) i).toPMF)))
      atTop (𝓝 (limitSemanticPair limit menu marginals reward)) := by
  apply Tendsto.prodMk_nhds
  · apply tendsto_pi_nhds.mpr
    intro who
    apply (tendsto_source_outcome_expect source subsequence hE hc hlaws
      (quittingLabelReward reward who)).congr'
    apply Eventually.of_forall
    intro k
    exact (sourceOutcome_expect_eq_stoppingLawExpectedPayoff reward
      (source (subsequence k)) who).trans
      (quittingTerminalPayoff_stoppingLawProfile_eq_expectedPayoff reward
        (fun i => (source (subsequence k) i).toPMF) who).symm
  · apply tendsto_pi_nhds.mpr
    intro who
    apply (tendsto_sourceFullCap source subsequence hE hc hT hlaws reward who).congr'
    exact Eventually.of_forall fun k =>
      quittingStoppingLawCap_eq_continuationBestResponseValue_stoppingLawProfile reward
        (fun i => (source (subsequence k) i).toPMF) who

/-- Carrier membership is derived from actual source profiles, for every actual marked limit. -/
theorem limitSemanticPair_mem_carrier
    (source : ℕ → ι → FinDist (Option ℕ)) (subsequence : ℕ → ℕ)
    {limit : MathUE.MarkedCalendar.Calendar} {menu : NonemptyCompacts ℝ}
    {marginals : ι → ProbabilityMeasure unitInterval}
    (hE : Tendsto (fun k => (calendar (source (subsequence k))).endpoints) atTop
      (𝓝 limit.endpoints))
    (hc : Tendsto (fun k => cutoff (source (subsequence k))) atTop (𝓝 limit.cutoff))
    (hT : Tendsto (fun k => legalMenuCompacts (source (subsequence k))) atTop (𝓝 menu))
    (hlaws : Tendsto (fun k => chartLaw (source (subsequence k))) atTop (𝓝 marginals))
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) :
    limitSemanticPair limit menu marginals reward ∈ quittingTerminalSemanticCarrier reward := by
  apply (quittingTerminalSemanticCarrier_isCompact reward).isClosed.mem_of_tendsto
    (tendsto_sourceSemanticPair source subsequence hE hc hT hlaws reward)
  exact Eventually.of_forall fun k => subset_closure
    ⟨quittingStoppingLawProfile reward (fun i => (source (subsequence k) i).toPMF), rfl⟩

/-- Any minimizing finite source has the original SUM infimum at every marked limit. -/
theorem limitSemanticPair_debtSum_eq_inf_of_minimizing_source
    (source : ℕ → ι → FinDist (Option ℕ)) (subsequence : ℕ → ℕ)
    (hsubsequence : Tendsto subsequence atTop atTop)
    {limit : MathUE.MarkedCalendar.Calendar} {menu : NonemptyCompacts ℝ}
    {marginals : ι → ProbabilityMeasure unitInterval}
    (hE : Tendsto (fun k => (calendar (source (subsequence k))).endpoints) atTop
      (𝓝 limit.endpoints))
    (hc : Tendsto (fun k => cutoff (source (subsequence k))) atTop (𝓝 limit.cutoff))
    (hT : Tendsto (fun k => legalMenuCompacts (source (subsequence k))) atTop (𝓝 menu))
    (hlaws : Tendsto (fun k => chartLaw (source (subsequence k))) atTop (𝓝 marginals))
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hminimizing : Tendsto (fun k => quittingTerminalDebtSum reward
      (quittingStoppingLawProfile reward (fun i => (source k i).toPMF))) atTop
      (𝓝 (quittingTerminalDebtSumInf reward))) :
    quittingTerminalSemanticDebtSum (limitSemanticPair limit menu marginals reward) =
      quittingTerminalDebtSumInf reward := by
  have hdebt := continuous_quittingTerminalSemanticDebtSum.continuousAt.tendsto.comp
    (tendsto_sourceSemanticPair source subsequence hE hc hT hlaws reward)
  exact tendsto_nhds_unique hdebt (hminimizing.comp hsubsequence)

/-- The resulting minimum is global on the original closed attainable carrier. -/
theorem limitSemanticPair_isMinimum_of_minimizing_source
    (source : ℕ → ι → FinDist (Option ℕ)) (subsequence : ℕ → ℕ)
    (hsubsequence : Tendsto subsequence atTop atTop)
    {limit : MathUE.MarkedCalendar.Calendar} {menu : NonemptyCompacts ℝ}
    {marginals : ι → ProbabilityMeasure unitInterval}
    (hE : Tendsto (fun k => (calendar (source (subsequence k))).endpoints) atTop
      (𝓝 limit.endpoints))
    (hc : Tendsto (fun k => cutoff (source (subsequence k))) atTop (𝓝 limit.cutoff))
    (hT : Tendsto (fun k => legalMenuCompacts (source (subsequence k))) atTop (𝓝 menu))
    (hlaws : Tendsto (fun k => chartLaw (source (subsequence k))) atTop (𝓝 marginals))
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hminimizing : Tendsto (fun k => quittingTerminalDebtSum reward
      (quittingStoppingLawProfile reward (fun i => (source k i).toPMF))) atTop
      (𝓝 (quittingTerminalDebtSumInf reward))) :
    ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum (limitSemanticPair limit menu marginals reward) ≤
        quittingTerminalSemanticDebtSum candidate := by
  rw [limitSemanticPair_debtSum_eq_inf_of_minimizing_source source subsequence hsubsequence
    hE hc hT hlaws reward hminimizing]
  obtain ⟨minimum, hminimum, hleast⟩ := exists_minimum_quittingTerminalSemanticDebtSum reward
  rw [quittingTerminalDebtSumInf_eq_terminalSemanticDebtSum_of_minimum
    minimum hminimum hleast]
  exact hleast

/-- One actual-source compactification precedes all reward tables and all minimizing-source
consumers. No new extraction is made for the SUM minimum. -/
theorem exists_chart_compactification_semantic_minimum
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
      ∀ reward : {S : Finset ι // S.Nonempty} → Payoff ι,
        Tendsto (fun k => quittingTerminalSemanticPair reward
          (quittingStoppingLawProfile reward (fun i => (source (subsequence k) i).toPMF)))
          atTop (𝓝 (limitSemanticPair limit menu marginals reward)) ∧
        limitSemanticPair limit menu marginals reward ∈ quittingTerminalSemanticCarrier reward ∧
        (Tendsto (fun k => quittingTerminalDebtSum reward
          (quittingStoppingLawProfile reward (fun i => (source k i).toPMF))) atTop
          (𝓝 (quittingTerminalDebtSumInf reward)) →
          quittingTerminalSemanticDebtSum (limitSemanticPair limit menu marginals reward) =
            quittingTerminalDebtSumInf reward ∧
          ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
            quittingTerminalSemanticDebtSum (limitSemanticPair limit menu marginals reward) ≤
              quittingTerminalSemanticDebtSum candidate) := by
  obtain ⟨subsequence, limit, menu, marginals, hmono, hE, hc, hT, hμ, hbound,
    hsum, hsubset, hcutoff, hdates, _⟩ :=
    exists_chart_compactification_payoff_fullCap_limits source
  refine ⟨subsequence, limit, menu, marginals, hmono, hE, hc, hT, hμ, hbound,
    hsum, hsubset, hcutoff, hdates, ?_⟩
  intro reward
  refine ⟨tendsto_sourceSemanticPair source subsequence hE hc hT hμ reward,
    limitSemanticPair_mem_carrier source subsequence hE hc hT hμ reward, ?_⟩
  intro hminimizing
  exact ⟨limitSemanticPair_debtSum_eq_inf_of_minimizing_source source subsequence
      hmono.tendsto_atTop hE hc hT hμ reward hminimizing,
    limitSemanticPair_isMinimum_of_minimizing_source source subsequence
      hmono.tendsto_atTop hE hc hT hμ reward hminimizing⟩

omit [Nonempty ι] in
/-- Every original carrier point is approximated by actual finite source laws. The existing
finite-clock approximation is only repackaged: its laws, including Never, remain unchanged. -/
theorem exists_finite_source_tendsto_semanticPair
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (pair : QuittingTerminalSemanticPair ι)
    (hpair : pair ∈ quittingTerminalSemanticCarrier reward) :
    ∃ source : ℕ → ι → FinDist (Option ℕ),
      Tendsto (fun k => quittingTerminalSemanticPair reward
        (quittingStoppingLawProfile reward (fun i => (source k i).toPMF)))
        atTop (𝓝 pair) := by
  obtain ⟨approximants, hlevels, htendsto⟩ :=
    exists_cofinalFiniteClockSemanticPair_sequence_tendsto reward pair hpair
  have hdata : ∀ k, ∃ laws : ι → PMF (Option ℕ),
      (∀ i, IsFiniteClockStoppingLaw (quantileClockSupport ι (k + 1)) (laws i)) ∧
      approximants k = quittingTerminalSemanticPair reward
        (quittingStoppingLawProfile reward laws) := hlevels
  choose laws hlaws hpairs using hdata
  let source : ℕ → ι → FinDist (Option ℕ) := fun k i =>
    quittingCensoredFiniteStoppingLaw (laws k i) (quantileClockSupport ι (k + 1))
  have hexact (k : ℕ) (i : ι) : (source k i).toPMF = laws k i := by
    change (quittingCensoredFiniteStoppingLaw (laws k i)
      (quantileClockSupport ι (k + 1))).toPMF = laws k i
    rw [quittingCensoredFiniteStoppingLaw_toPMF]
    apply _root_.Math.Probability.censorLateFiniteStoppingLaw_eq_self_of_support_prefix
    intro choice hchoice
    rcases hlaws k i choice hchoice with rfl | ⟨time, htime, rfl⟩
    · simp
    · exact (_root_.Math.Probability.some_mem_stoppingLawFinitePrefix _ _).mpr htime.le
  refine ⟨source, htendsto.congr' (Eventually.of_forall fun k => ?_)⟩
  have heq : (fun i => (source k i).toPMF) = laws k := funext (hexact k)
  change approximants k = quittingTerminalSemanticPair reward
    (quittingStoppingLawProfile reward (fun i => (source k i).toPMF))
  rw [heq]
  exact hpairs k

omit [Nonempty ι] in
/-- Every reward table has an actual finite source minimizing the original unrestricted SUM debt. -/
theorem exists_finite_minimizing_source
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) :
    ∃ source : ℕ → ι → FinDist (Option ℕ),
      Tendsto (fun k => quittingTerminalDebtSum reward
        (quittingStoppingLawProfile reward (fun i => (source k i).toPMF))) atTop
        (𝓝 (quittingTerminalDebtSumInf reward)) := by
  obtain ⟨pair, hpair, hminimum⟩ := exists_minimum_quittingTerminalSemanticDebtSum reward
  obtain ⟨source, hsource⟩ := exists_finite_source_tendsto_semanticPair reward pair hpair
  have hsum := continuous_quittingTerminalSemanticDebtSum.continuousAt.tendsto.comp hsource
  rw [← quittingTerminalDebtSumInf_eq_terminalSemanticDebtSum_of_minimum
    pair hpair hminimum] at hsum
  exact ⟨source, hsum⟩

/-- An actual finite minimizing family and its marked global minimum are produced from the
reward table alone. The universal source/limit results above remain independent of this choice. -/
theorem exists_finite_source_marked_semantic_minimum
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) :
    ∃ (source : ℕ → ι → FinDist (Option ℕ)) (subsequence : ℕ → ℕ)
      (limit : MathUE.MarkedCalendar.Calendar) (menu : NonemptyCompacts ℝ)
      (marginals : ι → ProbabilityMeasure unitInterval),
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
      Tendsto (fun k => quittingTerminalDebtSum reward
        (quittingStoppingLawProfile reward (fun i => (source k i).toPMF))) atTop
        (𝓝 (quittingTerminalDebtSumInf reward)) ∧
      Tendsto (fun k => quittingTerminalSemanticPair reward
        (quittingStoppingLawProfile reward (fun i => (source (subsequence k) i).toPMF)))
        atTop (𝓝 (limitSemanticPair limit menu marginals reward)) ∧
      limitSemanticPair limit menu marginals reward ∈ quittingTerminalSemanticCarrier reward ∧
      quittingTerminalSemanticDebtSum (limitSemanticPair limit menu marginals reward) =
        quittingTerminalDebtSumInf reward ∧
      ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
        quittingTerminalSemanticDebtSum (limitSemanticPair limit menu marginals reward) ≤
          quittingTerminalSemanticDebtSum candidate := by
  obtain ⟨source, hsource⟩ := exists_finite_minimizing_source reward
  obtain ⟨subsequence, limit, menu, marginals, hmono, hE, hc, hT, hμ, hbound,
    hsum, hsubset, hcutoff, hdates, hconsumer⟩ :=
    exists_chart_compactification_semantic_minimum source
  obtain ⟨hpair, hmem, hminimum⟩ := hconsumer reward
  exact ⟨source, subsequence, limit, menu, marginals, hmono, hE, hc, hT, hμ,
    hbound, hsum, hsubset, hcutoff, hdates, hsource, hpair, hmem, hminimum hsource⟩

end GameTheory.MarkedCalendarChart
