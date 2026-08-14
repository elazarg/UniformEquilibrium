/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Research.Quitting.KActiveMarkedAtomPathConsumer
import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegime
import UniformEquilibrium.Quitting.Cycles.ConditionedDeletedClockMonopoly

/-!
# Cumulative marked-clock compact extraction

A fixed one-active singleton mark need not have a positive floor at every
date.  It is enough that compatible finite prefixes force its cumulative mass
above a divergent deterministic budget.  The budget constraints are closed,
and imposing every earlier budget at every longer horizon makes the compact
prefix sets nested.

The extracted infinite path has nonsummable marked mass.  One-activity makes
that mass no larger than total absorption, so the joint survival vanishes and
the exact Bellman path is selected by its literal terminal law.  This gives a
direct UE certificate.

Thus a diffuse fixed singleton edge remains terminal whenever its cumulative
clock diverges.  The unresolved alternatives are summable fixed-label mass or
failure to retain one label on compatible prefixes.
-/

noncomputable section

namespace GameTheory

open Finset Set StochasticGame Filter Math.Probability Math.PMFProduct
open Math.ProbabilityMassFunction Math.Topology

variable {Point : Type*} [TopologicalSpace Point] [T2Space Point]

/-! ## Generic compact extraction with divergent prefix budgets -/

/-- Box-valued relation prefixes satisfying every cumulative weight budget
whose cutoff has already appeared. -/
def compactBudgetedPrefixSolutionSet
    (box : Set Point) (relation : Point → Point → Prop)
    (weight : Point → ℝ) (budget : ℕ → ℝ) (horizon : ℕ) :
    Set (ℕ → Point) :=
  {path |
    path ∈ compactFinitePrefixSolutionSet box relation horizon ∧
      ∀ cutoff ≤ horizon,
        budget cutoff ≤
          ∑ time ∈ Finset.range cutoff, weight (path time)}

omit [TopologicalSpace Point] [T2Space Point] in
/-- Increasing the horizon only adds relation and budget constraints. -/
theorem compactBudgetedPrefixSolutionSet_succ_subset
    (box : Set Point) (relation : Point → Point → Prop)
    (weight : Point → ℝ) (budget : ℕ → ℝ) (horizon : ℕ) :
    compactBudgetedPrefixSolutionSet box relation weight budget (horizon + 1) ⊆
      compactBudgetedPrefixSolutionSet box relation weight budget horizon := by
  intro path hpath
  refine ⟨compactFinitePrefixSolutionSet_succ_subset
    box relation horizon hpath.1, ?_⟩
  intro cutoff hcutoff
  exact hpath.2 cutoff (hcutoff.trans (Nat.le_succ horizon))

/-- The budgeted prefix set is closed when the edge graph and weight are
closed/continuous. -/
theorem compactBudgetedPrefixSolutionSet_isClosed
    (box : Set Point) (relation : Point → Point → Prop)
    (weight : Point → ℝ) (budget : ℕ → ℝ)
    (hbox : IsCompact box)
    (hgraph : IsClosed
      {pair : Point × Point |
        pair.1 ∈ box ∧ pair.2 ∈ box ∧ relation pair.1 pair.2})
    (hweight : Continuous weight) (horizon : ℕ) :
    IsClosed
      (compactBudgetedPrefixSolutionSet
        box relation weight budget horizon) := by
  have hprefix := compactFinitePrefixSolutionSet_isClosed
    box relation hbox hgraph horizon
  have hbudgetClosed : IsClosed {path : ℕ → Point |
      ∀ cutoff ≤ horizon,
        budget cutoff ≤
          ∑ time ∈ Finset.range cutoff, weight (path time)} := by
    rw [show {path : ℕ → Point |
        ∀ cutoff ≤ horizon,
          budget cutoff ≤
            ∑ time ∈ Finset.range cutoff, weight (path time)} =
      ⋂ cutoff : ℕ, ⋂ (_h : cutoff ≤ horizon),
        {path | budget cutoff ≤
          ∑ time ∈ Finset.range cutoff, weight (path time)} by
      ext path
      simp]
    apply isClosed_iInter
    intro cutoff
    apply isClosed_iInter
    intro _h
    apply isClosed_le continuous_const
    exact continuous_finsetSum _ fun time _ =>
      hweight.comp (continuous_apply time)
  rw [show compactBudgetedPrefixSolutionSet
      box relation weight budget horizon =
    compactFinitePrefixSolutionSet box relation horizon ∩
      {path : ℕ → Point |
        ∀ cutoff ≤ horizon,
          budget cutoff ≤
            ∑ time ∈ Finset.range cutoff, weight (path time)} by
    ext path
    rfl]
  exact hprefix.inter hbudgetClosed

/-- Every budgeted prefix set is compact. -/
theorem compactBudgetedPrefixSolutionSet_isCompact
    (box : Set Point) (relation : Point → Point → Prop)
    (weight : Point → ℝ) (budget : ℕ → ℝ)
    (hbox : IsCompact box)
    (hgraph : IsClosed
      {pair : Point × Point |
        pair.1 ∈ box ∧ pair.2 ∈ box ∧ relation pair.1 pair.2})
    (hweight : Continuous weight) (horizon : ℕ) :
    IsCompact
      (compactBudgetedPrefixSolutionSet
        box relation weight budget horizon) := by
  exact (isCompact_pi_infinite fun _ => hbox).of_isClosed_subset
    (compactBudgetedPrefixSolutionSet_isClosed
      box relation weight budget hbox hgraph hweight horizon)
    (fun _ hpath => hpath.1.1)

/-- **Budgeted compact inverse limit.**  Arbitrarily long compatible prefixes
meeting all elapsed cumulative budgets yield one infinite relation chain that
meets every budget. -/
theorem exists_infiniteChain_of_budgetedFinitePrefixes
    (box : Set Point) (relation : Point → Point → Prop)
    (weight : Point → ℝ) (budget : ℕ → ℝ)
    (hbox : IsCompact box)
    (hgraph : IsClosed
      {pair : Point × Point |
        pair.1 ∈ box ∧ pair.2 ∈ box ∧ relation pair.1 pair.2})
    (hweight : Continuous weight)
    (hprefix : ∀ horizon,
      (compactBudgetedPrefixSolutionSet
        box relation weight budget horizon).Nonempty) :
    ∃ path : ℕ → Point,
      (∀ time, path time ∈ box) ∧
      (∀ time, relation (path time) (path (time + 1))) ∧
      ∀ cutoff, budget cutoff ≤
        ∑ time ∈ Finset.range cutoff, weight (path time) := by
  let prefixSet : ℕ → Set (ℕ → Point) := fun horizon =>
    compactBudgetedPrefixSolutionSet box relation weight budget horizon
  have hnested : ∀ horizon, prefixSet (horizon + 1) ⊆ prefixSet horizon :=
    compactBudgetedPrefixSolutionSet_succ_subset
      box relation weight budget
  have hnonempty : ∀ horizon, (prefixSet horizon).Nonempty := hprefix
  have hcompact0 : IsCompact (prefixSet 0) :=
    compactBudgetedPrefixSolutionSet_isCompact
      box relation weight budget hbox hgraph hweight 0
  have hclosed : ∀ horizon, IsClosed (prefixSet horizon) :=
    compactBudgetedPrefixSolutionSet_isClosed
      box relation weight budget hbox hgraph hweight
  obtain ⟨path, hpath⟩ :=
    IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed
      prefixSet hnested hnonempty hcompact0 hclosed
  have hpref : ∀ horizon, path ∈ prefixSet horizon :=
    Set.mem_iInter.mp hpath
  refine ⟨path, (hpref 0).1.1, ?_, ?_⟩
  · intro time
    exact (hpref (time + 1)).1.2 ⟨time, Nat.lt_succ_self time⟩
  · intro cutoff
    exact (hpref cutoff).2 cutoff le_rfl

/-! ## A divergent cumulative budget forces nonsummability -/

/-- A nonnegative sequence whose partial sums dominate a function tending to
`+∞` cannot be summable. -/
theorem not_summable_of_tendsto_budget_atTop_of_prefix_le
    (weight budget : ℕ → ℝ)
    (hbudget : Tendsto budget atTop atTop)
    (hprefix : ∀ cutoff, budget cutoff ≤
      ∑ time ∈ Finset.range cutoff, weight time) :
    ¬Summable weight := by
  intro hsummable
  have hpartial : Tendsto
      (fun cutoff => ∑ time ∈ Finset.range cutoff, weight time)
      atTop (nhds (∑' time, weight time)) :=
    hsummable.hasSum.tendsto_sum_nat
  have hsumEventually : ∀ᶠ cutoff in atTop,
      (∑ time ∈ Finset.range cutoff, weight time) <
        (∑' time, weight time) + 1 :=
    hpartial.eventually (Iio_mem_nhds (by linarith))
  have hbudgetEventually : ∀ᶠ cutoff in atTop,
      (∑' time, weight time) + 2 ≤ budget cutoff :=
    (tendsto_atTop.1 hbudget) ((∑' time, weight time) + 2)
  obtain ⟨cutoff, hsum, hbudgetLarge⟩ :=
    (hsumEventually.and hbudgetEventually).exists
  have := hprefix cutoff
  linarith

/-! ## Game-facing one-active marked-budget consumer -/

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- An exact `K`-active Bellman path whose cumulative total absorption
dominates a divergent budget is already a support-rational divergent terminal
path.  No marked coalition is needed. -/
theorem kActiveAbsorptionBudgetPath_is_supportRationalDivergent
    [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (K : ℕ) (bound epsilon : ℝ) (budget : ℕ → ℝ)
    (hbound0 : 0 ≤ bound)
    (hreward : ∀ terminal who, |reward terminal who| ≤ bound)
    (hbudget : Tendsto budget atTop atTop)
    (state : ℕ → QuittingNashBellmanPoint ι)
    (hstateBox : ∀ time,
      state time ∈ quittingCirculationPathBox bound
        (fun who => quittingPunishmentValue reward who - epsilon))
    (hstateEdge : ∀ time,
      IsQuittingKActiveCirculationPathEdge reward K epsilon 0
        (state time) (state (time + 1)))
    (hprefixBudget : ∀ cutoff, budget cutoff ≤
      ∑ time ∈ Finset.range cutoff,
        quittingSimplexAbsorptionMass (state time).2) :
    ∃ plan : ℕ → ι → PMF Bool,
      IsQuittingRootSequenceSupportApproxNash reward plan epsilon ∧
      ¬Summable (quittingTotalAbsorptionCharge plan) ∧
      (∀ target time,
        quittingPunishmentValue reward target - epsilon ≤
          quittingRootSequenceTerminalValue reward plan target time) ∧
      ∀ time, HasQuittingSupportCardAtMost K (plan time) := by
  let value : ℕ → Payoff ι := fun time => (state time).1
  let plan : ℕ → ι → PMF Bool := fun time =>
    quittingRootOfSimplex (state time).2
  let absorption : ℕ → ℝ := fun time =>
    quittingRootAbsorptionMass (plan time)
  have hvalueBound : ∀ time who, |value time who| ≤ bound := by
    intro time who
    exact abs_le.mpr
      ⟨(hstateBox time).1.1 who, (hstateBox time).1.2 who⟩
  have hvalueLower : ∀ time who,
      quittingPunishmentValue reward who - epsilon ≤ value time who := by
    intro time who
    exact (hstateBox time).2 who
  have hpolicy : ∀ time,
      value time = quittingRootSuccessorPayoff reward
        (value (time + 1)) (plan time) := by
    intro time
    exact (hstateEdge time).1.1
  have hactive : ∀ time,
      HasQuittingSupportCardAtMost K (plan time) := by
    intro time
    exact hasQuittingSupportCardAtMost_quittingRootOfSimplex
      K (state time).2 (hstateEdge time).2
  have habsorptionPrefix : ∀ cutoff, budget cutoff ≤
      ∑ time ∈ Finset.range cutoff, absorption time := by
    intro cutoff
    simpa [absorption, plan,
      quittingSimplexAbsorptionMass_eq_rootAbsorptionMass] using
        hprefixBudget cutoff
  have habsorptionDiverges : ¬Summable absorption :=
    not_summable_of_tendsto_budget_atTop_of_prefix_le
      absorption budget hbudget habsorptionPrefix
  have hsurvival : ∀ start,
      Tendsto (quittingJointSurvivalWeight plan start) atTop (nhds 0) := by
    intro start
    apply tendsto_zero_quittingJointSurvivalWeight_of_not_summable_absorption
    intro hsuffix
    apply habsorptionDiverges
    have hshift : Summable (fun offset => absorption (offset + start)) := by
      simpa [absorption, Nat.add_comm] using hsuffix
    exact (summable_nat_add_iff start).1 hshift
  have hselected : ∀ time,
      value time = fun who =>
        quittingRootSequenceTerminalValue reward plan who time :=
    eq_quittingRootSequenceTerminalValue_of_exact_bounded_path_of_jointSurvival_tendsto_zero
      reward plan value hsurvival hbound0 hreward hvalueBound hpolicy
  have hsupport :
      IsQuittingRootSequenceSupportApproxNash reward plan epsilon := by
    intro time
    have htail : quittingRootSequenceTailVector reward plan (time + 1) =
        value (time + 1) := by
      funext who
      change quittingRootSequenceTerminalValue reward plan who (time + 1) =
        value (time + 1) who
      exact (congrFun (hselected (time + 1)) who).symm
    rw [htail]
    exact (isQuittingSimplexRootSupportApproxNash_iff
      reward (value (time + 1)) epsilon (state time).2).1
        (hstateEdge time).1.2.1
  refine ⟨plan, hsupport, ?_, ?_, hactive⟩
  · change ¬Summable absorption
    exact habsorptionDiverges
  · intro target time
    rw [← congrFun (hselected time) target]
    exact hvalueLower time target

/-- **Cumulative-clock `K/N` compact consumer.**  Compatible finite
prefixes with `K`-active roots and a divergent cumulative total-absorption
budget imply a uniform-equilibrium payoff.  This strengthens the rowwise
positive-charge compact consumer: the one-stage absorption may tend to zero. -/
theorem quittingGame_exists_uniformEquilibriumPayoff_of_KActiveAbsorptionBudgetPrefixes
    [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (K : ℕ) (bound : ℝ)
    (hbound0 : 0 ≤ bound)
    (hreward : ∀ terminal who, |reward terminal who| ≤ bound)
    (hprefix : ∀ epsilon, 0 < epsilon →
      ∃ budget : ℕ → ℝ,
        Tendsto budget atTop atTop ∧
        ∀ horizon,
          (compactBudgetedPrefixSolutionSet
            (quittingCirculationPathBox bound
              (fun who => quittingPunishmentValue reward who - epsilon))
            (IsQuittingKActiveCirculationPathEdge reward K epsilon 0)
            (fun point => quittingSimplexAbsorptionMass point.2)
            budget horizon).Nonempty) :
    ∃ payoff : Payoff ι,
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff := by
  apply quittingGame_exists_uniformEquilibriumPayoff_of_KActivePaths reward K
  intro epsilon hepsilon
  obtain ⟨budget, hbudget, hpref⟩ := hprefix epsilon hepsilon
  let box := quittingCirculationPathBox bound
    (fun who => quittingPunishmentValue reward who - epsilon)
  let relation := IsQuittingKActiveCirculationPathEdge reward K epsilon 0
  let weight : QuittingNashBellmanPoint ι → ℝ := fun point =>
    quittingSimplexAbsorptionMass point.2
  have hbox : IsCompact box :=
    quittingCirculationPathBox_isCompact bound
      (fun who => quittingPunishmentValue reward who - epsilon)
  have hgraph : IsClosed {edge : QuittingNashBellmanPoint ι ×
      QuittingNashBellmanPoint ι |
      edge.1 ∈ box ∧ edge.2 ∈ box ∧ relation edge.1 edge.2} := by
    simpa only [box, relation] using
      isClosed_quittingKActiveCirculationPathEdgeGraph reward bound
        (fun who => quittingPunishmentValue reward who - epsilon)
        K epsilon 0
  have hweight : Continuous weight := by
    exact continuous_quittingSimplexAbsorptionMass.comp
      (continuous_snd.comp continuous_id)
  obtain ⟨state, hstateBox, hstateEdge, hprefixBudget⟩ :=
    exists_infiniteChain_of_budgetedFinitePrefixes
      box relation weight budget hbox hgraph hweight
      (by simpa only [box, relation, weight] using hpref)
  obtain ⟨plan, hsupport, hdiverges, hir, hactive⟩ :=
    kActiveAbsorptionBudgetPath_is_supportRationalDivergent
      reward K bound epsilon budget hbound0 hreward hbudget state
        (by simpa only [box] using hstateBox)
        (by simpa only [relation] using hstateEdge)
        (by simpa only [weight] using hprefixBudget)
  exact ⟨plan, hsupport, hdiverges, hir, hactive⟩

/-- Pointwise version without a strictly positive supplied floor: a marked
singleton atom never exceeds total absorption on a one-active root. -/
theorem oneActive_markedSingletonMass_le_absorption'
    (root : ι → PMF Bool) (markedPlayer clockOwner : ι)
    (hactive : HasQuittingSupportCardAtMost 1 root) :
    quittingOpponentCoalitionMass root markedPlayer {clockOwner} ≤
      quittingRootAbsorptionMass root := by
  by_cases hpos : 0 <
      quittingOpponentCoalitionMass root markedPlayer {clockOwner}
  · exact (quittingOpponentCoalitionMass_singleton_eq_absorption_of_oneActive
      root markedPlayer clockOwner hactive hpos).le
  · exact (le_of_not_gt hpos).trans
      (quittingRootAbsorptionMass_nonneg root)

/-- A one-active exact Bellman path with divergent cumulative mass on one
fixed singleton mark is a support-rational divergent terminal path. -/
theorem oneActiveMarkedBudgetPath_is_supportRationalDivergent
    [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (bound epsilon : ℝ) (markedPlayer clockOwner : ι)
    (budget : ℕ → ℝ)
    (hbound0 : 0 ≤ bound)
    (hreward : ∀ terminal who, |reward terminal who| ≤ bound)
    (hbudget : Tendsto budget atTop atTop)
    (state : ℕ → QuittingNashBellmanPoint ι)
    (hstateBox : ∀ time,
      state time ∈ quittingCirculationPathBox bound
        (fun who => quittingPunishmentValue reward who - epsilon))
    (hstateEdge : ∀ time,
      IsQuittingKActiveCirculationPathEdge reward 1 epsilon 0
        (state time) (state (time + 1)))
    (hprefixBudget : ∀ cutoff, budget cutoff ≤
      ∑ time ∈ Finset.range cutoff,
        quittingSimplexOpponentCoalitionMass
          (state time).2 markedPlayer {clockOwner}) :
    ∃ plan : ℕ → ι → PMF Bool,
      IsQuittingRootSequenceSupportApproxNash reward plan epsilon ∧
      ¬Summable (quittingTotalAbsorptionCharge plan) ∧
      (∀ target time,
        quittingPunishmentValue reward target - epsilon ≤
          quittingRootSequenceTerminalValue reward plan target time) ∧
      ∀ time, HasQuittingSupportCardAtMost 1 (plan time) := by
  let value : ℕ → Payoff ι := fun time => (state time).1
  let plan : ℕ → ι → PMF Bool := fun time =>
    quittingRootOfSimplex (state time).2
  let markedMass : ℕ → ℝ := fun time =>
    quittingOpponentCoalitionMass
      (plan time) markedPlayer {clockOwner}
  have hvalueBound : ∀ time who, |value time who| ≤ bound := by
    intro time who
    exact abs_le.mpr
      ⟨(hstateBox time).1.1 who, (hstateBox time).1.2 who⟩
  have hvalueLower : ∀ time who,
      quittingPunishmentValue reward who - epsilon ≤ value time who := by
    intro time who
    exact (hstateBox time).2 who
  have hpolicy : ∀ time,
      value time = quittingRootSuccessorPayoff reward
        (value (time + 1)) (plan time) := by
    intro time
    exact (hstateEdge time).1.1
  have hactive : ∀ time,
      HasQuittingSupportCardAtMost 1 (plan time) := by
    intro time
    exact hasQuittingSupportCardAtMost_quittingRootOfSimplex
      1 (state time).2 (hstateEdge time).2
  have hmarkedPrefix : ∀ cutoff, budget cutoff ≤
      ∑ time ∈ Finset.range cutoff, markedMass time := by
    intro cutoff
    simpa [markedMass, plan,
      quittingSimplexOpponentCoalitionMass_eq_root] using
        hprefixBudget cutoff
  have hmarkedDiverges : ¬Summable markedMass :=
    not_summable_of_tendsto_budget_atTop_of_prefix_le
      markedMass budget hbudget hmarkedPrefix
  have habsorptionDiverges : ¬Summable
      (fun time => quittingRootAbsorptionMass (plan time)) := by
    intro habsorption
    apply hmarkedDiverges
    apply habsorption.of_nonneg_of_le
    · exact fun time => quittingOpponentCoalitionMass_nonneg
        (plan time) markedPlayer {clockOwner}
    · exact fun time => oneActive_markedSingletonMass_le_absorption'
        (plan time) markedPlayer clockOwner (hactive time)
  have hsurvival : ∀ start,
      Tendsto (quittingJointSurvivalWeight plan start) atTop (nhds 0) := by
    intro start
    apply tendsto_zero_quittingJointSurvivalWeight_of_not_summable_absorption
    intro hsuffix
    apply habsorptionDiverges
    have hshift : Summable (fun offset =>
        quittingRootAbsorptionMass (plan (offset + start))) := by
      simpa [Nat.add_comm] using hsuffix
    exact (summable_nat_add_iff start).1 hshift
  have hselected : ∀ time,
      value time = fun who =>
        quittingRootSequenceTerminalValue reward plan who time :=
    eq_quittingRootSequenceTerminalValue_of_exact_bounded_path_of_jointSurvival_tendsto_zero
      reward plan value hsurvival hbound0 hreward hvalueBound hpolicy
  have hsupport :
      IsQuittingRootSequenceSupportApproxNash reward plan epsilon := by
    intro time
    have htail : quittingRootSequenceTailVector reward plan (time + 1) =
        value (time + 1) := by
      funext who
      change quittingRootSequenceTerminalValue reward plan who (time + 1) =
        value (time + 1) who
      exact (congrFun (hselected (time + 1)) who).symm
    rw [htail]
    exact (isQuittingSimplexRootSupportApproxNash_iff
      reward (value (time + 1)) epsilon (state time).2).1
        (hstateEdge time).1.2.1
  refine ⟨plan, hsupport, ?_, ?_, hactive⟩
  · change ¬Summable (fun time => quittingRootAbsorptionMass (plan time))
    exact habsorptionDiverges
  · intro target time
    rw [← congrFun (hselected time) target]
    exact hvalueLower time target

/-- **Divergent marked-prefix consumer.**  For every accuracy, compatible
one-active finite prefixes whose fixed singleton mark dominates one divergent
cumulative budget imply a uniform-equilibrium payoff. -/
theorem quittingGame_exists_uniformEquilibriumPayoff_of_oneActiveMarkedBudgetPrefixes
    [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (bound : ℝ)
    (hbound0 : 0 ≤ bound)
    (hreward : ∀ terminal who, |reward terminal who| ≤ bound)
    (hprefix : ∀ epsilon, 0 < epsilon →
      ∃ (markedPlayer clockOwner : ι) (budget : ℕ → ℝ),
        Tendsto budget atTop atTop ∧
        ∀ horizon,
          (compactBudgetedPrefixSolutionSet
            (quittingCirculationPathBox bound
              (fun who => quittingPunishmentValue reward who - epsilon))
            (IsQuittingKActiveCirculationPathEdge reward 1 epsilon 0)
            (fun point => quittingSimplexOpponentCoalitionMass
              point.2 markedPlayer {clockOwner})
            budget horizon).Nonempty) :
    ∃ payoff : Payoff ι,
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff := by
  apply quittingGame_exists_uniformEquilibriumPayoff_of_KActivePaths reward 1
  intro epsilon hepsilon
  obtain ⟨markedPlayer, clockOwner, budget, hbudget, hpref⟩ :=
    hprefix epsilon hepsilon
  let box := quittingCirculationPathBox bound
    (fun who => quittingPunishmentValue reward who - epsilon)
  let relation := IsQuittingKActiveCirculationPathEdge reward 1 epsilon 0
  let weight : QuittingNashBellmanPoint ι → ℝ := fun point =>
    quittingSimplexOpponentCoalitionMass
      point.2 markedPlayer {clockOwner}
  have hbox : IsCompact box :=
    quittingCirculationPathBox_isCompact bound
      (fun who => quittingPunishmentValue reward who - epsilon)
  have hgraph : IsClosed {edge : QuittingNashBellmanPoint ι ×
      QuittingNashBellmanPoint ι |
      edge.1 ∈ box ∧ edge.2 ∈ box ∧ relation edge.1 edge.2} := by
    simpa only [box, relation] using
      isClosed_quittingKActiveCirculationPathEdgeGraph reward bound
        (fun who => quittingPunishmentValue reward who - epsilon)
        1 epsilon 0
  have hweight : Continuous weight := by
    exact (continuous_quittingSimplexOpponentCoalitionMass
      markedPlayer {clockOwner}).comp
        (continuous_snd.comp continuous_id)
  obtain ⟨state, hstateBox, hstateEdge, hprefixBudget⟩ :=
    exists_infiniteChain_of_budgetedFinitePrefixes
      box relation weight budget hbox hgraph hweight
      (by simpa only [box, relation, weight] using hpref)
  obtain ⟨plan, hsupport, hdiverges, hir, hactive⟩ :=
    oneActiveMarkedBudgetPath_is_supportRationalDivergent
      reward bound epsilon markedPlayer clockOwner budget
        hbound0 hreward hbudget state
        (by simpa only [box] using hstateBox)
        (by simpa only [relation] using hstateEdge)
        (by simpa only [weight] using hprefixBudget)
  exact ⟨plan, hsupport, hdiverges, hir, hactive⟩

/-! ## Counterexample-facing exclusions -/

/-- A counterexample regime cannot admit cumulative-clock `K`-active prefix
families of the form consumed above, for any fixed `K`. -/
theorem QuittingCounterexampleRegime.not_KActiveAbsorptionBudgetPrefixes
    [Nonempty ι]
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (regime : QuittingCounterexampleRegime reward)
    (K : ℕ) (bound : ℝ)
    (hbound0 : 0 ≤ bound)
    (hreward : ∀ terminal who, |reward terminal who| ≤ bound) :
    ¬(∀ epsilon, 0 < epsilon →
      ∃ budget : ℕ → ℝ,
        Tendsto budget atTop atTop ∧
        ∀ horizon,
          (compactBudgetedPrefixSolutionSet
            (quittingCirculationPathBox bound
              (fun who => quittingPunishmentValue reward who - epsilon))
            (IsQuittingKActiveCirculationPathEdge reward K epsilon 0)
            (fun point => quittingSimplexAbsorptionMass point.2)
            budget horizon).Nonempty) := by
  intro hprefix
  exact regime.not_exists_uniformEquilibriumPayoff
    (quittingGame_exists_uniformEquilibriumPayoff_of_KActiveAbsorptionBudgetPrefixes
      reward K bound hbound0 hreward hprefix)

/-- In particular, a counterexample cannot retain one fixed one-active
singleton edge with a divergent cumulative clock on compatible prefixes at
every accuracy. -/
theorem QuittingCounterexampleRegime.not_oneActiveMarkedBudgetPrefixes
    [Nonempty ι]
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (regime : QuittingCounterexampleRegime reward)
    (bound : ℝ)
    (hbound0 : 0 ≤ bound)
    (hreward : ∀ terminal who, |reward terminal who| ≤ bound) :
    ¬(∀ epsilon, 0 < epsilon →
      ∃ (markedPlayer clockOwner : ι) (budget : ℕ → ℝ),
        Tendsto budget atTop atTop ∧
        ∀ horizon,
          (compactBudgetedPrefixSolutionSet
            (quittingCirculationPathBox bound
              (fun who => quittingPunishmentValue reward who - epsilon))
            (IsQuittingKActiveCirculationPathEdge reward 1 epsilon 0)
            (fun point => quittingSimplexOpponentCoalitionMass
              point.2 markedPlayer {clockOwner})
            budget horizon).Nonempty) := by
  intro hprefix
  exact regime.not_exists_uniformEquilibriumPayoff
    (quittingGame_exists_uniformEquilibriumPayoff_of_oneActiveMarkedBudgetPrefixes
      reward bound hbound0 hreward hprefix)

end GameTheory
