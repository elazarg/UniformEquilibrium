/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Research.Quitting.KActiveMarkedAtomCompactPath

/-!
# A persistent one-active marked atom is already a UE certificate

The exceptional five-role graph does not require cardinal compression if its
fixed singleton atom can be carried through compatible chronological finite
prefixes.  On a one-active root, a positive marked singleton atom is the
whole one-stage absorption mass.  A uniform marked floor therefore supplies
the positive clock needed to identify the compact Bellman path with its
literal terminal payoff path and to make total absorption nonsummable.

The main theorem below consumes, for each accuracy, finite prefixes of every
depth with one fixed marked singleton and a positive floor.  It returns a
uniform-equilibrium payoff directly.  Thus the unresolved producer is
precisely prefix compatibility/mark retention; no `5 -> 4` deletion is needed
on this branch once that producer is available.
-/

noncomputable section

namespace GameTheory

open Finset Set StochasticGame Math.Probability Math.PMFProduct
open Math.ProbabilityMassFunction Math.Topology

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- In the one-active stratum, a positive lower bound on one marked singleton
opponent atom is automatically the same lower bound on total absorption. -/
theorem oneActive_markedSingletonMass_le_absorption
    (root : ι → PMF Bool) (markedPlayer clockOwner : ι) (eta : ℝ)
    (heta : 0 < eta)
    (hactive : HasQuittingSupportCardAtMost 1 root)
    (hmarked : eta ≤
      quittingOpponentCoalitionMass root markedPlayer {clockOwner}) :
    eta ≤ quittingRootAbsorptionMass root := by
  have hmass : 0 <
      quittingOpponentCoalitionMass root markedPlayer {clockOwner} :=
    heta.trans_le hmarked
  rw [← quittingOpponentCoalitionMass_singleton_eq_absorption_of_oneActive
    root markedPlayer clockOwner hactive hmass]
  exact hmarked

/-- Compact finite-prefix extraction followed by the terminal-law decoder.
The returned plan retains the fixed marked atom, is one-active, is
support-approximately Nash against its actual tails, has a divergent
absorption clock, and satisfies the punishment floors. -/
theorem exists_oneActiveMarkedSingletonSupportRationalDivergentPath_of_finitePrefixes
    [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (bound : ℝ) (markedPlayer clockOwner : ι)
    (eta epsilon edgeCharge : ℝ)
    (hreward : ∀ terminal who, |reward terminal who| ≤ bound)
    (heta : 0 < eta)
    (hprefix : ∀ horizon,
      (compactFinitePrefixSolutionSet
        (quittingCirculationPathBox bound
          (fun who => quittingPunishmentValue reward who - epsilon))
        (IsQuittingKActiveMarkedAtomCirculationPathEdge reward 1
          markedPlayer {clockOwner} eta epsilon edgeCharge)
        horizon).Nonempty) :
    ∃ plan : ℕ → ι → PMF Bool,
      IsQuittingRootSequenceSupportApproxNash reward plan epsilon ∧
      ¬Summable (quittingTotalAbsorptionCharge plan) ∧
      (∀ target time,
        quittingPunishmentValue reward target - epsilon ≤
          quittingRootSequenceTerminalValue reward plan target time) ∧
      (∀ time, HasQuittingSupportCardAtMost 1 (plan time)) ∧
      ∀ time, eta ≤
        quittingOpponentCoalitionMass
          (plan time) markedPlayer {clockOwner} := by
  obtain ⟨state, hstateBox, hstateEdge⟩ :=
    exists_chronologicalKActiveMarkedAtomPath_of_finitePrefixes
      reward bound
      (fun who => quittingPunishmentValue reward who - epsilon)
      1 markedPlayer {clockOwner} eta epsilon edgeCharge hprefix
  let value : ℕ → Payoff ι := fun time => (state time).1
  let plan : ℕ → ι → PMF Bool := fun time =>
    quittingRootOfSimplex (state time).2
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
      1 (state time).2 (hstateEdge time).2.1
  have hmarked : ∀ time, eta ≤
      quittingOpponentCoalitionMass
        (plan time) markedPlayer {clockOwner} := by
    intro time
    exact (hstateEdge time).2.2
  have habsorption : ∀ time,
      eta ≤ quittingRootAbsorptionMass (plan time) := by
    intro time
    exact oneActive_markedSingletonMass_le_absorption
      (plan time) markedPlayer clockOwner eta heta
        (hactive time) (hmarked time)
  have hselected : ∀ time,
      value time = fun who =>
        quittingRootSequenceTerminalValue reward plan who time :=
    eq_quittingRootSequenceTerminalValue_of_exact_bounded_path_of_absorption_lower
      reward plan value heta habsorption hreward hvalueBound hpolicy
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
  have hdiverges : ¬Summable (quittingTotalAbsorptionCharge plan) := by
    apply not_summable_quittingTotalAbsorptionCharge_of_uniform_lower
      plan heta
    intro time
    simpa [quittingTotalAbsorptionCharge] using habsorption time
  refine ⟨plan, hsupport, hdiverges, ?_, hactive, hmarked⟩
  intro target time
  rw [← congrFun (hselected time) target]
  exact hvalueLower time target

/-- **Persistent marked-prefix consumer.**  If at every accuracy some fixed
one-active singleton mark has a positive quantitative floor on compatible
prefixes of every depth, the quitting game already has a uniform-equilibrium
payoff.  Labels and floors may depend on the requested accuracy; they only
have to be fixed across the prefixes used for that one compact extraction. -/
theorem quittingGame_exists_uniformEquilibriumPayoff_of_oneActiveMarkedPrefixes
    [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (bound : ℝ)
    (hreward : ∀ terminal who, |reward terminal who| ≤ bound)
    (hprefix : ∀ epsilon, 0 < epsilon →
      ∃ (markedPlayer clockOwner : ι) (eta edgeCharge : ℝ),
        0 < eta ∧
        ∀ horizon,
          (compactFinitePrefixSolutionSet
            (quittingCirculationPathBox bound
              (fun who => quittingPunishmentValue reward who - epsilon))
            (IsQuittingKActiveMarkedAtomCirculationPathEdge reward 1
              markedPlayer {clockOwner} eta epsilon edgeCharge)
            horizon).Nonempty) :
    ∃ payoff : Payoff ι,
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff := by
  apply quittingGame_exists_uniformEquilibriumPayoff_of_KActivePaths reward 1
  intro epsilon hepsilon
  obtain ⟨markedPlayer, clockOwner, eta, edgeCharge, heta, hpref⟩ :=
    hprefix epsilon hepsilon
  obtain ⟨plan, hsupport, hdiverges, hir, hactive, _hmarked⟩ :=
    exists_oneActiveMarkedSingletonSupportRationalDivergentPath_of_finitePrefixes
      reward bound markedPlayer clockOwner eta epsilon edgeCharge
        hreward heta hpref
  exact ⟨plan, hsupport, hdiverges, hir, hactive⟩

end GameTheory
