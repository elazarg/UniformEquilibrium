/-
Copyright (c) 2026 UniformEquilibrium contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: UniformEquilibrium contributors
-/

import UniformEquilibrium.Quitting.Bellman.Finite.BooleanMobiusAdapter
import UniformEquilibrium.Quitting.Paths.LiveTail
import UniformEquilibrium.Quitting.Root.TerminalSemanticMoment
import UniformEquilibrium.Quitting.Root.OpponentCoalitionMass

/-! # The terminal coalition law of an absorbing stationary profile -/

noncomputable section

namespace GameTheory

open Math.Probability

/-- Positive absorption identifies the actual stationary terminal coalition
law with the conditional one-row product law. -/
theorem quittingTerminalOutcomeMass_stationary_some_eq_conditionalCoalitionMass
    {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (root : ι → PMF Bool)
    (hquit : quittingStationaryContinueMass root < 1)
    (terminal : {S : Finset ι // S.Nonempty}) :
    quittingTerminalOutcomeMass reward (quittingStationaryProfile reward root) (some terminal) =
      quittingRootCoalitionMass root terminal.1 / quittingRootAbsorptionMass root := by
  let indicator : {S : Finset ι // S.Nonempty} → Payoff ι :=
    fun outcome _ ↦ if outcome = terminal then 1 else 0
  let profile := quittingStationaryProfile indicator root
  obtain ⟨observer⟩ := (inferInstance : Nonempty ι)
  have hmoment := congrFun (quittingTerminalRewardMoment_outcomeMass indicator profile) observer
  have hmass : quittingAbsorbedMassLimit reward
      (quittingStationaryProfile reward root) terminal =
        quittingAbsorbedMassLimit indicator profile terminal :=
    quittingAbsorbedMassLimit_reward_irrelevant reward indicator
      (quittingStationaryProfile reward root) terminal
  have hvalue : quittingAbsorbedMassLimit indicator profile terminal =
      quittingTerminalPayoff indicator profile observer := by
    rw [← hmoment]
    unfold quittingTerminalRewardMoment quittingTerminalOutcomeReward quittingTerminalOutcomeMass
    rw [Fintype.sum_option]
    simp [indicator, mul_ite]
  change quittingAbsorbedMassLimit reward (quittingStationaryProfile reward root) terminal = _
  rw [hmass, hvalue]
  change quittingTerminalPayoff indicator (quittingStationaryProfile indicator root) observer = _
  rw [quittingTerminalPayoff_stationary_eq_absorbingContribution_div indicator root observer hquit,
    quittingRootAbsorbingContribution_eq_sum_nonemptyCoalitionMass]
  simp [indicator, mul_ite, quittingRootCoalitionMass, quittingRootAbsorptionMass]
  rfl

end GameTheory
