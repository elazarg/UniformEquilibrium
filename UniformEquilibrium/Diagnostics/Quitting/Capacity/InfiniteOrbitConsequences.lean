/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Terminal.TerminalExploitabilityWitness
import UniformEquilibrium.Quitting.Bellman.Finite.PunishmentFloorInfiniteOrbit
import UniformEquilibrium.Quitting.Bellman.Finite.PunishmentFloorAdmissibleChargedRelation
import UniformEquilibrium.Quitting.Boundary.Repair.FixedTailUniformAbsorption

/-!
# Search consequences of the quitting terminal exploitability witness

This module extracts local and finite rejection tests from the global
terminal exploitability witness.  They are intended for exact search code: a proposed
Nash--Bellman predecessor graph can be rejected without constructing a
strategy once it exhibits a reachable positive-charge return.

The strongest graph restriction is local.  Every edge lying on a directed
cycle has zero absorption charge.  Hence every positive-charge edge is
strictly transient, and strictly decreases the canonical budget-to-go
potential.  Quantitatively, a path contains at most `C / threshold` edges
whose charge is at least a positive threshold, where `C` is the common
common prefix-charge bound.

The same prefix bound has an all-orbits consequence.  Every arbitrary
infinite exact punishment-floor Nash--Bellman orbit has total absorption at
most the common bound.  Its absorption masses, and every player's individual
quit probabilities, are summable; the roots therefore converge
coordinatewise to all-Continue.  More sharply, every visit to a state with a
fixed positive singleton deficit spends a fixed positive amount of that same
budget, even after arbitrary exits, re-entry, and changes of deficit owner.
Consequently every coherent infinite orbit drives all one-sided singleton
deficits to zero.

The cycle-rejection statements concern the exact punishment-floor reachable
relation; the all-orbits statement uses the larger finite-prefix family whose
initial value may merely dominate the floor.  A numerical near-cycle is not
an exact rejection certificate unless its Bellman, Nash, endpoint, and return
equalities have been certified.
-/

noncomputable section

namespace GameTheory

open Filter
open Math.ChargedPathBudget

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}

/-- A payoff has singleton deficit at least `eta` when some player is at least
`eta` below that player's own singleton reward. -/
def HasQuittingSingletonDeficitAtLeast
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (eta : ℝ) (payoff : Payoff ι) : Prop :=
  ∃ who, payoff who ≤ reward (quittingSingletonTerminal who) who - eta

namespace QuittingPunishmentFloorAdmissibleChargedRelation

private abbrev AdmissibleRelation :=
  quittingPunishmentFloorAdmissibleChargedRelation reward

/-- Number of outgoing path edges whose tail payoff has some singleton deficit
at least `eta`.  Re-entry into the deficit region is counted again. -/
noncomputable def singletonDeficitVisitCount
    (eta : ℝ) {source target : QuittingPunishmentFloorAdmissibleState reward}
    (path : AdmissibleRelation.Path source target) : ℕ :=
  path.sourceVisitCount fun state =>
    HasQuittingSingletonDeficitAtLeast reward eta state.1.1.1

/-- Every visit to an `eta`-singleton-deficit tail pays the same explicit
absorption charge.  The path may leave and re-enter the deficit region, and
the player witnessing the deficit may change at every visit. -/
theorem singletonDeficitVisitCount_mul_ratio_le_chargeSum
    (eta : ℝ) (heta : 0 < eta)
    {source target : QuittingPunishmentFloorAdmissibleState reward}
    (path : AdmissibleRelation.Path source target) :
    (singletonDeficitVisitCount eta path : ℝ) *
        (eta / (eta + 2 * quittingRewardBound reward)) ≤ path.chargeSum := by
  unfold singletonDeficitVisitCount
  apply path.sourceVisitCount_mul_le_chargeSum
  intro edge hedge
  rcases hedge with ⟨who, hgap⟩
  exact gap_div_le_quittingRootAbsorptionMass_of_isZeroEndpointNash
    reward edge.tail.1.1.1 edge.toBoxEdge.root who heta
    (abs_reward_le_quittingRewardBound reward) hgap (by
      simpa only [QuittingPunishmentFloorAdmissibleEdge.toBoxEdge,
        QuittingPunishmentFloorBoxEdge.root] using edge.exactEdge.2)

end QuittingPunishmentFloorAdmissibleChargedRelation

open QuittingPunishmentFloorAdmissibleChargedRelation

namespace QuittingTerminalExploitabilityWitness

private abbrev ReachableRelation :=
  quittingPunishmentFloorReachableChargedRelation reward

/-- A counterexample path can cross a positive absorption threshold only
finitely often, with an explicit bound supplied by the common prefix budget.

This avoids division and rounding: search code can compare the integer count
after coercion directly with `prefixChargeBound / threshold`. -/
theorem highChargeCount_mul_threshold_le_prefixChargeBound
    (witness : QuittingTerminalExploitabilityWitness reward)
    (threshold : ℝ)
    {source target : QuittingPunishmentFloorReachableState reward}
    (path : ReachableRelation.Path source target) :
    (path.highChargeCount threshold : ℝ) * threshold ≤
      quittingPunishmentFloorPrefixChargeBound reward := by
  exact (path.highChargeCount_mul_le_chargeSum threshold).trans
    (witness.reachablePath_chargeSum_le_prefixChargeBound path)

/-- The same threshold-count restriction holds on the larger family of all
exact punishment-floor finite-prefix certificates, including those whose
initial value merely dominates the floor rather than equals its anchor. -/
theorem highAbsorptionStageCount_mul_threshold_le_prefixChargeBound
    (witness : QuittingTerminalExploitabilityWitness reward)
    (cert : QuittingPunishmentFloorFinitePrefix reward)
    (threshold : ℝ) :
    (cert.highAbsorptionStageCount threshold : ℝ) * threshold ≤
      quittingPunishmentFloorPrefixChargeBound reward := by
  exact (cert.highAbsorptionStageCount_mul_le_charge threshold).trans
    (witness.prefixCharge_le cert)

/-- Under a terminal exploitability witness, every exact floor-admissible path
has a uniform budget on all visits to a fixed singleton-deficit region.  The
bound counts arbitrary re-entry and changing deficit owners. -/
theorem admissiblePath_singletonDeficitVisitCount_mul_ratio_le_prefixChargeBound
    (witness : QuittingTerminalExploitabilityWitness reward)
    (eta : ℝ) (heta : 0 < eta)
    {source target : QuittingPunishmentFloorAdmissibleState reward}
    (path : (quittingPunishmentFloorAdmissibleChargedRelation reward).Path
      source target) :
    (QuittingPunishmentFloorAdmissibleChargedRelation.singletonDeficitVisitCount
        eta path : ℝ) *
          (eta / (eta + 2 * quittingRewardBound reward)) ≤
      quittingPunishmentFloorPrefixChargeBound reward := by
  exact
    (singletonDeficitVisitCount_mul_ratio_le_chargeSum eta heta path).trans
      (by
        rw [← pathToFinitePrefix_charge path]
        exact witness.prefixCharge_le _)

/-- Division form of the uniform singleton-deficit visit budget. -/
theorem admissiblePath_singletonDeficitVisitCount_le
    (witness : QuittingTerminalExploitabilityWitness reward)
    (eta : ℝ) (heta : 0 < eta)
    {source target : QuittingPunishmentFloorAdmissibleState reward}
    (path : (quittingPunishmentFloorAdmissibleChargedRelation reward).Path
      source target) :
    (QuittingPunishmentFloorAdmissibleChargedRelation.singletonDeficitVisitCount
        eta path : ℝ) ≤
      quittingPunishmentFloorPrefixChargeBound reward /
        (eta / (eta + 2 * quittingRewardBound reward)) := by
  have hdenominator : 0 < eta + 2 * quittingRewardBound reward := by
    linarith [quittingRewardBound_nonneg reward]
  apply (le_div_iff₀ (div_pos heta hdenominator)).2
  exact witness.admissiblePath_singletonDeficitVisitCount_mul_ratio_le_prefixChargeBound
    eta heta path

/-- Every finite partial absorption sum along every exact punishment-floor
orbit is bounded by the common prefix-charge bound. -/
theorem infiniteOrbit_partialAbsorption_le_prefixChargeBound
    (witness : QuittingTerminalExploitabilityWitness reward)
    (orbit : QuittingPunishmentFloorInfiniteOrbit reward)
    (horizon : ℕ) :
    orbit.partialAbsorption horizon ≤
      quittingPunishmentFloorPrefixChargeBound reward := by
  rw [← orbit.toFinitePrefix_charge horizon]
  exact witness.prefixCharge_le (orbit.toFinitePrefix horizon)

/-- Every arbitrary infinite exact punishment-floor orbit has summable total
absorption mass.  This is an all-orbits statement, not a property only of the
classically selected predecessor orbit. -/
theorem infiniteOrbit_absorptionMass_summable
    (witness : QuittingTerminalExploitabilityWitness reward)
    (orbit : QuittingPunishmentFloorInfiniteOrbit reward) :
    Summable (fun time =>
      quittingRootAbsorptionMass (orbit.roots time)) := by
  refine summable_of_sum_range_le
    (c := quittingPunishmentFloorPrefixChargeBound reward)
    (fun time => orbit.absorptionMass_nonneg time) ?_
  intro horizon
  simpa only [QuittingPunishmentFloorInfiniteOrbit.partialAbsorption] using
    witness.infiniteOrbit_partialAbsorption_le_prefixChargeBound orbit horizon

/-- The total absorption mass of every arbitrary exact orbit is bounded by
the same common prefix-charge bound. -/
theorem infiniteOrbit_tsum_absorptionMass_le_prefixChargeBound
    (witness : QuittingTerminalExploitabilityWitness reward)
    (orbit : QuittingPunishmentFloorInfiniteOrbit reward) :
    ∑' time, quittingRootAbsorptionMass (orbit.roots time) ≤
      quittingPunishmentFloorPrefixChargeBound reward := by
  apply Real.tsum_le_of_sum_range_le orbit.absorptionMass_nonneg
  intro horizon
  simpa only [QuittingPunishmentFloorInfiniteOrbit.partialAbsorption] using
    witness.infiniteOrbit_partialAbsorption_le_prefixChargeBound orbit horizon

/-- Absorption mass tends to zero along every arbitrary exact
punishment-floor orbit. -/
theorem infiniteOrbit_absorptionMass_tendsto_zero
    (witness : QuittingTerminalExploitabilityWitness reward)
    (orbit : QuittingPunishmentFloorInfiniteOrbit reward) :
    Tendsto (fun time => quittingRootAbsorptionMass (orbit.roots time))
      atTop (nhds 0) :=
  (witness.infiniteOrbit_absorptionMass_summable orbit).tendsto_atTop_zero

/-- Along every arbitrary exact floor-admissible orbit, each player's positive
singleton deficit tends to zero.  This asserts neither convergence of payoff
states nor recurrence of stored roots. -/
theorem infiniteOrbit_singletonDeficit_tendsto_zero
    (witness : QuittingTerminalExploitabilityWitness reward)
    (orbit : QuittingPunishmentFloorInfiniteOrbit reward)
    (who : ι) :
    Tendsto (fun time => max 0
        (reward (quittingSingletonTerminal who) who - orbit.value time who))
      atTop (nhds 0) := by
  rw [Metric.tendsto_atTop]
  intro eta heta
  have hratio : 0 < eta / (eta + 2 * quittingRewardBound reward) := by
    apply div_pos heta
    linarith [quittingRewardBound_nonneg reward]
  obtain ⟨start, hstart⟩ := Metric.tendsto_atTop.mp
    (witness.infiniteOrbit_absorptionMass_tendsto_zero orbit)
      (eta / (eta + 2 * quittingRewardBound reward)) hratio
  refine ⟨start, fun time htime => ?_⟩
  have habsorption : quittingRootAbsorptionMass (orbit.roots time) <
      eta / (eta + 2 * quittingRewardBound reward) := by
    have hdist := hstart time htime
    rw [Real.dist_eq, sub_zero,
      abs_of_nonneg (orbit.absorptionMass_nonneg time)] at hdist
    exact hdist
  have hgap : reward (quittingSingletonTerminal who) who -
      orbit.value time who < eta := by
    by_contra hnot
    have hlower := gap_div_le_quittingRootAbsorptionMass_of_isZeroEndpointNash
      reward (orbit.value time) (orbit.roots time) who heta
      (abs_reward_le_quittingRewardBound reward) (by linarith)
      ((isεQuittingRootEndpointNash_iff_isεQuittingRootNash
        reward (orbit.value time) 0 (orbit.roots time)).2
          (orbit.exactNash time))
    linarith
  rw [Real.dist_eq, sub_zero,
    abs_of_nonneg (le_max_left 0
      (reward (quittingSingletonTerminal who) who - orbit.value time who))]
  exact max_lt heta hgap

/-- The whole vector of one-sided singleton deficits tends coordinatewise to
zero along every arbitrary exact floor-admissible orbit. -/
theorem infiniteOrbit_singletonDeficits_tendsto_zero
    (witness : QuittingTerminalExploitabilityWitness reward)
    (orbit : QuittingPunishmentFloorInfiniteOrbit reward) :
    Tendsto (fun time who => max 0
        (reward (quittingSingletonTerminal who) who - orbit.value time who))
      atTop (nhds 0) := by
  rw [tendsto_pi_nhds]
  exact fun who => witness.infiniteOrbit_singletonDeficit_tendsto_zero orbit who

/-- Every player's quit probability tends to zero along every arbitrary exact
punishment-floor orbit. -/
theorem infiniteOrbit_quitProbability_tendsto_zero
    (witness : QuittingTerminalExploitabilityWitness reward)
    (orbit : QuittingPunishmentFloorInfiniteOrbit reward)
    (who : ι) :
    Tendsto (fun time => (orbit.roots time who true).toReal)
      atTop (nhds 0) := by
  apply squeeze_zero
  · exact fun time => orbit.quitProbability_nonneg time who
  · exact fun time => orbit.quitProbability_le_absorptionMass time who
  · exact witness.infiniteOrbit_absorptionMass_tendsto_zero orbit

/-- Each individual player's quit probabilities are themselves summable
along every arbitrary exact punishment-floor orbit. -/
theorem infiniteOrbit_quitProbability_summable
    (witness : QuittingTerminalExploitabilityWitness reward)
    (orbit : QuittingPunishmentFloorInfiniteOrbit reward)
    (who : ι) :
    Summable (fun time => (orbit.roots time who true).toReal) :=
  Summable.of_nonneg_of_le
    (fun time => orbit.quitProbability_nonneg time who)
    (fun time => orbit.quitProbability_le_absorptionMass time who)
    (witness.infiniteOrbit_absorptionMass_summable orbit)

/-- Equivalently, every player's continuation probability tends to one: all
arbitrary exact punishment-floor roots converge coordinatewise to the
all-Continue root. -/
theorem infiniteOrbit_continueProbability_tendsto_one
    (witness : QuittingTerminalExploitabilityWitness reward)
    (orbit : QuittingPunishmentFloorInfiniteOrbit reward)
    (who : ι) :
    Tendsto (fun time => (orbit.roots time who false).toReal)
      atTop (nhds 1) := by
  have hquit := witness.infiniteOrbit_quitProbability_tendsto_zero orbit who
  have hidentity : (fun time => (orbit.roots time who false).toReal) =
      fun time => 1 - (orbit.roots time who true).toReal := by
    funext time
    linarith [quittingRoot_continueProbability_add_quitProbability
      (orbit.roots time) who]
  rw [hidentity]
  simpa using tendsto_const_nhds.sub hquit

/-- **Combined all-orbits counterexample capstone.**  Along every arbitrary
exact punishment-floor orbit, every sufficiently late current root has
arbitrarily small absorption, yet the actual root-sequence behavior profile
starting at that date still admits a unilateral terminal improvement of at
least the witness's common terminal gap.

The terminal payoffs here are the genuine stochastic-game terminal payoffs of
`quittingRootSequenceProfile`.  No equality with `orbit.value time` is used or
claimed: the stored orbit values certify exact one-stage Nash--Bellman edges,
whereas identifying them with realized continuation payoffs is precisely the
separate realization problem.  The exploiting player and deviation may vary
with time. -/
theorem eventually_smallAbsorption_and_terminalExploitability
    (witness : QuittingTerminalExploitabilityWitness reward)
    (orbit : QuittingPunishmentFloorInfiniteOrbit reward)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ time in atTop,
      quittingRootAbsorptionMass (orbit.roots time) < ε ∧
        ∃ (who : ι) (dev : (quittingGame reward).BehaviorStrategy who),
          quittingTerminalPayoff reward
              (quittingRootSequenceProfile reward orbit.roots time) who +
              witness.terminalGap ≤
            quittingTerminalPayoff reward
              (Function.update
                (quittingRootSequenceProfile reward orbit.roots time)
                who dev) who := by
  have hsmall : ∀ᶠ time in atTop,
      quittingRootAbsorptionMass (orbit.roots time) < ε :=
    (witness.infiniteOrbit_absorptionMass_tendsto_zero orbit).eventually
      (Iio_mem_nhds hε)
  filter_upwards [hsmall] with time htime
  exact ⟨htime, witness.terminalExploitability
    (quittingRootSequenceProfile reward orbit.roots time)⟩

/-- A positive-charge edge strictly decreases the canonical budget-to-go
potential. -/
theorem canonicalPotential_strict_decrease_of_positiveCharge
    (witness : QuittingTerminalExploitabilityWitness reward)
    (edge : QuittingPunishmentFloorReachableEdge reward)
    (hpositive : 0 < edge.toBoxEdge.absorptionCharge) :
    quittingPunishmentFloorReachablePotential reward edge.current <
      quittingPunishmentFloorReachablePotential reward edge.tail := by
  have hdecrement := witness.canonicalPotential_predecessor_decrement edge
  linarith

/-- Every edge admitting a return path has zero absorption charge.  Thus all
edges internal to a directed strongly connected component are zero-charge. -/
theorem absorptionCharge_eq_zero_of_returnPath
    (witness : QuittingTerminalExploitabilityWitness reward)
    (edge : QuittingPunishmentFloorReachableEdge reward)
    (returnPath : ReachableRelation.Path edge.current edge.tail) :
    edge.toBoxEdge.absorptionCharge = 0 := by
  let cycle : ReachableRelation.Path edge.tail edge.tail :=
    ChargedRelation.Path.cons edge returnPath
  have hcycle : cycle.chargeSum = 0 :=
    witness.reachable_cycle_chargeSum_eq_zero cycle
  have hreturn := returnPath.chargeSum_nonneg
  change edge.toBoxEdge.absorptionCharge + returnPath.chargeSum = 0 at hcycle
  exact le_antisymm (by linarith)
    (QuittingPunishmentFloorBoxEdge.absorptionCharge_nonneg edge.toBoxEdge)

end QuittingTerminalExploitabilityWitness

end GameTheory
