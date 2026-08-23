/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Terminal.TerminalExploitabilityWitness
import UniformEquilibrium.Quitting.Bellman.Finite.PunishmentFloorInfiniteOrbit

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
whose charge is at least a positive threshold, where `C` is the regime's
common prefix-charge bound.

The same prefix bound has an all-orbits consequence.  Every arbitrary
infinite exact punishment-floor Nash--Bellman orbit has total absorption at
most the common bound.  Its absorption masses, and every player's individual
quit probabilities, are summable; the roots therefore converge
coordinatewise to all-Continue.

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

/-- Every finite partial absorption sum along every exact punishment-floor
orbit is bounded by the one common regime constant. -/
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
the same regime constant. -/
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
least the regime's common terminal gap.

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
