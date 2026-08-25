/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Classification.Existence.WellSupportedAbsorbingSequence
import UniformEquilibrium.Quitting.Bellman.Finite.PunishmentFloorForward
import UniformEquilibrium.Quitting.Examples.SolanVieilleBoundaryNonstationarity
import UniformEquilibrium.Quitting.Paths.SupportWitnessPeriodic

/-!
# AGKRS Theorem 3.4 on the Solan--Vieille boundary table

This is an adversarial bounded-instance audit of the three branches in AGKRS
Theorem 3.4.  The explicit rational four-player boundary table has an exact
period-two terminal equilibrium, but its stationary branch fails below one
positive accuracy threshold.  The same period-two Nash--Bellman block does
give the literal sequentially-perfect absorbing branch.

Thus this hard nonstationary example is not a counterexample to Theorem 3.4:
it eliminates `S.1` and lands in `S.3`.  No assertion about `S.2` is made.
-/

noncomputable section

namespace GameTheory
namespace AGKRSTheorem34BoundaryAudit

open StochasticGame

open SolanVieilleBoundary
open FourPlayerPairedSingleton

/-- The two rows of the checked period-two Nash--Bellman block. -/
def cycle : Fin 2 → Fin 4 → PMF Bool :=
  quittingCyclicContinuationBlockCycle 1 periodTwoBlock

/-- The two displayed continuation values of the checked block. -/
def value : Fin 2 → Payoff (Fin 4) :=
  quittingCyclicContinuationBlockValue 1 periodTwoBlock

/-- The period-two roots repeated forever from the odd phase. -/
def roots : ℕ → Fin 4 → PMF Bool :=
  quittingCyclicRootSequence cycle 0

theorem value_eq_cyclicTerminalValue :
    value = quittingCyclicTerminalValue boundaryReward cycle := by
  apply eq_quittingCyclicTerminalValue_of_rootSuccessorPayoff_of_absorbing
  · exact quittingCyclicContinuationBlock_policy boundaryReward oddValue 1
      periodTwoBlock periodTwoBlock_isQuittingCyclicContinuationBlock
  · exact quittingCyclicContinuationBlock_prod_continueMass_lt_one
      boundaryReward oddValue 1 periodTwoBlock
        periodTwoBlock_isQuittingCyclicContinuationBlock

/-- The actual tail value of the repeated roots is the displayed next value
of the Nash--Bellman block. -/
theorem rootSequenceTailVector_eq (time : ℕ) :
    quittingRootSequenceTailVector boundaryReward roots (time + 1) =
      value (finRotate 2 (quittingCyclicOrbit 0 time)) := by
  funext who
  change quittingRootSequenceTerminalValue boundaryReward
      (quittingCyclicRootSequence cycle 0) who (time + 1) = _
  rw [quittingRootSequenceTerminalValue_cyclic_eq]
  rw [← value_eq_cyclicTerminalValue]
  rw [quittingCyclicOrbit_succ]

/-- Every repeated row is support-perfect at zero error against its actual
tail, not merely against a formal Bellman annotation. -/
theorem roots_supportExact :
    IsQuittingRootSequenceSupportApproxNash boundaryReward roots 0 := by
  intro time
  have hnash := quittingCyclicContinuationBlock_rootNash boundaryReward
    oddValue 1 periodTwoBlock periodTwoBlock_isQuittingCyclicContinuationBlock
    (quittingCyclicOrbit (0 : Fin 2) time)
  have hsupport := isQuittingRootSupportApproxNash_zero_of_isZeroNash
    boundaryReward _ _ hnash
  rw [rootSequenceTailVector_eq]
  change IsQuittingRootSupportApproxNash boundaryReward
    (value (finRotate 2 (quittingCyclicOrbit 0 time))) 0
    (cycle (quittingCyclicOrbit 0 time))
  exact hsupport

/-- The repeated roots absorb completely. -/
theorem roots_completelyAbsorbing : IsCompletelyAbsorbing roots := by
  apply isCompletelyAbsorbing_of_not_summable_totalAbsorptionCharge
  apply not_summable_quittingTotalAbsorptionCharge_cyclicRootSequence_of_pos
    cycle (0 : Fin 2)
  rw [cycle, quittingCyclicContinuationBlockCycle_periodTwoBlock]
  exact oddRoot_absorption_pos

/-- The hard four-player boundary table satisfies the literal `S.3` branch
at every positive tolerance. -/
theorem sequentiallyPerfectAbsorbingExistence :
    QuittingSequentiallyεPerfectAbsorbingExistence boundaryReward := by
  intro ε hε
  refine ⟨roots, roots_completelyAbsorbing, fun time ↦ ?_⟩
  apply quittingRowεPerfect_of_supportApproxNash hε.le
  exact (roots_supportExact time).mono hε.le

/-- The same table fails the literal `S.1` branch. -/
theorem not_stationaryEquilibriumExistence :
    ¬QuittingStationaryεEquilibriumExistence boundaryReward := by
  obtain ⟨ε₀, hε₀, hgap⟩ := no_stationary_terminalApproximateEquilibrium
  intro hstationary
  obtain ⟨root, hnash⟩ := hstationary (ε₀ / 2) (by linarith)
  exact hgap (ε₀ / 2) (by linarith) (by linarith) ⟨root, hnash⟩

/-- The table has approximate equilibria at every positive accuracy, witnessed
by one exact period-two profile. -/
theorem approximateEquilibriumExistence :
    ∀ ε : ℝ, 0 < ε → ∃ profile : (quittingGame boundaryReward).BehaviorProfile,
      (quittingGame boundaryReward).IsεAsymptoticNash
        (quittingTerminalPayoff boundaryReward) ε profile := by
  intro ε hε
  exact ⟨periodTwoProfile, periodTwoProfile_isExactTerminalNash.mono hε.le⟩

/-- Bounded-instance audit package: the premise holds, `S.1` fails, and
`S.3` holds in its actual-tail semantics. -/
theorem premise_and_not_stationary_and_sequential :
    (∀ ε : ℝ, 0 < ε → ∃ profile : (quittingGame boundaryReward).BehaviorProfile,
      (quittingGame boundaryReward).IsεAsymptoticNash
        (quittingTerminalPayoff boundaryReward) ε profile) ∧
      ¬QuittingStationaryεEquilibriumExistence boundaryReward ∧
      QuittingSequentiallyεPerfectAbsorbingExistence boundaryReward :=
  ⟨approximateEquilibriumExistence, not_stationaryEquilibriumExistence,
    sequentiallyPerfectAbsorbingExistence⟩

end AGKRSTheorem34BoundaryAudit
end GameTheory
