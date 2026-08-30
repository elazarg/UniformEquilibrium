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
# Existence branches realized by the Solan--Vieille boundary table

The explicit rational four-player boundary table has an exact period-two
terminal equilibrium, but stationary approximate equilibria fail below one
positive accuracy threshold.  The same period-two Nash--Bellman block gives
the literal sequentially-perfect absorbing existence property.

The capstone packages the three literal properties proved here: approximate
equilibrium existence, failure of stationary equilibrium existence, and
sequentially-perfect absorbing existence.  It makes no claim about any other
existence branch.
-/

noncomputable section

namespace GameTheory
namespace SolanVieilleBoundary

open StochasticGame

open FourPlayerPairedSingleton

/-- The two rows of the checked period-two Nash--Bellman block. -/
def boundaryPeriodTwoCycle : Fin 2 → Fin 4 → PMF Bool :=
  quittingCyclicContinuationBlockCycle 1 periodTwoBlock

/-- The two displayed continuation values of the checked block. -/
def boundaryPeriodTwoValue : Fin 2 → Payoff (Fin 4) :=
  quittingCyclicContinuationBlockValue 1 periodTwoBlock

/-- The period-two roots repeated forever from the odd phase. -/
def boundaryPeriodTwoRoots : ℕ → Fin 4 → PMF Bool :=
  quittingCyclicRootSequence boundaryPeriodTwoCycle 0

theorem boundaryPeriodTwoValue_eq_cyclicTerminalValue :
    boundaryPeriodTwoValue =
      quittingCyclicTerminalValue boundaryReward boundaryPeriodTwoCycle := by
  apply eq_quittingCyclicTerminalValue_of_rootSuccessorPayoff_of_absorbing
  · exact quittingCyclicContinuationBlock_policy boundaryReward oddValue 1
      periodTwoBlock periodTwoBlock_isQuittingCyclicContinuationBlock
  · exact quittingCyclicContinuationBlock_prod_continueMass_lt_one
      boundaryReward oddValue 1 periodTwoBlock
        periodTwoBlock_isQuittingCyclicContinuationBlock

/-- The actual tail value of the repeated roots is the displayed next value
of the Nash--Bellman block. -/
theorem boundaryPeriodTwoRootSequenceTailVector_eq (time : ℕ) :
    quittingRootSequenceTailVector boundaryReward boundaryPeriodTwoRoots (time + 1) =
      boundaryPeriodTwoValue (finRotate 2 (quittingCyclicOrbit 0 time)) := by
  funext who
  change quittingRootSequenceTerminalValue boundaryReward
      (quittingCyclicRootSequence boundaryPeriodTwoCycle 0) who (time + 1) = _
  rw [quittingRootSequenceTerminalValue_cyclic_eq]
  rw [← boundaryPeriodTwoValue_eq_cyclicTerminalValue]
  rw [quittingCyclicOrbit_succ]

/-- Every repeated row is support-perfect at zero error against its actual
tail, not merely against a formal Bellman annotation. -/
theorem boundaryPeriodTwoRoots_supportExact :
    IsQuittingRootSequenceSupportApproxNash boundaryReward boundaryPeriodTwoRoots 0 := by
  intro time
  have hnash := quittingCyclicContinuationBlock_rootNash boundaryReward
    oddValue 1 periodTwoBlock periodTwoBlock_isQuittingCyclicContinuationBlock
    (quittingCyclicOrbit (0 : Fin 2) time)
  have hsupport := isQuittingRootSupportApproxNash_zero_of_isZeroNash
    boundaryReward _ _ hnash
  rw [boundaryPeriodTwoRootSequenceTailVector_eq]
  change IsQuittingRootSupportApproxNash boundaryReward
    (boundaryPeriodTwoValue (finRotate 2 (quittingCyclicOrbit 0 time))) 0
    (boundaryPeriodTwoCycle (quittingCyclicOrbit 0 time))
  exact hsupport

/-- The repeated roots absorb completely. -/
theorem boundaryPeriodTwoRoots_completelyAbsorbing :
    IsCompletelyAbsorbing boundaryPeriodTwoRoots := by
  apply isCompletelyAbsorbing_of_not_summable_totalAbsorptionCharge
  apply not_summable_quittingTotalAbsorptionCharge_cyclicRootSequence_of_pos
    boundaryPeriodTwoCycle (0 : Fin 2)
  rw [boundaryPeriodTwoCycle, quittingCyclicContinuationBlockCycle_periodTwoBlock]
  exact oddRoot_absorption_pos

/-- The hard four-player boundary table has a sequentially-perfect completely
absorbing root sequence at every positive tolerance. -/
theorem boundaryReward_sequentiallyPerfectAbsorbingExistence :
    QuittingSequentiallyεPerfectAbsorbingExistence boundaryReward := by
  intro ε hε
  refine ⟨boundaryPeriodTwoRoots, boundaryPeriodTwoRoots_completelyAbsorbing,
    fun time ↦ ?_⟩
  apply quittingRowεPerfect_of_supportApproxNash hε.le
  exact (boundaryPeriodTwoRoots_supportExact time).mono hε.le

/-- The same table does not have stationary approximate equilibria at every
positive tolerance. -/
theorem boundaryReward_not_stationaryEquilibriumExistence :
    ¬QuittingStationaryεEquilibriumExistence boundaryReward := by
  obtain ⟨ε₀, hε₀, hgap⟩ := no_stationary_terminalApproximateEquilibrium
  intro hstationary
  obtain ⟨root, hnash⟩ := hstationary (ε₀ / 2) (by linarith)
  exact hgap (ε₀ / 2) (by linarith) (by linarith) ⟨root, hnash⟩

/-- The table has approximate equilibria at every positive accuracy, witnessed
by one exact period-two profile. -/
theorem boundaryReward_approximateEquilibriumExistence :
    ∀ ε : ℝ, 0 < ε → ∃ profile : (quittingGame boundaryReward).BehaviorProfile,
      (quittingGame boundaryReward).IsεAsymptoticNash
        (quittingTerminalPayoff boundaryReward) ε profile := by
  intro ε hε
  exact ⟨periodTwoProfile, periodTwoProfile_isExactTerminalNash.mono hε.le⟩

/-- The table has approximate equilibria at every positive accuracy, has no
stationary approximate equilibria at every positive accuracy, and has a
sequentially-perfect completely absorbing root sequence at every positive
accuracy. -/
theorem boundaryReward_approximate_not_stationary_and_sequential :
    (∀ ε : ℝ, 0 < ε → ∃ profile : (quittingGame boundaryReward).BehaviorProfile,
      (quittingGame boundaryReward).IsεAsymptoticNash
        (quittingTerminalPayoff boundaryReward) ε profile) ∧
      ¬QuittingStationaryεEquilibriumExistence boundaryReward ∧
      QuittingSequentiallyεPerfectAbsorbingExistence boundaryReward :=
  ⟨boundaryReward_approximateEquilibriumExistence,
    boundaryReward_not_stationaryEquilibriumExistence,
    boundaryReward_sequentiallyPerfectAbsorbingExistence⟩

end SolanVieilleBoundary
end GameTheory
