/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticPositiveSlopeCausalRegression
import UniformEquilibrium.Quitting.Cycles.BlockSurvival
import UniformEquilibrium.Quitting.Debt.Dynamic.ExactChronologicalData
import UniformEquilibrium.Quitting.Terminal.TailCompression.ElementaryTailSemanticReduction

/-!
# A source-matched reset need not create deleted-player exposure

The literal `Never` reset endpoint in the positive-slope regression strictly
decreases the mover's semantic debt while its repeated endpoint has zero
opponent clock charge.  Thus a debt-decreasing reset alone cannot provide the
opponent-survival hypothesis required by a chronological shadowing argument.
The same example also records that exact reached-tail data has zero local
forcing but retains the source's initial debt; it is not a small-debt producer.
-/

noncomputable section

namespace GameTheory

open Filter Math.Probability
open scoped Topology

namespace PositiveSlopeCausalRegression

open QuittingSureSetOwnerRepair

/-- Repeating the literal `Never` reset endpoint exposes no opponent of the
observer at any stage. -/
theorem endpoint_opponentClockCharge_observer_zero (time : ℕ) :
    quittingOpponentClockCharge
        (quittingProfileLiveRoot PositiveSlopeCausalRegression.reward endpoint)
        observer time = 0 := by
  have hroot :
      quittingProfileLiveRoot PositiveSlopeCausalRegression.reward endpoint =
        fun _ _ ↦ PMF.pure false := by
    simp [endpoint, quittingPureSetRoot_empty]
  rw [hroot]
  simp [quittingOpponentClockCharge, quittingRootOpponentAbsorptionMass,
    quittingRootAbsorptionMass, quittingStationaryContinueMass,
    quittingAllContinueAction]

/-- Accordingly every finite deleted-player survival product at the reset
endpoint is exactly one. -/
theorem endpoint_opponentSurvivalWeight_observer_one
    (start fuel : ℕ) :
    quittingOpponentSurvivalWeight
        (quittingProfileLiveRoot PositiveSlopeCausalRegression.reward endpoint)
        observer start fuel = 1 := by
  unfold quittingOpponentSurvivalWeight
  apply Finset.prod_eq_one
  intro offset _
  have hzero := endpoint_opponentClockCharge_observer_zero (start + offset)
  rw [quittingOpponentClockCharge_eq_one_sub] at hzero
  linarith

/-- A literal whole-stopping-law reset can strictly decrease the mover's debt
while its repeated endpoint has no opponent exposure and hence no vanishing
deleted-player survival. -/
theorem debt_decreasing_reset_does_not_force_opponentExposure :
    quittingTerminalSemanticDebt
          (quittingTerminalSemanticPair
            PositiveSlopeCausalRegression.reward endpoint) mover <
        quittingTerminalSemanticDebt
          (quittingTerminalSemanticPair
            PositiveSlopeCausalRegression.reward source) mover ∧
      (∀ time,
        quittingOpponentClockCharge
          (quittingProfileLiveRoot PositiveSlopeCausalRegression.reward endpoint)
          observer time = 0) ∧
      (∀ start fuel,
        quittingOpponentSurvivalWeight
          (quittingProfileLiveRoot PositiveSlopeCausalRegression.reward endpoint)
          observer start fuel = 1) := by
  refine ⟨?_, endpoint_opponentClockCharge_observer_zero,
    endpoint_opponentSurvivalWeight_observer_one⟩
  rw [endpoint_debt_mover, source_debt_mover]
  norm_num

/-- Reading a profile through its unique live-root sequence preserves its
complete terminal semantic pair. -/
theorem terminalSemanticPair_rootSequence_profileLiveRoot
    (profile : (quittingGame
      PositiveSlopeCausalRegression.reward).BehaviorProfile) :
    quittingTerminalSemanticPair PositiveSlopeCausalRegression.reward
        (quittingRootSequenceProfile PositiveSlopeCausalRegression.reward
          (quittingProfileLiveRoot PositiveSlopeCausalRegression.reward profile)
          0) =
      quittingTerminalSemanticPair PositiveSlopeCausalRegression.reward
        profile := by
  apply Prod.ext
  · funext who
    exact (quittingTerminalPayoff_eq_rootSequence_profileLiveRoot
      PositiveSlopeCausalRegression.reward profile who).symm
  · funext who
    change quittingContinuationBestResponseValue
        PositiveSlopeCausalRegression.reward
          (quittingRootSequenceProfile PositiveSlopeCausalRegression.reward
            (quittingProfileLiveRoot PositiveSlopeCausalRegression.reward
              profile) 0) who =
      quittingContinuationBestResponseValue
        PositiveSlopeCausalRegression.reward profile who
    simpa [quittingRootSequenceBestResponseValue] using
      (quittingContinuationBestResponseValue_eq_rootSequence_profileLiveRoot
        PositiveSlopeCausalRegression.reward profile who).symm

/-- Exact reached-tail data has zero local forcing but retains the source's
initial debt, so it is not by itself a small-debt chronological producer. -/
theorem exact_source_has_zero_forcing_but_unit_initialDebt :
    let roots := quittingProfileLiveRoot PositiveSlopeCausalRegression.reward
      source
    let data := QuittingChronologicalDebtData.exactOfRoots
      PositiveSlopeCausalRegression.reward roots
    data.debt 0 mover = 1 ∧
      (∀ time, data.prescribedDefect
        PositiveSlopeCausalRegression.reward time = 0) ∧
      (∀ time, data.directDebtDefect
        PositiveSlopeCausalRegression.reward time = 0) := by
  dsimp only
  constructor
  · rw [QuittingChronologicalDebtData.exactOfRoots_debt,
      QuittingChronologicalDebtData.exactOfRoots_semanticPair,
      terminalSemanticPair_rootSequence_profileLiveRoot, source_debt_mover]
  · exact ⟨QuittingChronologicalDebtData.exactOfRoots_prescribedDefect
      PositiveSlopeCausalRegression.reward _,
      QuittingChronologicalDebtData.exactOfRoots_directDebtDefect
        PositiveSlopeCausalRegression.reward _⟩

end PositiveSlopeCausalRegression

end GameTheory
