import UniformEquilibrium.Quitting.Stationary.FiniteCensorCutoff
import UniformEquilibrium.Quitting.Examples.GuardedCrossedResponseExactRoots

/-! # Exact one-date censor of the literal unit-ceiling crossed-response root -/

noncomputable section

namespace GameTheory.GuardedCrossedResponseExamples

open _root_.Math.Probability

theorem unitCeilingRoot_deletedSurvivalMax :
    quittingStationaryDeletedSurvivalMax unitCeilingRoot = 0 := by
  apply le_antisymm
  · unfold quittingStationaryDeletedSurvivalMax
    apply (Finset.sup'_le_iff Finset.univ_nonempty _).mpr
    intro player _
    cases player with
    | none => exact le_rfl
    | some who =>
        change quittingStationaryFixedOpponentsContinueMass unitCeilingRoot who ≤ 0
        rw [unitCeilingRoot_deletedSurvival]
  · exact quittingStationaryDeletedSurvivalMax_nonneg unitCeilingRoot

/-- The literal unit-ceiling root needs just date zero or Never. The same
independent finite laws preserve its exact terminal payoff and full behavioral cap.
No equilibrium, root, or cap is supplied by the caller. -/
theorem exists_unitCeiling_oneDateFiniteCensor_exact :
    ∃ mixed : Fin 4 → PMF (QuittingFiniteDeadlineTimingAction 1),
      (∀ who, (quittingFiniteDeadlineTimingLaw (mixed who)).toPMF =
        censorLateFiniteStoppingLaw
          (quittingBehaviorStoppingLaw unitCeilingReward
            (quittingStationaryProfile unitCeilingReward unitCeilingRoot who)) 0) ∧
      quittingTerminalSemanticPair unitCeilingReward
          (quittingFiniteDeadlineTimingProfile unitCeilingReward 1 mixed) =
        quittingTerminalSemanticPair unitCeilingReward
          (quittingStationaryFiniteCensorProfile unitCeilingReward unitCeilingRoot 1) ∧
      (∀ who, quittingTerminalPayoff unitCeilingReward
          (quittingFiniteDeadlineTimingProfile unitCeilingReward 1 mixed) who =
        unitCeilingValue who) ∧
      (∀ who, quittingContinuationBestResponseValue unitCeilingReward
          (quittingFiniteDeadlineTimingProfile unitCeilingReward 1 mixed) who =
        unitCeilingValue who) ∧
      (quittingGame unitCeilingReward).IsεAsymptoticNash
        (quittingTerminalPayoff unitCeilingReward) 0
        (quittingFiniteDeadlineTimingProfile unitCeilingReward 1 mixed) := by
  simpa only [unitCeilingRoot_terminalPayoff] using
    exists_stationaryFiniteCensor_oneDate_exact unitCeilingReward unitCeilingRoot
      (abs_reward_le_quittingRewardBound unitCeilingReward) unitCeilingRoot_terminalNash
      unitCeilingRoot_deletedSurvivalMax

end GameTheory.GuardedCrossedResponseExamples

