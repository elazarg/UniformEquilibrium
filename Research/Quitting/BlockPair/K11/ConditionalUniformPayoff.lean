import Research.Quitting.BlockPair.K11.ConditionalExactNash
import UniformEquilibrium.Quitting.Punishment.OwnerSoloCertification

noncomputable section

namespace GameTheory.BlockPairK11.ConditionalData

theorem isUniformEquilibriumPayoff_phaseZero
    (x : HazardIndex → ℝ)
    (hx : ∀ index, 0 < x index ∧ x index < 1)
    (hblock : IsQuittingCyclicContinuationBlock reward (phaseValue x 0) 11
      (block x hx))
    (hadmissible : IsQuittingCycleAdmissible reward (phaseRoot x hx)) :
    (quittingGame reward).IsUniformEquilibriumPayoff none (phaseValue x 0) := by
  have hnash := profile_isExactTerminalNash x hx hblock hadmissible
  have huniform := quittingGame_isUniformEquilibriumPayoff_of_terminalNash_exact
    reward (profile x hx) hnash
  exact (profile_terminalPayoff x hx hblock) ▸ huniform

end GameTheory.BlockPairK11.ConditionalData
