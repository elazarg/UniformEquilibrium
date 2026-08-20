import Research.Quitting.BlockPair.K11.ConditionalProfile

noncomputable section

namespace GameTheory.BlockPairK11.ConditionalData

theorem profile_isExactTerminalNash
    (x : HazardIndex → ℝ)
    (hx : ∀ index, 0 < x index ∧ x index < 1)
    (hblock : IsQuittingCyclicContinuationBlock reward (phaseValue x 0) 11
      (block x hx))
    (hadmissible : IsQuittingCycleAdmissible reward (phaseRoot x hx)) :
    (quittingGame reward).IsεAsymptoticNash
      (quittingTerminalPayoff reward) 0 (profile x hx) := by
  have hcycle : quittingCyclicContinuationBlockCycle 10 (block x hx) =
      phaseRoot x hx := funext (blockCycle_eq_phaseRoot x hx)
  exact isZeroAsymptoticNash_quittingCyclicContinuationBlockProfile reward
    (phaseValue x 0) 10 (block x hx) hblock (hcycle.symm ▸ hadmissible) 0

theorem profile_terminalPayoff
    (x : HazardIndex → ℝ)
    (hx : ∀ index, 0 < x index ∧ x index < 1)
    (hblock : IsQuittingCyclicContinuationBlock reward (phaseValue x 0) 11
      (block x hx)) :
    quittingTerminalPayoff reward (profile x hx) = phaseValue x 0 :=
  quittingTerminalPayoff_quittingCyclicContinuationBlockProfile reward
    (phaseValue x 0) 10 (block x hx) hblock

end GameTheory.BlockPairK11.ConditionalData
