import Research.Quitting.BlockPair.K11.ConditionalBlock

noncomputable section

namespace GameTheory.BlockPairK11.ConditionalData

@[simp] theorem blockCycle_eq_phaseRoot
    (x : HazardIndex → ℝ)
    (hx : ∀ index, 0 < x index ∧ x index < 1)
    (stage : Fin 11) :
    quittingCyclicContinuationBlockCycle 10 (block x hx) stage =
      phaseRoot x hx stage := by
  change quittingRootOfSimplex
    (phasePoint x hx (pathPhase (Fin.castSucc stage))).2 = _
  rw [rootOfSimplex_phasePoint, pathPhase_castSucc]

def profile (x : HazardIndex → ℝ)
    (hx : ∀ index, 0 < x index ∧ x index < 1) :
    (quittingGame reward).BehaviorProfile :=
  quittingCyclicContinuationBlockProfile reward 10 (block x hx) 0

end GameTheory.BlockPairK11.ConditionalData
