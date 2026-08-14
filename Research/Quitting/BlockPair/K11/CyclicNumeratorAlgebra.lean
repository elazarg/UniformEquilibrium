import Research.Quitting.BlockPair.K11.NumeratorAlgebra
import Research.Quitting.BlockPair.K11.PhaseArithmetic

noncomputable section

namespace GameTheory.BlockPairK11.ConditionalData

/-- Eleven-step scalar fold beginning at a named phase. -/
def scalarCycleNumerator (immediate survival : Phase → ℝ)
    (phase : Phase) : ℝ × ℝ :=
  scalarNumeratorAux (fun offset ↦ immediate (phaseAdd phase offset))
    (fun offset ↦ survival (phaseAdd phase offset)) 11

/-- Rotation identity for the named eleven-step numerator fold.  Its proof
uses only the first/last recurrence nodes; it does not expand eleven terms. -/
theorem scalarCycleNumerator_recurrence
    (immediate survival : Phase → ℝ) (phase : Phase) :
    (scalarCycleNumerator immediate survival phase).1 =
      (1 - (scalarCycleNumerator immediate survival phase).2) *
          immediate phase +
        survival phase *
          (scalarCycleNumerator immediate survival (nextPhase phase)).1 := by
  let tail := scalarNumeratorAux
    (fun offset ↦ immediate (phaseAdd phase (offset + 1)))
    (fun offset ↦ survival (phaseAdd phase (offset + 1))) 10
  have hphase := scalarNumeratorAux_prepend
    (fun offset ↦ immediate (phaseAdd phase offset))
    (fun offset ↦ survival (phaseAdd phase offset)) 10
  have hnext := scalarNumeratorAux_append
    (fun offset ↦ immediate (phaseAdd (nextPhase phase) offset))
    (fun offset ↦ survival (phaseAdd (nextPhase phase) offset)) 10
  have htailNext :
      scalarNumeratorAux
          (fun offset ↦ immediate (phaseAdd (nextPhase phase) offset))
          (fun offset ↦ survival (phaseAdd (nextPhase phase) offset)) 10 =
        tail := by
    apply congrArg₂ (fun first second ↦
      scalarNumeratorAux first second 10)
    · funext offset
      rw [phaseAdd_nextPhase]
    · funext offset
      rw [phaseAdd_nextPhase]
  simp only [scalarCycleNumerator]
  rw [hphase]
  change
    immediate (phaseAdd phase 0) + survival (phaseAdd phase 0) * tail.1 =
      (1 - survival (phaseAdd phase 0) * tail.2) * immediate phase +
        survival phase *
          (scalarNumeratorAux
            (fun offset ↦ immediate (phaseAdd (nextPhase phase) offset))
            (fun offset ↦ survival (phaseAdd (nextPhase phase) offset))
            11).1
  rw [hnext, htailNext]
  simp only [phaseAdd_nextPhase_ten]
  have hzero : phaseAdd phase 0 = phase := by
    apply Fin.ext
    simp [phaseAdd, Fin.ofNat]
  rw [hzero]
  ring

end GameTheory.BlockPairK11.ConditionalData
