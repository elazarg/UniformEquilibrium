import Research.Quitting.BlockPair.K11.ConditionalData

namespace GameTheory.BlockPairK11.ConditionalData

theorem phaseAdd_nextPhase (phase : Phase) (offset : ℕ) :
    phaseAdd (nextPhase phase) offset = phaseAdd phase (offset + 1) := by
  apply Fin.ext
  simp [phaseAdd, nextPhase, Fin.ofNat, Nat.add_mod]
  omega

theorem phaseAdd_nextPhase_ten (phase : Phase) :
    phaseAdd (nextPhase phase) 10 = phase := by
  apply Fin.ext
  simp [phaseAdd, nextPhase, Fin.ofNat, Nat.add_mod]
  omega

theorem phaseAdd_eleven (phase : Phase) :
    phaseAdd phase 11 = phase := by
  apply Fin.ext
  simp [phaseAdd, Fin.ofNat]

end GameTheory.BlockPairK11.ConditionalData
