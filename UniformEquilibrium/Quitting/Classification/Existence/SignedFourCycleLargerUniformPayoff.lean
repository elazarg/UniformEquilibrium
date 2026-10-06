import UniformEquilibrium.Quitting.Cycles.SignedFourCycleLargerCertificate
import UniformEquilibrium.Quitting.Cycles.SignedFourCycleLargerSourceBridge
import UniformEquilibrium.Quitting.Classification.PlayerReindex

noncomputable section

namespace GameTheory

/-- An open raw reward-table class; all source data are reconstructed internally. -/
theorem exists_uniformEquilibriumPayoff_of_largerSignedFourCycleSingletonTable
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (htable : HasLargerSignedFourCycleSingletonTable reward) :
    ∃ target, (quittingGame reward).IsUniformEquilibriumPayoff none target := by
  let data := SignedFourCycleSingletonData.ofSingletonMatrixLargerTests htable
  let tests := SignedFourCycleSingletonData.ofSingletonMatrixLargerTests_largerTests htable
  exact ⟨data.largerTargetValue tests, data.largerTargetValue_isUniformEquilibriumPayoff tests⟩

def HasReindexedLargerSignedFourCycleSingletonTable {ι : Type} [Fintype ι] [DecidableEq ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) : Prop :=
  ∃ order : ι ≃ Fin 4,
    HasLargerSignedFourCycleSingletonTable (quittingRewardReindex order reward)

theorem isOpen_hasReindexedLargerSignedFourCycleSingletonTable
    {ι : Type} [Fintype ι] [DecidableEq ι] :
    IsOpen {reward : {S : Finset ι // S.Nonempty} → Payoff ι |
      HasReindexedLargerSignedFourCycleSingletonTable reward} := by
  have heq : {reward : {S : Finset ι // S.Nonempty} → Payoff ι |
      HasReindexedLargerSignedFourCycleSingletonTable reward} =
      ⋃ order : ι ≃ Fin 4, {reward |
        HasLargerSignedFourCycleSingletonTable (quittingRewardReindex order reward)} := by
    ext reward
    simp [HasReindexedLargerSignedFourCycleSingletonTable]
  rw [heq]
  apply isOpen_iUnion
  intro order
  apply isOpen_hasLargerSignedFourCycleSingletonTable.preimage
  unfold quittingRewardReindex
  fun_prop

theorem exists_uniformEquilibriumPayoff_of_reindexedLargerSignedFourCycleSingletonTable
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (htable : HasReindexedLargerSignedFourCycleSingletonTable reward) :
    ∃ target, (quittingGame reward).IsUniformEquilibriumPayoff none target := by
  obtain ⟨order, horder⟩ := htable
  exact quittingGame_exists_uniformEquilibriumPayoff_of_reindex order reward
    (exists_uniformEquilibriumPayoff_of_largerSignedFourCycleSingletonTable _ horder)

/-- Literal signed singleton rows and the larger-branch tests produce one fixed target. -/
theorem exists_uniformEquilibriumPayoff_of_signedFourCycle_larger
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    (data : SignedFourCycleSingletonData reward) (tests : data.LargerTests) :
    ∃ target, (quittingGame reward).IsUniformEquilibriumPayoff none target :=
  ⟨data.largerTargetValue tests, data.largerTargetValue_isUniformEquilibriumPayoff tests⟩

/-- Player relabeling returns the constructed payoff to the original game. -/
theorem exists_uniformEquilibriumPayoff_of_reindexed_signedFourCycle_larger
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (order : ι ≃ Fin 4)
    (data : SignedFourCycleSingletonData (quittingRewardReindex order reward))
    (tests : data.LargerTests) :
    ∃ target, (quittingGame reward).IsUniformEquilibriumPayoff none target :=
  quittingGame_exists_uniformEquilibriumPayoff_of_reindex order reward
    (exists_uniformEquilibriumPayoff_of_signedFourCycle_larger data tests)

end GameTheory
