import UniformEquilibrium.Quitting.Cycles.SignedFourCycleLargerCertificate
import UniformEquilibrium.Quitting.Classification.PlayerReindex

noncomputable section

namespace GameTheory

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
