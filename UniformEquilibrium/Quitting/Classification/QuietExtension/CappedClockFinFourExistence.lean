import UniformEquilibrium.Quitting.Classification.QuietExtension.CappedClockFixedTargetQuietExtension
import UniformEquilibrium.Quitting.Classification.PlayerReindex

/-! # A raw four-player capped-clock existence consumer -/

noncomputable section

namespace GameTheory

open StochasticGame

/-- The four-player table reindexed so that `owner` is the distinguished
`none` player and every other player is a child. -/
def quittingFinFourOwnerOptionReward
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (owner : Fin 4) :
    {S : Finset (Option (QuittingDeletedPlayer owner)) // S.Nonempty} →
      Payoff (Option (QuittingDeletedPlayer owner)) :=
  quittingRewardReindex (Equiv.optionSubtypeNe owner).symm reward

/-- A four-player quitting game has a uniform-equilibrium payoff whenever
one displayed owner reindexing of its raw reward table has a capped-clock
parent certificate. No equilibrium or strategy is part of the criterion. -/
theorem quittingGame_exists_uniformEquilibriumPayoff_of_finFour_cappedClockCertificate
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (owner : Fin 4)
    (certificate : CappedClockParentRewardCertificate
      (quittingFinFourOwnerOptionReward reward owner)) :
    ∃ payoff : Payoff (Fin 4),
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff := by
  let reindex : Fin 4 ≃ Option (QuittingDeletedPlayer owner) :=
    (Equiv.optionSubtypeNe owner).symm
  let parentReward := quittingFinFourOwnerOptionReward reward owner
  let childReward := quittingDeleteReward parentReward (· = none)
  have hsurvivorCard : Fintype.card (QuittingDeletedPlayer owner) = 3 :=
    card_quittingDeletedPlayer_eq_three_of_card_eq_four owner rfl
  letI : Nonempty (QuittingDeletedPlayer owner) :=
    Fintype.card_pos_iff.mp (by rw [hsurvivorCard]; norm_num)
  have hparentCard : Fintype.card (Option (QuittingDeletedPlayer owner)) = 4 := by
    rw [Fintype.card_option, hsurvivorCard]
  have hchildCard :
      Fintype.card {who : Option (QuittingDeletedPlayer owner) // who ≠ none} = 3 :=
    card_quittingDeletedPlayer_eq_three_of_card_eq_four none hparentCard
  obtain ⟨childTarget, hchildTarget⟩ :=
    quittingGame_exists_uniformEquilibriumPayoff_of_card_eq_three
      hchildCard childReward
  obtain ⟨parentTarget, _, hparentTarget⟩ :=
    exists_uniformEquilibriumPayoff_eq_some_of_cappedClockCertificate
      parentReward certificate childTarget hchildTarget
  change ∃ payoff : Payoff (Fin 4),
    (quittingGame reward).IsUniformEquilibriumPayoff none payoff
  exact quittingGame_exists_uniformEquilibriumPayoff_of_reindex
    reindex reward ⟨parentTarget, hparentTarget⟩

end GameTheory
