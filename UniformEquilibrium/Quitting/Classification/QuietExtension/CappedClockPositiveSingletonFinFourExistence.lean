import UniformEquilibrium.Quitting.Classification.QuietExtension.CappedClockFinFourExistence
import UniformEquilibrium.Quitting.Classification.QuietExtension.CappedClockPositiveSingletonQuietExtension

/-! # Raw four-player existence from the positive-singleton relaxation -/

noncomputable section

namespace GameTheory

open StochasticGame

/-- A raw Fin4 reward table has a uniform-equilibrium payoff if one owner
reindexing satisfies F/J and one child has a positive own singleton. -/
theorem
    quittingGame_exists_uniformEquilibriumPayoff_of_finFour_cappedClockPositiveSingleton
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (owner : Fin 4)
    (certificate : CappedClockParentFutureJoinCertificate
      (quittingFinFourOwnerOptionReward reward owner))
    (pivot : QuittingDeletedPlayer owner)
    (hpivot : 0 < quittingFinFourOwnerOptionReward reward owner
      ⟨{some pivot}, Finset.singleton_nonempty (some pivot)⟩ (some pivot)) :
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
    exists_uniformEquilibriumPayoff_eq_some_of_cappedClockPositiveSingleton
      parentReward certificate pivot hpivot childTarget hchildTarget
  change ∃ payoff : Payoff (Fin 4),
    (quittingGame reward).IsUniformEquilibriumPayoff none payoff
  exact quittingGame_exists_uniformEquilibriumPayoff_of_reindex
    reindex reward ⟨parentTarget, hparentTarget⟩

end GameTheory
