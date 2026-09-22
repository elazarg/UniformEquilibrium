import UniformEquilibrium.Quitting.Classification.QuietExtension.CappedClockFinFourExistence
import UniformEquilibrium.Quitting.Classification.QuietExtension.CappedClockPositiveSingletonQuietExtension
import UniformEquilibrium.Quitting.Examples.AdaptiveChildCenter

/-!
# Capped-clock noncoverage at the adaptive-child center

Every player deletion of the existing `AdaptiveChildCenter.reward` fails even
the relaxed capped-clock system containing only future and joining rows.  The
center's checked Nash and uniform-payoff results are not reproved here.
-/

noncomputable section

namespace GameTheory
namespace AdaptiveChildCenterCappedClockObstruction

abbrev Player := Fin 4

private theorem mapped_childCoalition (owner : Player)
    (coalition : Finset (QuittingDeletedPlayer owner)) :
    (cappedClockChildCoalition coalition).map
        (Equiv.optionSubtypeNe owner).toEmbedding =
      coalition.map (Function.Embedding.subtype _) := by
  change (coalition.map ⟨some, Option.some_injective _⟩).map
      (Equiv.optionSubtypeNe owner).toEmbedding = _
  rw [Finset.map_map]
  rfl

private theorem mapped_joinedCoalition (owner : Player)
    (coalition : Finset (QuittingDeletedPlayer owner)) :
    (cappedClockJoinedCoalition coalition).map
        (Equiv.optionSubtypeNe owner).toEmbedding =
      insert owner (coalition.map (Function.Embedding.subtype _)) := by
  rw [cappedClockJoinedCoalition, Finset.map_insert,
    mapped_childCoalition owner coalition]
  rfl

private theorem mapped_univ_eq_erase (owner : Player) :
    (Finset.univ : Finset (QuittingDeletedPlayer owner)).map
        (Function.Embedding.subtype _) = Finset.univ.erase owner := by
  ext player
  simp [and_comm]

@[simp] private theorem optionReward_singleton (owner : Player)
    (who quitter : Option (QuittingDeletedPlayer owner)) :
    quittingFinFourOwnerOptionReward AdaptiveChildCenter.reward owner
        (quittingSingletonTerminal quitter) who =
      AdaptiveChildCenter.reward
        (quittingSingletonTerminal (Equiv.optionSubtypeNe owner quitter))
        (Equiv.optionSubtypeNe owner who) := by
  change AdaptiveChildCenter.reward
      ((quittingCoalitionEquiv (Equiv.optionSubtypeNe owner).symm).symm
        (quittingSingletonTerminal quitter))
      (Equiv.optionSubtypeNe owner who) = _
  congr 1

@[simp] private theorem optionReward_childCoalition (owner : Player)
    (coalition : Finset (QuittingDeletedPlayer owner)) (hne : coalition.Nonempty)
    (who : Option (QuittingDeletedPlayer owner)) :
    quittingFinFourOwnerOptionReward AdaptiveChildCenter.reward owner
        ⟨cappedClockChildCoalition coalition,
          cappedClockChildCoalition_nonempty hne⟩ who =
      AdaptiveChildCenter.reward
        ⟨coalition.map (Function.Embedding.subtype _),
          Finset.map_nonempty.mpr hne⟩
        (Equiv.optionSubtypeNe owner who) := by
  change AdaptiveChildCenter.reward
      ((quittingCoalitionEquiv (Equiv.optionSubtypeNe owner).symm).symm
        ⟨cappedClockChildCoalition coalition,
          cappedClockChildCoalition_nonempty hne⟩)
      (Equiv.optionSubtypeNe owner who) = _
  congr 1
  exact Subtype.ext (mapped_childCoalition owner coalition)

@[simp] private theorem optionReward_joinedCoalition (owner : Player)
    (coalition : Finset (QuittingDeletedPlayer owner))
    (who : Option (QuittingDeletedPlayer owner)) :
    quittingFinFourOwnerOptionReward AdaptiveChildCenter.reward owner
        ⟨cappedClockJoinedCoalition coalition,
          cappedClockJoinedCoalition_nonempty coalition⟩ who =
      AdaptiveChildCenter.reward
        ⟨insert owner (coalition.map (Function.Embedding.subtype _)),
          Finset.insert_nonempty owner _⟩
        (Equiv.optionSubtypeNe owner who) := by
  change AdaptiveChildCenter.reward
      ((quittingCoalitionEquiv (Equiv.optionSubtypeNe owner).symm).symm
        ⟨cappedClockJoinedCoalition coalition,
          cappedClockJoinedCoalition_nonempty coalition⟩)
      (Equiv.optionSubtypeNe owner who) = _
  congr 1
  exact Subtype.ext (mapped_joinedCoalition owner coalition)

private theorem not_futureJoin_zero :
    ¬Nonempty (CappedClockParentFutureJoinCertificate
      (quittingFinFourOwnerOptionReward AdaptiveChildCenter.reward 0)) := by
  rintro ⟨certificate⟩
  let anchor : QuittingDeletedPlayer (0 : Player) := ⟨3, by decide⟩
  let coalition : Finset (QuittingDeletedPlayer (0 : Player)) := {anchor}
  have hrow := certificate.future_row coalition (by simp [coalition])
  have hdelta : ∀ who : QuittingDeletedPlayer (0 : Player),
      quittingFinFourOwnerOptionReward AdaptiveChildCenter.reward 0
          (quittingSingletonTerminal (some who)) (some who) -
        quittingFinFourOwnerOptionReward AdaptiveChildCenter.reward 0
          ⟨cappedClockChildCoalition coalition,
            cappedClockChildCoalition_nonempty (by simp [coalition])⟩ (some who) ≤ 0 := by
    intro who
    rw [optionReward_singleton,
      optionReward_childCoalition (hne := by simp [coalition])]
    rcases who with ⟨who, hwho⟩
    fin_cases who
    · exact (hwho rfl).elim
    all_goals
      simp_all [coalition, anchor, AdaptiveChildCenter.reward,
        quittingSingletonTerminal]
  have hsum : (∑ who, certificate.weight who *
      (quittingFinFourOwnerOptionReward AdaptiveChildCenter.reward 0
          (quittingSingletonTerminal (some who)) (some who) -
        quittingFinFourOwnerOptionReward AdaptiveChildCenter.reward 0
          ⟨cappedClockChildCoalition coalition,
            cappedClockChildCoalition_nonempty (by simp [coalition])⟩ (some who))) ≤ 0 := by
    exact Finset.sum_nonpos fun who _ =>
      mul_nonpos_of_nonneg_of_nonpos (certificate.weight_nonneg who) (hdelta who)
  have hbase : 0 <
      quittingFinFourOwnerOptionReward AdaptiveChildCenter.reward 0
          (quittingSingletonTerminal none) none -
        quittingFinFourOwnerOptionReward AdaptiveChildCenter.reward 0
          ⟨cappedClockChildCoalition coalition,
            cappedClockChildCoalition_nonempty (by simp [coalition])⟩ none := by
    rw [optionReward_singleton,
      optionReward_childCoalition (hne := by simp [coalition])]
    norm_num [coalition, anchor, AdaptiveChildCenter.reward,
      quittingSingletonTerminal]
  exact hbase.not_ge (hrow.trans hsum)

private theorem not_futureJoin_of_nonzero (owner : Player) (howner : owner ≠ 0) :
    ¬Nonempty (CappedClockParentFutureJoinCertificate
      (quittingFinFourOwnerOptionReward AdaptiveChildCenter.reward owner)) := by
  rintro ⟨certificate⟩
  let : Nonempty (QuittingDeletedPlayer owner) := ⟨⟨0, Ne.symm howner⟩⟩
  let coalition : Finset (QuittingDeletedPlayer owner) := Finset.univ
  have hrow := certificate.join_row coalition (Finset.univ_nonempty)
  have hdelta : ∀ who : QuittingDeletedPlayer owner,
      quittingFinFourOwnerOptionReward AdaptiveChildCenter.reward owner
          ⟨cappedClockChildCoalition (insert who coalition),
            cappedClockChildCoalition_nonempty (Finset.insert_nonempty who coalition)⟩
          (some who) -
        quittingFinFourOwnerOptionReward AdaptiveChildCenter.reward owner
          ⟨cappedClockChildCoalition coalition,
            cappedClockChildCoalition_nonempty Finset.univ_nonempty⟩ (some who) = 0 := by
    intro who
    simp [coalition]
  have hsum : (∑ who, certificate.weight who *
      (quittingFinFourOwnerOptionReward AdaptiveChildCenter.reward owner
          ⟨cappedClockChildCoalition (insert who coalition),
            cappedClockChildCoalition_nonempty (Finset.insert_nonempty who coalition)⟩
          (some who) -
        quittingFinFourOwnerOptionReward AdaptiveChildCenter.reward owner
          ⟨cappedClockChildCoalition coalition,
            cappedClockChildCoalition_nonempty Finset.univ_nonempty⟩ (some who))) = 0 := by
    apply Finset.sum_eq_zero
    intro who _
    rw [hdelta who, mul_zero]
  have hbase : 0 <
      quittingFinFourOwnerOptionReward AdaptiveChildCenter.reward owner
          ⟨cappedClockJoinedCoalition coalition,
            cappedClockJoinedCoalition_nonempty coalition⟩ none -
        quittingFinFourOwnerOptionReward AdaptiveChildCenter.reward owner
          ⟨cappedClockChildCoalition coalition,
            cappedClockChildCoalition_nonempty Finset.univ_nonempty⟩ none := by
    rw [optionReward_joinedCoalition,
      optionReward_childCoalition (hne := Finset.univ_nonempty)]
    fin_cases owner
    · exact (howner rfl).elim
    all_goals
      simp_all [coalition, mapped_univ_eq_erase, AdaptiveChildCenter.reward]
  exact hbase.not_ge (hrow.trans (le_of_eq hsum))

/-- Every deletion fails the future/join capped-clock system, even after its
Never row is removed. -/
theorem not_nonempty_cappedClockParentFutureJoinCertificate (owner : Player) :
    ¬Nonempty (CappedClockParentFutureJoinCertificate
      (quittingFinFourOwnerOptionReward AdaptiveChildCenter.reward owner)) := by
  by_cases howner : owner = 0
  · subst owner
    exact not_futureJoin_zero
  · exact not_futureJoin_of_nonzero owner howner

/-- Consequently every deletion also fails the raw N/F/J capped-clock LP. -/
theorem not_nonempty_cappedClockParentRewardCertificate (owner : Player) :
    ¬Nonempty (CappedClockParentRewardCertificate
      (quittingFinFourOwnerOptionReward AdaptiveChildCenter.reward owner)) := by
  rintro ⟨certificate⟩
  apply not_nonempty_cappedClockParentFutureJoinCertificate owner
  exact ⟨{
    weight := certificate.weight
    weight_nonneg := certificate.weight_nonneg
    future_row := certificate.future_row
    join_row := certificate.join_row
  }⟩

end AdaptiveChildCenterCappedClockObstruction
end GameTheory
