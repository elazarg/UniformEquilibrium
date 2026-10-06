import UniformEquilibrium.Quitting.Classification.BadRootPremiumSupport
import UniformEquilibrium.Quitting.Root.PureSetNashSureExit

/-! # The actual sure-hazard cascade in a joining-attractive premium core

Strict raw insertion comparisons on nonempty core coalitions force every
core player to quit surely once one core opponent does. The entire literal
root is then the pure greatest-core root, giving the canonical sure-exit
payoff. Without this exit, bad roots are proper on their actual support.
The mixed-sign equality stratum is not covered by this predicate.
-/

noncomputable section

namespace GameTheory

open Set QuittingSureSetOwnerRepair

variable {ι : Type} [Fintype ι] [DecidableEq ι]

def HasStrictJoiningAttractivePremiumCore
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) : Prop :=
  ∀ player ∈ quittingPremiumCore reward,
    ∀ (coalition : Finset ι) (hnonempty : coalition.Nonempty),
      coalition ⊆ (quittingPremiumCore reward).erase player →
        reward ⟨coalition, hnonempty⟩ player <
          reward ⟨insert player coalition, Finset.insert_nonempty _ _⟩ player

private theorem mem_opponentCoalition_of_mass_pos_of_sure
    (root : ι → PMF Bool) (player other : ι) (hne : other ≠ player)
    (hsure : (root other true).toReal = 1) (coalition : Finset ι)
    (hmass : 0 < quittingOpponentCoalitionMass root player coalition) : other ∈ coalition := by
  by_contra hnot
  have hfalse : (root other false).toReal = 0 := by
    have hsum := quittingRoot_continueProbability_add_quitProbability root other
    linarith
  have hmember : other ∈ Finset.univ.erase player \ coalition := by simp [hne, hnot]
  have hproduct : (∏ who ∈ Finset.univ.erase player \ coalition,
      (root who false).toReal) = 0 := Finset.prod_eq_zero hmember hfalse
  unfold quittingOpponentCoalitionMass at hmass
  rw [hproduct, mul_zero] at hmass
  exact lt_irrefl _ hmass

theorem quittingRootEndpointDifference_pos_of_joiningAttractive_sureOpponent
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (tail : Payoff ι)
    (hjoining : HasStrictJoiningAttractivePremiumCore reward)
    (root : ι → PMF Bool)
    (hsupport : quittingPositiveHazardSupport root ⊆ quittingPremiumCore reward)
    (player : ι) (hplayer : player ∈ quittingPremiumCore reward)
    (other : ι) (hne : other ≠ player) (hsure : (root other true).toReal = 1) :
    0 < quittingRootEndpointDifference reward tail root player := by
  have htoggle : ∀ coalition ∈ (Finset.univ.erase player).powerset,
      0 < quittingOpponentCoalitionMass root player coalition →
        0 < quittingEndpointInsertionToggle reward tail player coalition := by
    intro coalition hcoalition hmass
    have hother := mem_opponentCoalition_of_mass_pos_of_sure root player other hne
      hsure coalition hmass
    have hnonempty : coalition.Nonempty := ⟨other, hother⟩
    have hsubset := quittingOpponentCoalition_subset_positiveHazardSupport_of_mass_pos
      root player coalition hmass
    have hsubsetCore : coalition ⊆ (quittingPremiumCore reward).erase player := by
      intro member hmember
      exact Finset.mem_erase.mpr
        ⟨Finset.ne_of_mem_erase (Finset.mem_powerset.mp hcoalition hmember),
          hsupport (hsubset hmember)⟩
    rw [quittingEndpointInsertionToggle_of_nonempty reward tail player coalition hnonempty]
    exact sub_pos.mpr (hjoining player hplayer coalition hnonempty hsubsetCore)
  obtain ⟨witness, hwitness, _hnonempty, hwitnessPositive⟩ :=
    exists_nonempty_opponentCoalition_of_positive_hazard root player other hne
      (by rw [hsure]; norm_num)
  rw [quittingRootEndpointDifference_eq_sum_opponentCoalitionToggle]
  apply Finset.sum_pos'
  · intro coalition hcoalition
    by_cases hzero : quittingOpponentCoalitionMass root player coalition = 0
    · simp [hzero]
    · have hpositive : 0 < quittingOpponentCoalitionMass root player coalition :=
        lt_of_le_of_ne (quittingOpponentCoalitionMass_nonneg root player coalition)
          (Ne.symm hzero)
      exact (mul_pos hpositive (htoggle coalition hcoalition hpositive)).le
  · exact ⟨witness, hwitness, mul_pos hwitnessPositive
      (htoggle witness hwitness hwitnessPositive)⟩

theorem exactRoot_eq_pureCore_of_joiningAttractive_sureHazard
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (tail : Payoff ι)
    (hjoining : HasStrictJoiningAttractivePremiumCore reward)
    (root : ι → PMF Bool) (hnash : IsεQuittingRootNash reward tail 0 root)
    (hsupport : quittingPositiveHazardSupport root ⊆ quittingPremiumCore reward)
    (other : ι) (hsure : (root other true).toReal = 1) :
    root = quittingPureSetRoot (quittingPremiumCore reward) := by
  have hendpoint :=
    (isZeroQuittingRootEndpointNash_iff_isZeroQuittingRootNash reward tail root).mpr hnash
  have hallSure : ∀ player ∈ quittingPremiumCore reward, (root player true).toReal = 1 := by
    intro player hplayer
    by_cases heq : player = other
    · simpa only [heq] using hsure
    · have hgap := quittingRootEndpointDifference_pos_of_joiningAttractive_sureOpponent
        reward tail hjoining root hsupport player hplayer other (Ne.symm heq) hsure
      have hnonpos := (hendpoint player).1
      have hsum := quittingRoot_continueProbability_add_quitProbability root player
      have hfalseNonneg : 0 ≤ (root player false).toReal := ENNReal.toReal_nonneg
      have htrueLe : (root player true).toReal ≤ 1 := hazardOfRoot_le_one root player
      nlinarith
  funext player
  by_cases hplayer : player ∈ quittingPremiumCore reward
  · have hpure := Math.PMFProduct.eq_pure_true_of_true_toReal_eq_one (root player)
      (hallSure player hplayer)
    simp [quittingPureSetRoot, quittingSetAction, hplayer, hpure]
  · have hpure := quittingRoot_eq_pure_false_of_not_mem_positiveHazardSupport root
      (fun hmem => hplayer (hsupport hmem))
    simp [quittingPureSetRoot, quittingSetAction, hplayer, hpure]

theorem isUniformEquilibriumPayoff_coreReward_of_joiningAttractive_bad_sureRoot
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (tail : Payoff ι)
    (hjoining : HasStrictJoiningAttractivePremiumCore reward)
    (root : ι → PMF Bool) (hnash : IsεQuittingRootNash reward tail 0 root)
    (hbelow : ∃ player, tail player < reward (quittingSingletonTerminal player) player)
    (hbad : ∀ player, reward (quittingSingletonTerminal player) player <
      quittingRootSuccessorPayoff reward tail root player)
    (other : ι) (hsure : (root other true).toReal = 1) :
    (quittingGame reward).IsUniformEquilibriumPayoff none
      (quittingSetReward reward (quittingPremiumCore reward)) := by
  have hsupport := exactRoot_bad_successor_support_subset_core reward tail root hnash hbelow hbad
  have hroot := exactRoot_eq_pureCore_of_joiningAttractive_sureHazard
    reward tail hjoining root hnash hsupport other hsure
  have hcard : 2 ≤ (quittingPremiumCore reward).card :=
    (exactRoot_bad_successor_support_card_ge_two reward tail root hnash hbelow hbad).trans
      (Finset.card_le_card hsupport)
  apply isUniformEquilibriumPayoff_setReward_of_pureSetNash reward tail
    (quittingPremiumCore reward) hcard
  rwa [← hroot]

theorem exactRoot_bad_support_proper_of_joiningAttractive_noPureCore
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (tail : Payoff ι)
    (hjoining : HasStrictJoiningAttractivePremiumCore reward)
    (root : ι → PMF Bool) (hnash : IsεQuittingRootNash reward tail 0 root)
    (hbelow : ∃ player, tail player < reward (quittingSingletonTerminal player) player)
    (hbad : ∀ player, reward (quittingSingletonTerminal player) player <
      quittingRootSuccessorPayoff reward tail root player)
    (hnopure : ¬IsεQuittingRootNash reward tail 0
      (quittingPureSetRoot (quittingPremiumCore reward))) :
    ∀ player ∈ quittingPositiveHazardSupport root,
      (root player true).toReal ∈ Ioo (0 : ℝ) 1 := by
  have hsupport := exactRoot_bad_successor_support_subset_core reward tail root hnash hbelow hbad
  intro player hplayer
  refine ⟨(Finset.mem_filter.mp hplayer).2, ?_⟩
  by_contra hnot
  have hsure : (root player true).toReal = 1 :=
    le_antisymm (hazardOfRoot_le_one root player) (le_of_not_gt hnot)
  have hroot := exactRoot_eq_pureCore_of_joiningAttractive_sureHazard
    reward tail hjoining root hnash hsupport player hsure
  exact hnopure (hroot ▸ hnash)

end GameTheory
