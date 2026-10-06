import UniformEquilibrium.Quitting.Classification.CommonQuittingPremiumLeaver
import UniformEquilibrium.Quitting.Root.AllContinueWeightedRoot

/-! # Actual bad-root support and signed outsider bounds

At a source below some own singleton, an all-high exact successor has trap
support inside the greatest premium core. Outside-core gaps are strictly
negative. No participant-premium sign assumption is used.
-/

noncomputable section

namespace GameTheory

variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem quittingPremiumCore_outsider_reward_le_singleton
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hcore : (quittingPremiumCore reward).Nonempty)
    (player : ι) (houtside : player ∉ quittingPremiumCore reward)
    (terminal : {S : Finset ι // S.Nonempty})
    (hsubset : terminal.val ⊆ insert player (quittingPremiumCore reward))
    (hmember : player ∈ terminal.val) :
    reward terminal player ≤ reward (quittingSingletonTerminal player) player := by
  apply le_of_not_gt
  intro hpositive
  exact MathUE.not_positive_on_core_insert (HasPositiveOwnQuittingPremium reward)
    hcore player houtside terminal.val hsubset hmember ⟨terminal.property, hpositive⟩

theorem quittingRootQuitPayoff_le_singleton_of_core_support_outsider
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (tail : Payoff ι)
    (hcore : (quittingPremiumCore reward).Nonempty) (root : ι → PMF Bool)
    (hsupport : quittingPositiveHazardSupport root ⊆ quittingPremiumCore reward)
    (player : ι) (houtside : player ∉ quittingPremiumCore reward) :
    quittingRootQuitPayoff reward tail root player ≤
      reward (quittingSingletonTerminal player) player := by
  apply quittingRootQuitPayoff_le_singleton_of_support_participantReward
  intro terminal hsubset hmember
  exact quittingPremiumCore_outsider_reward_le_singleton reward hcore player houtside
    terminal (hsubset.trans (Finset.insert_subset_insert player hsupport)) hmember

theorem exactRoot_absorptionMass_pos_of_below_singleton
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (tail : Payoff ι)
    (root : ι → PMF Bool) (hnash : IsεQuittingRootNash reward tail 0 root)
    (hbelow : ∃ player, tail player < reward (quittingSingletonTerminal player) player) :
    0 < quittingRootAbsorptionMass root := by
  rw [quittingRootAbsorptionMass_pos_iff_exists_quitProbability_pos]
  by_contra hnot
  have hroot : root = quittingAllContinueRoot := by
    funext player
    apply Math.PMFProduct.eq_pure_false_of_true_toReal_eq_zero
    apply le_antisymm
    · exact le_of_not_gt (fun hpositive => hnot ⟨player, hpositive⟩)
    · exact ENNReal.toReal_nonneg
  obtain ⟨player, hplayer⟩ := hbelow
  have hquit := quittingRootQuitPayoff_le_successor_add_of_isεNash reward tail 0 root player hnash
  rw [hroot, quittingRootQuitPayoff_allContinueRoot,
    quittingRootSuccessorPayoff_allContinueRoot_eq] at hquit
  exact (not_le_of_gt hplayer) (by simpa only [add_zero] using hquit)

theorem exactRoot_bad_successor_isPremiumTrap
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (tail : Payoff ι)
    (root : ι → PMF Bool) (hnash : IsεQuittingRootNash reward tail 0 root)
    (hbelow : ∃ player, tail player < reward (quittingSingletonTerminal player) player)
    (hbad : ∀ player, reward (quittingSingletonTerminal player) player <
      quittingRootSuccessorPayoff reward tail root player) :
    IsQuittingPremiumTrap reward (quittingPositiveHazardSupport root) := by
  by_contra hnot
  obtain ⟨player, hplayer⟩ := exists_successor_le_singleton_of_exactRoot_nontrap_support
    reward tail root hnash
    (exactRoot_absorptionMass_pos_of_below_singleton reward tail root hnash hbelow) hnot
  exact (not_le_of_gt (hbad player)) hplayer

theorem exactRoot_bad_successor_support_subset_core
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (tail : Payoff ι)
    (root : ι → PMF Bool) (hnash : IsεQuittingRootNash reward tail 0 root)
    (hbelow : ∃ player, tail player < reward (quittingSingletonTerminal player) player)
    (hbad : ∀ player, reward (quittingSingletonTerminal player) player <
      quittingRootSuccessorPayoff reward tail root player) :
    quittingPositiveHazardSupport root ⊆ quittingPremiumCore reward := by
  exact MathUE.IsFiniteCoalitionPremiumTrap.subset_core
    (exactRoot_bad_successor_isPremiumTrap reward tail root hnash hbelow hbad)

theorem exactRoot_bad_successor_support_card_ge_two
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (tail : Payoff ι)
    (root : ι → PMF Bool) (hnash : IsεQuittingRootNash reward tail 0 root)
    (hbelow : ∃ player, tail player < reward (quittingSingletonTerminal player) player)
    (hbad : ∀ player, reward (quittingSingletonTerminal player) player <
      quittingRootSuccessorPayoff reward tail root player) :
    2 ≤ (quittingPositiveHazardSupport root).card := by
  have htrap := exactRoot_bad_successor_isPremiumTrap reward tail root hnash hbelow hbad
  obtain ⟨chosen, hchosen⟩ := htrap.1
  by_contra hcard
  have hsmall : (quittingPositiveHazardSupport root).card ≤ 1 := by omega
  have hsubset : quittingPositiveHazardSupport root ⊆ {chosen} := by
    intro player hplayer
    exact Finset.mem_singleton.mpr ((Finset.card_le_one.mp hsmall) player hplayer chosen hchosen)
  have heq : quittingPositiveHazardSupport root = {chosen} :=
    Finset.Subset.antisymm hsubset (Finset.singleton_subset_iff.mpr hchosen)
  exact not_isQuittingPremiumTrap_singleton reward chosen (heq ▸ htrap)

theorem exactRoot_bad_successor_outside_core_gap_neg
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (tail : Payoff ι)
    (root : ι → PMF Bool) (hnash : IsεQuittingRootNash reward tail 0 root)
    (hbelow : ∃ player, tail player < reward (quittingSingletonTerminal player) player)
    (hbad : ∀ player, reward (quittingSingletonTerminal player) player <
      quittingRootSuccessorPayoff reward tail root player)
    (player : ι) (houtside : player ∉ quittingPremiumCore reward) :
    quittingRootEndpointDifference reward tail root player < 0 := by
  have htrap := exactRoot_bad_successor_isPremiumTrap reward tail root hnash hbelow hbad
  have hsubset := exactRoot_bad_successor_support_subset_core reward tail root hnash hbelow hbad
  have hcoreNonempty : (quittingPremiumCore reward).Nonempty := htrap.1.mono hsubset
  have hquit := quittingRootQuitPayoff_le_singleton_of_core_support_outsider
    reward tail hcoreNonempty root hsubset player houtside
  have hpure := quittingRoot_eq_pure_false_of_not_mem_positiveHazardSupport root
    (fun hplayer => houtside (hsubset hplayer))
  have hcontinue : quittingRootContinuePayoff reward tail root player =
      quittingRootSuccessorPayoff reward tail root player := by
    unfold quittingRootContinuePayoff
    rw [Function.update_eq_self_iff.mpr hpure.symm]
    rfl
  unfold quittingRootEndpointDifference
  rw [hcontinue]
  exact sub_neg.mpr (hquit.trans_lt (hbad player))

theorem exactRoot_bad_successor_support_pair_or_core_of_core_card_three
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (tail : Payoff ι)
    (hcard : (quittingPremiumCore reward).card = 3)
    (root : ι → PMF Bool) (hnash : IsεQuittingRootNash reward tail 0 root)
    (hbelow : ∃ player, tail player < reward (quittingSingletonTerminal player) player)
    (hbad : ∀ player, reward (quittingSingletonTerminal player) player <
      quittingRootSuccessorPayoff reward tail root player) :
    (∃ first second : ι, first ≠ second ∧
      quittingPositiveHazardSupport root = {first, second}) ∨
      quittingPositiveHazardSupport root = quittingPremiumCore reward := by
  have hsubset := exactRoot_bad_successor_support_subset_core reward tail root hnash hbelow hbad
  have hlower := exactRoot_bad_successor_support_card_ge_two reward tail root hnash hbelow hbad
  have hupper := Finset.card_le_card hsubset
  by_cases hpair : (quittingPositiveHazardSupport root).card = 2
  · exact Or.inl (Finset.card_eq_two.mp hpair)
  · right
    apply Finset.eq_of_subset_of_card_le hsubset
    omega

end GameTheory
