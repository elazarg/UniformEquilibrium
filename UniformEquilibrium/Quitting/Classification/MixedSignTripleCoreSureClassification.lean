import UniformEquilibrium.Quitting.Classification.BadRootPremiumSupport
import UniformEquilibrium.Quitting.Classification.SignedPairCoreBadRoot
import UniformEquilibrium.Quitting.Root.TripleEndpointPartials

/-! # Mixed-sign triple joining data and actual partly-sure roots

The two two-opponent equalities are literal raw reward conditions, not
open-neighborhood assumptions. Sure hazards at either positive-pair member
force the actual pure pair; the opposite-sign member is handled separately.
-/

noncomputable section

namespace GameTheory

open Set

variable {ι : Type} [Fintype ι] [DecidableEq ι]

structure HasMixedSignTripleJoining
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (first second third : ι) : Prop where
  first_second_pos : 0 < quittingPairJoiningGap reward first second
  second_first_pos : 0 < quittingPairJoiningGap reward second first
  first_third_neg : quittingPairJoiningGap reward first third < 0
  third_first_neg : quittingPairJoiningGap reward third first < 0
  second_third_neg : quittingPairJoiningGap reward second third < 0
  third_second_neg : quittingPairJoiningGap reward third second < 0
  first_triple_zero : quittingTripleJoiningGap reward first second third = 0
  second_triple_zero : quittingTripleJoiningGap reward second first third = 0
  third_triple_neg : quittingTripleJoiningGap reward third first second < 0

private theorem quit_probability_zero_of_gap_neg
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (tail : Payoff ι)
    (root : ι → PMF Bool) (hnash : IsεQuittingRootNash reward tail 0 root)
    (player : ι) (hgap : quittingRootEndpointDifference reward tail root player < 0) :
    (root player true).toReal = 0 := by
  have hendpoint :=
    (isZeroQuittingRootEndpointNash_iff_isZeroQuittingRootNash reward tail root).mpr hnash
  have hproduct := (hendpoint player).2
  have hnonneg : 0 ≤ (root player true).toReal := ENNReal.toReal_nonneg
  nlinarith

private theorem quit_probability_one_of_gap_pos
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (tail : Payoff ι)
    (root : ι → PMF Bool) (hnash : IsεQuittingRootNash reward tail 0 root)
    (player : ι) (hgap : 0 < quittingRootEndpointDifference reward tail root player) :
    (root player true).toReal = 1 := by
  have hendpoint :=
    (isZeroQuittingRootEndpointNash_iff_isZeroQuittingRootNash reward tail root).mpr hnash
  have hproduct := (hendpoint player).1
  have hnonneg : 0 ≤ (root player false).toReal := ENNReal.toReal_nonneg
  have hsum := quittingRoot_continueProbability_add_quitProbability root player
  nlinarith

theorem exactRoot_eq_purePair_of_sureFirst_and_joiningSigns
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (tail : Payoff ι)
    (root : ι → PMF Bool) {first second third : ι}
    (hfirstSecond : first ≠ second) (hfirstThird : first ≠ third)
    (hsecondThird : second ≠ third)
    (hsupport : quittingPositiveHazardSupport root ⊆ {first, second, third})
    (hnash : IsεQuittingRootNash reward tail 0 root)
    (hsure : (root first true).toReal = 1)
    (hpositive : 0 < quittingPairJoiningGap reward second first)
    (hnegative : quittingPairJoiningGap reward third first < 0)
    (hnegativeTriple : quittingTripleJoiningGap reward third first second < 0) :
    root = PairedCycle.root first second (PMF.pure true) (PMF.pure true) := by
  have hsupportThird : quittingPositiveHazardSupport root ⊆ {third, first, second} := by
    intro player hplayer
    have := hsupport hplayer
    simp only [Finset.mem_insert, Finset.mem_singleton] at this ⊢
    tauto
  have hthirdExpansion := quittingRootEndpointDifference_eq_triple_expansion reward tail root
    hfirstThird.symm hsecondThird.symm hfirstSecond hsupportThird
  simp [hsure] at hthirdExpansion
  have hthirdGap : quittingRootEndpointDifference reward tail root third < 0 := by
    rw [hthirdExpansion]
    have hq := hazardOfRoot_nonneg root second
    have hc := sub_nonneg.mpr (hazardOfRoot_le_one root second)
    by_cases hzero : (root second true).toReal = 0
    · simpa [hzero] using hnegative
    · exact add_neg_of_nonpos_of_neg
        (mul_nonpos_of_nonneg_of_nonpos hc hnegative.le)
        (mul_neg_of_pos_of_neg (lt_of_le_of_ne hq (Ne.symm hzero)) hnegativeTriple)
  have hthirdZero := quit_probability_zero_of_gap_neg reward tail root hnash third hthirdGap
  have hsupportSecond : quittingPositiveHazardSupport root ⊆ {second, first, third} := by
    intro player hplayer
    have := hsupport hplayer
    simp only [Finset.mem_insert, Finset.mem_singleton] at this ⊢
    tauto
  have hsecondExpansion := quittingRootEndpointDifference_eq_triple_expansion reward tail root
    hfirstSecond.symm hsecondThird hfirstThird hsupportSecond
  have hsecondGap : 0 < quittingRootEndpointDifference reward tail root second := by
    simp [hsure, hthirdZero] at hsecondExpansion
    rw [hsecondExpansion]
    exact hpositive
  have hsecondSure := quit_probability_one_of_gap_pos reward tail root hnash second hsecondGap
  have hpairSupport : quittingPositiveHazardSupport root = {first, second} := by
    ext player
    constructor
    · intro hplayer
      have := hsupport hplayer
      simp only [Finset.mem_insert, Finset.mem_singleton] at this ⊢
      rcases this with rfl | rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr rfl
      · have hpositiveThird := (Finset.mem_filter.mp hplayer).2
        change 0 < (root player true).toReal at hpositiveThird
        rw [hthirdZero] at hpositiveThird
        exact False.elim (lt_irrefl _ hpositiveThird)
    · intro hplayer
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      simp only [Finset.mem_insert, Finset.mem_singleton] at hplayer
      rcases hplayer with rfl | rfl
      · change 0 < (root player true).toReal
        simpa only [hsure] using (zero_lt_one : (0 : ℝ) < 1)
      · change 0 < (root player true).toReal
        simpa only [hsecondSure] using (zero_lt_one : (0 : ℝ) < 1)
  rw [quittingRoot_eq_pairedRoot_of_support_eq_pair root hfirstSecond hpairSupport,
    Math.PMFProduct.eq_pure_true_of_true_toReal_eq_one (root first) hsure,
    Math.PMFProduct.eq_pure_true_of_true_toReal_eq_one (root second) hsecondSure]

theorem exactRoot_bad_third_not_sure_of_mixedSignTriple
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (tail : Payoff ι)
    {first second third : ι} (hfirstSecond : first ≠ second)
    (hfirstThird : first ≠ third) (hsecondThird : second ≠ third)
    (hcore : quittingPremiumCore reward = {first, second, third})
    (hjoining : HasMixedSignTripleJoining reward first second third)
    (root : ι → PMF Bool) (hnash : IsεQuittingRootNash reward tail 0 root)
    (hbelow : ∃ player, tail player < reward (quittingSingletonTerminal player) player)
    (hbad : ∀ player, reward (quittingSingletonTerminal player) player <
      quittingRootSuccessorPayoff reward tail root player) :
    (root third true).toReal ≠ 1 := by
  intro hsure
  have hsupport := exactRoot_bad_successor_support_subset_core
    reward tail root hnash hbelow hbad
  rw [hcore] at hsupport
  have hsecondSupport : quittingPositiveHazardSupport root ⊆ {second, first, third} := by
    intro player hplayer
    have := hsupport hplayer
    simp only [Finset.mem_insert, Finset.mem_singleton] at this ⊢
    tauto
  have hthirdSupport : quittingPositiveHazardSupport root ⊆ {third, first, second} := by
    intro player hplayer
    have := hsupport hplayer
    simp only [Finset.mem_insert, Finset.mem_singleton] at this ⊢
    tauto
  have hfirstExpansion := quittingRootEndpointDifference_eq_triple_expansion reward tail root
    hfirstSecond hfirstThird hsecondThird hsupport
  have hsecondExpansion := quittingRootEndpointDifference_eq_triple_expansion reward tail root
    hfirstSecond.symm hsecondThird hfirstThird hsecondSupport
  simp [hsure, hjoining.first_triple_zero] at hfirstExpansion
  simp [hsure, hjoining.second_triple_zero] at hsecondExpansion
  have hendpoint :=
    (isZeroQuittingRootEndpointNash_iff_isZeroQuittingRootNash reward tail root).mpr hnash
  by_cases hsecondSure : (root second true).toReal = 1
  · have hsecondOptimal := (hendpoint second).2
    rw [hsecondSure, one_mul, hsecondExpansion] at hsecondOptimal
    have hfirstSure : (root first true).toReal = 1 := by
      have hfirstLe := hazardOfRoot_le_one root first
      change (root first true).toReal ≤ 1 at hfirstLe
      have hnegative := hjoining.second_third_neg
      nlinarith
    have hthirdExpansion := quittingRootEndpointDifference_eq_triple_expansion reward tail root
      hfirstThird.symm hsecondThird.symm hfirstSecond hthirdSupport
    simp [hfirstSure, hsecondSure] at hthirdExpansion
    have hthirdOptimal := (hendpoint third).2
    rw [hsure, one_mul, hthirdExpansion] at hthirdOptimal
    exact (not_le_of_gt hjoining.third_triple_neg) (by simpa only [neg_zero] using hthirdOptimal)
  · have hsecondLt : (root second true).toReal < 1 :=
      lt_of_le_of_ne (hazardOfRoot_le_one root second) hsecondSure
    have hfirstGap : quittingRootEndpointDifference reward tail root first < 0 := by
      rw [hfirstExpansion]
      exact mul_neg_of_pos_of_neg (sub_pos.mpr hsecondLt) hjoining.first_third_neg
    have hfirstZero := quit_probability_zero_of_gap_neg reward tail root hnash first hfirstGap
    have hsecondGap : quittingRootEndpointDifference reward tail root second < 0 := by
      rw [hsecondExpansion, hfirstZero]
      simpa using hjoining.second_third_neg
    have hsecondZero := quit_probability_zero_of_gap_neg reward tail root hnash second hsecondGap
    have hsmall : quittingPositiveHazardSupport root ⊆ {third} := by
      intro player hplayer
      have hmember := hsupport hplayer
      simp only [Finset.mem_insert, Finset.mem_singleton] at hmember ⊢
      rcases hmember with rfl | rfl | rfl
      · have hpositive := (Finset.mem_filter.mp hplayer).2
        change 0 < (root player true).toReal at hpositive
        rw [hfirstZero] at hpositive
        exact False.elim (lt_irrefl _ hpositive)
      · have hpositive := (Finset.mem_filter.mp hplayer).2
        change 0 < (root player true).toReal at hpositive
        rw [hsecondZero] at hpositive
        exact False.elim (lt_irrefl _ hpositive)
      · rfl
    have hlower := exactRoot_bad_successor_support_card_ge_two
      reward tail root hnash hbelow hbad
    have hupper := Finset.card_le_card hsmall
    simp only [Finset.card_singleton] at hupper
    omega

theorem exactRoot_bad_support_proper_of_mixedSignTriple_noPurePair
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (tail : Payoff ι)
    {first second third : ι} (hfirstSecond : first ≠ second)
    (hfirstThird : first ≠ third) (hsecondThird : second ≠ third)
    (hcore : quittingPremiumCore reward = {first, second, third})
    (hjoining : HasMixedSignTripleJoining reward first second third)
    (root : ι → PMF Bool) (hnash : IsεQuittingRootNash reward tail 0 root)
    (hbelow : ∃ player, tail player < reward (quittingSingletonTerminal player) player)
    (hbad : ∀ player, reward (quittingSingletonTerminal player) player <
      quittingRootSuccessorPayoff reward tail root player)
    (hnopure : ¬IsεQuittingRootNash reward tail 0
      (PairedCycle.root first second (PMF.pure true) (PMF.pure true))) :
    ∀ player ∈ quittingPositiveHazardSupport root,
      (root player true).toReal ∈ Ioo (0 : ℝ) 1 := by
  have hsupport := exactRoot_bad_successor_support_subset_core
    reward tail root hnash hbelow hbad
  rw [hcore] at hsupport
  have hfirstNotSure : (root first true).toReal ≠ 1 := by
    intro hsure
    have hroot := exactRoot_eq_purePair_of_sureFirst_and_joiningSigns reward tail root
      hfirstSecond hfirstThird hsecondThird hsupport hnash hsure
      hjoining.second_first_pos hjoining.third_first_neg hjoining.third_triple_neg
    exact hnopure (hroot ▸ hnash)
  have hsecondNotSure : (root second true).toReal ≠ 1 := by
    intro hsure
    have hswappedSupport : quittingPositiveHazardSupport root ⊆ {second, first, third} := by
      intro player hplayer
      have := hsupport hplayer
      simp only [Finset.mem_insert, Finset.mem_singleton] at this ⊢
      tauto
    have hswappedTriple : quittingTripleJoiningGap reward third second first < 0 := by
      simpa only [quittingTripleJoiningGap, Finset.pair_comm] using hjoining.third_triple_neg
    have hroot := exactRoot_eq_purePair_of_sureFirst_and_joiningSigns reward tail root
      hfirstSecond.symm hsecondThird hfirstThird hswappedSupport hnash hsure
      hjoining.first_second_pos hjoining.third_second_neg hswappedTriple
    rw [PairedCycle.root_swap hfirstSecond.symm] at hroot
    exact hnopure (hroot ▸ hnash)
  have hthirdNotSure := exactRoot_bad_third_not_sure_of_mixedSignTriple reward tail
    hfirstSecond hfirstThird hsecondThird hcore hjoining root hnash hbelow hbad
  intro player hplayer
  refine ⟨(Finset.mem_filter.mp hplayer).2, ?_⟩
  apply lt_of_le_of_ne (hazardOfRoot_le_one root player)
  have hmember := hsupport hplayer
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmember
  rcases hmember with rfl | rfl | rfl
  · exact hfirstNotSure
  · exact hsecondNotSure
  · exact hthirdNotSure

end GameTheory
