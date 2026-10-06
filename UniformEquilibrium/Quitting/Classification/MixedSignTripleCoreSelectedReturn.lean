import UniformEquilibrium.Quitting.Classification.MixedSignTripleCoreJacobian
import UniformEquilibrium.Quitting.Classification.CorePairTieAvoidance
import UniformEquilibrium.Quitting.Root.NegativeBadRootSelectedReturn
import UniformEquilibrium.Quitting.Projective.SelectedSingletonSublevelReturnSmoothDrift

/-! # Actual selected return from mixed-sign triple-core reward data

The seven strict signed comparisons and two equalities supply every proper
pair/triple actual derivative internally. Dense annotation restoration uses
the same full-root closed relation. The pure positive-pair exit is explicit.
-/

noncomputable section

namespace GameTheory

open Set

variable {ι : Type} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] in
theorem HasMixedSignTripleJoining.pairwise_distinct
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι} {first second third : ι}
    (hjoining : HasMixedSignTripleJoining reward first second third) :
    first ≠ second ∧ first ≠ third ∧ second ≠ third := by
  refine ⟨?_, ?_, ?_⟩
  · intro heq
    subst second
    have hpositive := hjoining.first_second_pos
    simp [quittingPairJoiningGap, quittingSingletonTerminal] at hpositive
  · intro heq
    subst third
    have hnegative := hjoining.first_third_neg
    simp [quittingPairJoiningGap, quittingSingletonTerminal] at hnegative
  · intro heq
    subst third
    have hnegative := hjoining.second_third_neg
    simp [quittingPairJoiningGap, quittingSingletonTerminal] at hnegative

theorem quittingPairJoiningGap_product_pos_of_mixedSignTriple
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    {first second third : ι} (hcore : quittingPremiumCore reward = {first, second, third})
    (hjoining : HasMixedSignTripleJoining reward first second third)
    {row column : ι} (hrow : row ∈ quittingPremiumCore reward)
    (hcolumn : column ∈ quittingPremiumCore reward) (hne : row ≠ column) :
    0 < quittingPairJoiningGap reward row column *
      quittingPairJoiningGap reward column row := by
  rw [hcore] at hrow hcolumn
  simp only [Finset.mem_insert, Finset.mem_singleton] at hrow hcolumn
  rcases hrow with rfl | rfl | rfl <;> rcases hcolumn with rfl | rfl | rfl <;>
    first
    | exact False.elim (hne rfl)
    | exact mul_pos hjoining.first_second_pos hjoining.second_first_pos
    | exact mul_pos hjoining.second_first_pos hjoining.first_second_pos
    | exact mul_pos_of_neg_of_neg hjoining.first_third_neg hjoining.third_first_neg
    | exact mul_pos_of_neg_of_neg hjoining.third_first_neg hjoining.first_third_neg
    | exact mul_pos_of_neg_of_neg hjoining.second_third_neg hjoining.third_second_neg
    | exact mul_pos_of_neg_of_neg hjoining.third_second_neg hjoining.second_third_neg

theorem mixedSignTriple_badRoot_hasFDerivAt_and_negative_det
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (tail : Payoff ι)
    {first second third : ι} (hcore : quittingPremiumCore reward = {first, second, third})
    (hjoining : HasMixedSignTripleJoining reward first second third)
    (havoid : tail ∈ quittingPairTieAvoidanceDomain reward (quittingCoreOrderedPairs reward))
    (hbelow : ∃ player, tail player < reward (quittingSingletonTerminal player) player)
    (hnopure : ¬IsεQuittingRootNash reward tail 0
      (PairedCycle.root first second (PMF.pure true) (PMF.pure true)))
    (root : ι → PMF Bool) (hnash : IsεQuittingRootNash reward tail 0 root)
    (hbad : ∀ player, reward (quittingSingletonTerminal player) player <
      quittingRootSuccessorPayoff reward tail root player) :
    ∃ derivative : (ι → ℝ) →L[ℝ] (ι → ℝ),
      HasFDerivAt (fun hazard => hazard - quittingFullClippedEndpointMap reward tail hazard)
        derivative (hazardOfRoot root) ∧
        (LinearMap.toMatrix' derivative.toLinearMap).det < 0 := by
  obtain ⟨hfirstSecond, hfirstThird, hsecondThird⟩ := hjoining.pairwise_distinct
  have hcard : (quittingPremiumCore reward).card = 3 := by
    rw [hcore]
    simp [hfirstSecond, hfirstThird, hsecondThird]
  have hsubset := exactRoot_bad_successor_support_subset_core
    reward tail root hnash hbelow hbad
  have hproper := exactRoot_bad_support_proper_of_mixedSignTriple_noPurePair reward tail
    hfirstSecond hfirstThird hsecondThird hcore hjoining root hnash hbelow hbad hnopure
  rcases exactRoot_bad_successor_support_pair_or_core_of_core_card_three
    reward tail hcard root hnash hbelow hbad with ⟨a, b, hab, hsupport⟩ | hsupport
  · have ha := hsubset (show a ∈ quittingPositiveHazardSupport root by rw [hsupport]; simp)
    have hb := hsubset (show b ∈ quittingPositiveHazardSupport root by rw [hsupport]; simp)
    exact proper_pairNash_hasFDerivAt_and_negative_det_of_core_tieAvoidance
      reward tail root hnash hsubset hproper hab hsupport
      (quittingPairJoiningGap_product_pos_of_mixedSignTriple reward hcore hjoining ha hb hab)
      havoid
  · have hcertificate := mixedSignTripleNash_hasFDerivAt_and_negative_det reward tail
      hfirstSecond hfirstThird hsecondThird hjoining root (hsupport.trans hcore)
      (fun player hplayer => hproper player ((hsupport.trans hcore).symm ▸ hplayer)) hnash
      (fun player hplayer => exactRoot_bad_successor_outside_core_gap_neg
        reward tail root hnash hbelow hbad player (hcore.symm ▸ hplayer))
    exact ⟨_, hcertificate.1, hcertificate.2⟩

theorem exists_exactRoot_singletonSublevel_of_mixedSignTriple_core
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (tail : Payoff ι)
    {first second third : ι} (hcore : quittingPremiumCore reward = {first, second, third})
    (hjoining : HasMixedSignTripleJoining reward first second third)
    (hbelow : ∃ player, tail player < reward (quittingSingletonTerminal player) player)
    (hnopure : ¬IsεQuittingRootNash reward tail 0
      (PairedCycle.root first second (PMF.pure true) (PMF.pure true))) :
    ∃ root, IsεQuittingRootNash reward tail 0 root ∧
      ∃ player, quittingRootSuccessorPayoff reward tail root player ≤
        reward (quittingSingletonTerminal player) player := by
  apply exists_exactRoot_singletonSublevel_of_dense_sources_excluding_root reward
    (quittingPairTieAvoidanceDomain reward (quittingCoreOrderedPairs reward))
    (dense_quittingCorePairTieAvoidanceDomain_of_positive_pair_products reward
      (fun a ha b hb hab => quittingPairJoiningGap_product_pos_of_mixedSignTriple
        reward hcore hjoining ha hb hab))
    (PairedCycle.root first second (PMF.pure true) (PMF.pure true))
    ?_ tail hbelow hnopure
  intro source havoid hsourceBelow hsourceNoPure
  apply exists_exactRoot_singletonSublevel_of_badRoot_negative_derivatives reward source
  intro root hnash hbad
  exact mixedSignTriple_badRoot_hasFDerivAt_and_negative_det reward source
    hcore hjoining havoid hsourceBelow hsourceNoPure root hnash hbad

theorem hasBoxedSelectedSingletonSublevelReturn_of_mixedSignTriple_core
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    {first second third : ι} (hcore : quittingPremiumCore reward = {first, second, third})
    (hjoining : HasMixedSignTripleJoining reward first second third)
    (hnopure : ∀ tail, ¬IsεQuittingRootNash reward tail 0
      (PairedCycle.root first second (PMF.pure true) (PMF.pure true)))
    (bound : ℝ) : HasBoxedSelectedSingletonSublevelReturn reward bound := by
  intro tail _ hbelow
  simpa only [quittingSoloReward, quittingSingletonTerminal] using
    exists_exactRoot_singletonSublevel_of_mixedSignTriple_core
      reward tail hcore hjoining hbelow (hnopure tail)

end GameTheory
