import UniformEquilibrium.Quitting.Classification.JoiningAttractiveCorePartials
import UniformEquilibrium.Quitting.Classification.CorePairTieAvoidance

/-! # Actual negative derivatives of joining-attractive bad roots

Every bad root has pair or full triple support. The sure-hazard cascade
excludes saturation after the pure-core alternative is removed. Pair ties
are excluded by the actual annotation domain; triple partials come directly
from the reward-only joining comparisons.
-/

noncomputable section

namespace GameTheory

open Set QuittingSureSetOwnerRepair

variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem dense_quittingCorePairTieAvoidanceDomain_of_joiningAttractive
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hattractive : HasStrictJoiningAttractivePremiumCore reward) :
    Dense (quittingPairTieAvoidanceDomain reward (quittingCoreOrderedPairs reward)) := by
  apply dense_quittingPairTieAvoidanceDomain
  intro pair hpair
  obtain ⟨_, hfirst, hsecond, hne⟩ := Finset.mem_filter.mp hpair
  exact ne_of_gt (mul_pos
    (quittingPairJoiningGap_pos_of_joiningAttractive_core reward hattractive hne hfirst hsecond)
    (quittingPairJoiningGap_pos_of_joiningAttractive_core reward hattractive
      hne.symm hsecond hfirst))

theorem joiningAttractive_badRoot_hasFDerivAt_and_negative_det
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (tail : Payoff ι)
    (hattractive : HasStrictJoiningAttractivePremiumCore reward)
    (hcard : (quittingPremiumCore reward).card = 3)
    (havoid : tail ∈ quittingPairTieAvoidanceDomain reward (quittingCoreOrderedPairs reward))
    (hbelow : ∃ player, tail player < reward (quittingSingletonTerminal player) player)
    (hnopure : ¬IsεQuittingRootNash reward tail 0
      (quittingPureSetRoot (quittingPremiumCore reward)))
    (root : ι → PMF Bool) (hnash : IsεQuittingRootNash reward tail 0 root)
    (hbad : ∀ player, reward (quittingSingletonTerminal player) player <
      quittingRootSuccessorPayoff reward tail root player) :
    ∃ derivative : (ι → ℝ) →L[ℝ] (ι → ℝ),
      HasFDerivAt (fun hazard => hazard - quittingFullClippedEndpointMap reward tail hazard)
        derivative (hazardOfRoot root) ∧
        (LinearMap.toMatrix' derivative.toLinearMap).det < 0 := by
  have hsubset := exactRoot_bad_successor_support_subset_core
    reward tail root hnash hbelow hbad
  have hproper := exactRoot_bad_support_proper_of_joiningAttractive_noPureCore
    reward tail hattractive root hnash hbelow hbad hnopure
  rcases exactRoot_bad_successor_support_pair_or_core_of_core_card_three
    reward tail hcard root hnash hbelow hbad with ⟨first, second, hne, hsupport⟩ | hsupport
  · have hfirstCore : first ∈ quittingPremiumCore reward :=
      hsubset (by rw [hsupport]; simp)
    have hsecondCore : second ∈ quittingPremiumCore reward :=
      hsubset (by rw [hsupport]; simp)
    have hproduct := mul_pos
      (quittingPairJoiningGap_pos_of_joiningAttractive_core reward hattractive
        hne hfirstCore hsecondCore)
      (quittingPairJoiningGap_pos_of_joiningAttractive_core reward hattractive
        hne.symm hsecondCore hfirstCore)
    exact proper_pairNash_hasFDerivAt_and_negative_det_of_core_tieAvoidance
      reward tail root hnash hsubset hproper hne hsupport hproduct havoid
  · obtain ⟨first, second, third, hfirstSecond, hfirstThird, hsecondThird, hcore⟩ :=
      Finset.card_eq_three.mp hcard
    have hproperCore : ∀ player ∈ quittingPremiumCore reward,
        (root player true).toReal ∈ Ioo (0 : ℝ) 1 := by
      simpa only [hsupport] using hproper
    have hpartial : ∀ a b c : ι, a ≠ b → a ≠ c → b ≠ c →
        quittingPremiumCore reward = {a, b, c} →
        0 < quittingRealHazardEndpointPartial reward tail (hazardOfRoot root) a b := by
      intro a b c hab hac hbc hcoreABC
      apply quittingRealHazardEndpointPartial_pos_of_joiningAttractive_core
        reward tail hattractive root hab hac hbc hcoreABC hsubset hnash
      · exact hproperCore a (by rw [hcoreABC]; simp)
      · exact hproperCore b (by rw [hcoreABC]; simp)
      · exact (hproperCore c (by rw [hcoreABC]; simp)).2
    have hperm : ∀ a b c : ι, ({a, b, c} : Finset ι) = {first, second, third} →
        quittingPremiumCore reward = {a, b, c} := by
      intro a b c heq
      exact hcore.trans heq.symm
    have h12 := hpartial first second third hfirstSecond hfirstThird hsecondThird hcore
    have h23 := hpartial second third first hsecondThird hfirstSecond.symm hfirstThird.symm
      (hperm _ _ _ (by ext player; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto))
    have h31 := hpartial third first second hfirstThird.symm hsecondThird.symm hfirstSecond
      (hperm _ _ _ (by ext player; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto))
    have h13 := hpartial first third second hfirstThird hfirstSecond hsecondThird.symm
      (hperm _ _ _ (by ext player; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto))
    have h21 := hpartial second first third hfirstSecond.symm hsecondThird hfirstThird
      (hperm _ _ _ (by ext player; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto))
    have h32 := hpartial third second first hsecondThird.symm hfirstThird.symm hfirstSecond.symm
      (hperm _ _ _ (by ext player; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto))
    have hcertificate := tripleNash_hasFDerivAt_and_negative_det_fullClippedDisplacement
      reward tail root hfirstSecond hfirstThird hsecondThird (hsupport.trans hcore)
      (fun player hplayer => hproperCore player (hcore.symm ▸ hplayer)) hnash
      (fun player hplayer => exactRoot_bad_successor_outside_core_gap_neg
        reward tail root hnash hbelow hbad player (hcore.symm ▸ hplayer))
      (add_pos (mul_pos (mul_pos h12 h23) h31) (mul_pos (mul_pos h13 h21) h32))
    exact ⟨_, hcertificate.1, hcertificate.2.1⟩

end GameTheory
