import UniformEquilibrium.Quitting.Classification.CommonQuittingPremiumLeaver
import UniformEquilibrium.Quitting.Classification.QuittingPremiumCorePair
import UniformEquilibrium.Quitting.Root.PairFullClippedJacobian
import UniformEquilibrium.Quitting.Root.AllContinueWeightedRoot

/-! # Literal bad-root classification on a signed greatest pair core

No nonnegative participant-premium assumption is used. Badness means every
successor coordinate strictly exceeds its own singleton. The pure-pair
alternative is explicitly excluded only in the proper-mixture statements;
no selected-return or uniform-equilibrium conclusion is asserted here.
-/

noncomputable section

namespace GameTheory

open Set

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

theorem exactRoot_bad_successor_support_eq_pair_core
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (tail : Payoff ι)
    (first second : ι) (hcore : quittingPremiumCore reward = {first, second})
    (root : ι → PMF Bool) (hnash : IsεQuittingRootNash reward tail 0 root)
    (hbelow : ∃ player, tail player < reward (quittingSingletonTerminal player) player)
    (hbad : ∀ player, reward (quittingSingletonTerminal player) player <
      quittingRootSuccessorPayoff reward tail root player) :
    quittingPositiveHazardSupport root = {first, second} := by
  have htrap : IsQuittingPremiumTrap reward (quittingPositiveHazardSupport root) := by
    by_contra hnot
    obtain ⟨player, hplayer⟩ := exists_successor_le_singleton_of_exactRoot_nontrap_support
      reward tail root hnash
      (exactRoot_absorptionMass_pos_of_below_singleton reward tail root hnash hbelow) hnot
    exact (not_le_of_gt (hbad player)) hplayer
  have hsubset := MathUE.IsFiniteCoalitionPremiumTrap.subset_core htrap
  change quittingPositiveHazardSupport root ⊆ quittingPremiumCore reward at hsubset
  rw [hcore] at hsubset
  exact MathUE.IsFiniteCoalitionPremiumTrap.eq_pair_of_subset
    (not_hasPositiveOwnQuittingPremium_singleton reward) htrap first second hsubset

theorem quittingRoot_eq_pairedRoot_of_support_eq_pair
    (root : ι → PMF Bool) {first second : ι} (hne : first ≠ second)
    (hsupport : quittingPositiveHazardSupport root = {first, second}) :
    root = PairedCycle.root first second (root first) (root second) := by
  funext player
  by_cases hfirst : player = first
  · subst player
    exact (PairedCycle.root_first hne _ _).symm
  · by_cases hsecond : player = second
    · subst player
      exact (PairedCycle.root_second first second _ _).symm
    · rw [PairedCycle.root_outside hfirst hsecond]
      apply quittingRoot_eq_pure_false_of_not_mem_positiveHazardSupport
      simp only [hsupport, Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨hfirst, hsecond⟩

theorem exactRoot_bad_successor_inactive_gap_neg_of_pair_core
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (tail : Payoff ι)
    (first second : ι) (hcore : quittingPremiumCore reward = {first, second})
    (root : ι → PMF Bool)
    (hsupport : quittingPositiveHazardSupport root = {first, second})
    (hbad : ∀ player, reward (quittingSingletonTerminal player) player <
      quittingRootSuccessorPayoff reward tail root player)
    (player : ι) (hfirst : player ≠ first) (hsecond : player ≠ second) :
    quittingRootEndpointDifference reward tail root player < 0 := by
  have houtside : player ∉ quittingPremiumCore reward := by simp [hcore, hfirst, hsecond]
  have hsupportCore : quittingPositiveHazardSupport root ⊆ quittingPremiumCore reward := by
    rw [hsupport, hcore]
  have hcoreNonempty : (quittingPremiumCore reward).Nonempty := by rw [hcore]; simp
  have hquit := quittingRootQuitPayoff_le_singleton_of_core_support_outsider reward tail
    hcoreNonempty root hsupportCore player houtside
  have hpure := quittingRoot_eq_pure_false_of_not_mem_positiveHazardSupport root
    (show player ∉ quittingPositiveHazardSupport root by simp [hsupport, hfirst, hsecond])
  have hcontinue : quittingRootContinuePayoff reward tail root player =
      quittingRootSuccessorPayoff reward tail root player := by
    unfold quittingRootContinuePayoff
    rw [Function.update_eq_self_iff.mpr hpure.symm]
    rfl
  unfold quittingRootEndpointDifference
  rw [hcontinue]
  exact sub_neg.mpr (hquit.trans_lt (hbad player))

private theorem pairedNash_first_probability_lt_one
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (tail : Payoff ι)
    {first second : ι} (hne : first ≠ second) (firstLaw secondLaw : PMF Bool)
    (hsecond : 0 < (secondLaw true).toReal)
    (hjoining : quittingPairJoiningGap reward second first ≠ 0)
    (hnash : IsεQuittingRootNash reward tail 0
      (PairedCycle.root first second firstLaw secondLaw))
    (hnopure : ¬IsεQuittingRootNash reward tail 0
      (PairedCycle.root first second (PMF.pure true) (PMF.pure true))) :
    (firstLaw true).toReal < 1 := by
  have hle : (firstLaw true).toReal ≤ 1 :=
    ENNReal.toReal_mono ENNReal.one_ne_top (PMF.coe_le_one firstLaw true)
  apply lt_of_le_of_ne hle
  intro hfull
  by_cases hsecondFull : (secondLaw true).toReal = 1
  · have hfirstPure := Math.PMFProduct.eq_pure_true_of_true_toReal_eq_one firstLaw hfull
    have hsecondPure := Math.PMFProduct.eq_pure_true_of_true_toReal_eq_one secondLaw hsecondFull
    exact hnopure (by simpa only [hfirstPure, hsecondPure] using hnash)
  · have hsecondLe : (secondLaw true).toReal ≤ 1 :=
      ENNReal.toReal_mono ENNReal.one_ne_top (PMF.coe_le_one secondLaw true)
    have hgap := quittingRootEndpointDifference_eq_zero_of_both_probabilities_pos
      reward tail (PairedCycle.root first second firstLaw secondLaw) second
      ((isZeroQuittingRootEndpointNash_iff_isZeroQuittingRootNash reward tail _).mpr hnash)
      (by rw [PairedCycle.root_second, Math.PMFProduct.pmfBool_false_toReal]
          exact sub_pos.mpr (lt_of_le_of_ne hsecondLe hsecondFull))
      (by simpa only [PairedCycle.root_second] using hsecond)
    unfold quittingRootEndpointDifference at hgap
    rw [PairedCycle.rootQuit_second reward tail hne,
      PairedCycle.rootContinue_second reward tail hne] at hgap
    apply hjoining
    simpa [quittingPairJoiningGap, Math.PairedAffine.activeValue, hfull,
      Finset.pair_comm] using hgap

/-- A bad root is a proper pair mixture once the literal pure-pair Nash
alternative is excluded. Both joining comparisons need only be nonzero. -/
theorem exactRoot_bad_successor_pair_probabilities_interior
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (tail : Payoff ι)
    {first second : ι} (hne : first ≠ second)
    (root : ι → PMF Bool) (hsupport : quittingPositiveHazardSupport root = {first, second})
    (hnash : IsεQuittingRootNash reward tail 0 root)
    (hjoiningFirst : quittingPairJoiningGap reward first second ≠ 0)
    (hjoiningSecond : quittingPairJoiningGap reward second first ≠ 0)
    (hnopure : ¬IsεQuittingRootNash reward tail 0
      (PairedCycle.root first second (PMF.pure true) (PMF.pure true))) :
    (root first true).toReal ∈ Ioo (0 : ℝ) 1 ∧
      (root second true).toReal ∈ Ioo (0 : ℝ) 1 := by
  have hfirstMem : first ∈ quittingPositiveHazardSupport root := by rw [hsupport]; simp
  have hsecondMem : second ∈ quittingPositiveHazardSupport root := by rw [hsupport]; simp
  have hfirst : 0 < (root first true).toReal := (Finset.mem_filter.mp hfirstMem).2
  have hsecond : 0 < (root second true).toReal := (Finset.mem_filter.mp hsecondMem).2
  have hroot := quittingRoot_eq_pairedRoot_of_support_eq_pair root hne hsupport
  have hpairNash : IsεQuittingRootNash reward tail 0
      (PairedCycle.root first second (root first) (root second)) := by rwa [← hroot]
  have hswapNash : IsεQuittingRootNash reward tail 0
      (PairedCycle.root second first (root second) (root first)) := by
    rwa [← PairedCycle.root_swap hne (root first) (root second)]
  have hswapNoPure : ¬IsεQuittingRootNash reward tail 0
      (PairedCycle.root second first (PMF.pure true) (PMF.pure true)) := by
    rwa [← PairedCycle.root_swap hne (PMF.pure true) (PMF.pure true)]
  exact ⟨⟨hfirst, pairedNash_first_probability_lt_one reward tail hne _ _
    hsecond hjoiningSecond hpairNash hnopure⟩,
    ⟨hsecond, pairedNash_first_probability_lt_one reward tail hne.symm _ _
      hfirst hjoiningFirst hswapNash hswapNoPure⟩⟩

private theorem pairedNash_second_probability_eq_ratio
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (tail : Payoff ι)
    {first second : ι} (hne : first ≠ second) (firstLaw secondLaw : PMF Bool)
    (hfirst : (firstLaw true).toReal ∈ Ioo (0 : ℝ) 1)
    (hnash : IsεQuittingRootNash reward tail 0
      (PairedCycle.root first second firstLaw secondLaw))
    (hjoining : quittingPairJoiningGap reward first second ≠ 0) :
    (secondLaw true).toReal =
      (tail first - reward (quittingSingletonTerminal first) first) /
        quittingPairHazardDenominator reward tail first second := by
  have hbalance := quittingPairJoiningGap_eq_survival_mul_denominator_of_pairNash
    reward tail hne firstLaw secondLaw hfirst hnash
  have hden : quittingPairHazardDenominator reward tail first second ≠ 0 := by
    intro hzero
    rw [hzero, mul_zero] at hbalance
    exact hjoining hbalance
  have hgap := quittingRootEndpointDifference_eq_zero_of_both_probabilities_pos
    reward tail (PairedCycle.root first second firstLaw secondLaw) first
    ((isZeroQuittingRootEndpointNash_iff_isZeroQuittingRootNash reward tail _).mpr hnash)
    (by rw [PairedCycle.root_first hne, Math.PMFProduct.pmfBool_false_toReal]
        exact sub_pos.mpr hfirst.2)
    (by simpa only [PairedCycle.root_first hne] using hfirst.1)
  unfold quittingRootEndpointDifference at hgap
  rw [PairedCycle.rootQuit_first reward tail hne,
    PairedCycle.rootContinue_first reward tail hne] at hgap
  unfold Math.PairedAffine.activeValue at hgap
  apply (eq_div_iff hden).mpr
  dsimp only [quittingPairHazardDenominator, quittingPairJoiningGap]
  nlinarith [hgap]

/-- At a fixed deficit source there is at most one bad exact root. This
classifies the actual complete root, not just its active-face coordinates. -/
theorem exactRoot_bad_successor_unique_of_signed_pair_core
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (tail : Payoff ι)
    {first second : ι} (hne : first ≠ second)
    (hcore : quittingPremiumCore reward = {first, second})
    (hbelow : ∃ player, tail player < reward (quittingSingletonTerminal player) player)
    (hjoiningFirst : quittingPairJoiningGap reward first second ≠ 0)
    (hjoiningSecond : quittingPairJoiningGap reward second first ≠ 0)
    (hnopure : ¬IsεQuittingRootNash reward tail 0
      (PairedCycle.root first second (PMF.pure true) (PMF.pure true)))
    (root other : ι → PMF Bool)
    (hnash : IsεQuittingRootNash reward tail 0 root)
    (hotherNash : IsεQuittingRootNash reward tail 0 other)
    (hbad : ∀ player, reward (quittingSingletonTerminal player) player <
      quittingRootSuccessorPayoff reward tail root player)
    (hotherBad : ∀ player, reward (quittingSingletonTerminal player) player <
      quittingRootSuccessorPayoff reward tail other player) : root = other := by
  have formula : ∀ candidate : ι → PMF Bool,
      IsεQuittingRootNash reward tail 0 candidate →
      (∀ player, reward (quittingSingletonTerminal player) player <
        quittingRootSuccessorPayoff reward tail candidate player) →
      (candidate first true).toReal =
        (tail second - reward (quittingSingletonTerminal second) second) /
          quittingPairHazardDenominator reward tail second first ∧
      (candidate second true).toReal =
        (tail first - reward (quittingSingletonTerminal first) first) /
          quittingPairHazardDenominator reward tail first second ∧
      ∀ player, player ≠ first → player ≠ second → candidate player = PMF.pure false := by
    intro candidate hcandidateNash hcandidateBad
    have hsupport := exactRoot_bad_successor_support_eq_pair_core reward tail first second
      hcore candidate hcandidateNash hbelow hcandidateBad
    obtain ⟨hfirst, hsecond⟩ := exactRoot_bad_successor_pair_probabilities_interior
      reward tail hne candidate hsupport hcandidateNash hjoiningFirst hjoiningSecond hnopure
    have hroot := quittingRoot_eq_pairedRoot_of_support_eq_pair candidate hne hsupport
    have hpairNash : IsεQuittingRootNash reward tail 0
        (PairedCycle.root first second (candidate first) (candidate second)) := by
      rwa [← hroot]
    have hswapNash : IsεQuittingRootNash reward tail 0
        (PairedCycle.root second first (candidate second) (candidate first)) := by
      rwa [← PairedCycle.root_swap hne (candidate first) (candidate second)]
    refine ⟨pairedNash_second_probability_eq_ratio reward tail hne.symm _ _ hsecond
      hswapNash hjoiningSecond,
      pairedNash_second_probability_eq_ratio reward tail hne _ _ hfirst
        hpairNash hjoiningFirst, ?_⟩
    intro player hfirstNe hsecondNe
    exact quittingRoot_eq_pure_false_of_not_mem_positiveHazardSupport candidate
      (by simp [hsupport, hfirstNe, hsecondNe])
  obtain ⟨hfirst, hsecond, hinactive⟩ := formula root hnash hbad
  obtain ⟨hotherFirst, hotherSecond, hotherInactive⟩ := formula other hotherNash hotherBad
  funext player
  by_cases hplayerFirst : player = first
  · subst player
    apply Math.PMFProduct.bernoulliBoolEquiv.symm.injective
    apply Subtype.ext
    exact hfirst.trans hotherFirst.symm
  · by_cases hplayerSecond : player = second
    · subst player
      apply Math.PMFProduct.bernoulliBoolEquiv.symm.injective
      apply Subtype.ext
      exact hsecond.trans hotherSecond.symm
    · exact (hinactive player hplayerFirst hplayerSecond).trans
        (hotherInactive player hplayerFirst hplayerSecond).symm

/-- Raw signed core data and actual bad-root comparisons supply the full
ambient nonsingular negative Jacobian internally. No local index, selector,
or continuation floor is an input. -/
theorem signed_pair_core_badRoot_hasFDerivAt_and_negative_det
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (tail : Payoff ι)
    {first second : ι} (hne : first ≠ second)
    (hcore : quittingPremiumCore reward = {first, second})
    (hbelow : ∃ player, tail player < reward (quittingSingletonTerminal player) player)
    (hjoining : 0 < quittingPairJoiningGap reward first second *
      quittingPairJoiningGap reward second first)
    (hnopure : ¬IsεQuittingRootNash reward tail 0
      (PairedCycle.root first second (PMF.pure true) (PMF.pure true)))
    (root : ι → PMF Bool) (hnash : IsεQuittingRootNash reward tail 0 root)
    (hbad : ∀ player, reward (quittingSingletonTerminal player) player <
      quittingRootSuccessorPayoff reward tail root player) :
    HasFDerivAt (fun hazard => hazard - quittingFullClippedEndpointMap reward tail hazard)
      (quittingFullClippedDisplacementDerivative reward tail {first, second}
        (hazardOfRoot root)) (hazardOfRoot root) ∧
    (LinearMap.toMatrix'
      (quittingFullClippedDisplacementDerivative reward tail {first, second}
        (hazardOfRoot root)).toLinearMap).det < 0 ∧
    (LinearMap.toMatrix'
      (quittingFullClippedDisplacementDerivative reward tail {first, second}
        (hazardOfRoot root)).toLinearMap).det ≠ 0 := by
  have hjoiningFirst : quittingPairJoiningGap reward first second ≠ 0 := by
    intro hzero
    rw [hzero, zero_mul] at hjoining
    exact lt_irrefl _ hjoining
  have hjoiningSecond : quittingPairJoiningGap reward second first ≠ 0 := by
    intro hzero
    rw [hzero, mul_zero] at hjoining
    exact lt_irrefl _ hjoining
  have hsupport := exactRoot_bad_successor_support_eq_pair_core reward tail first second
    hcore root hnash hbelow hbad
  obtain ⟨hfirst, hsecond⟩ := exactRoot_bad_successor_pair_probabilities_interior
    reward tail hne root hsupport hnash hjoiningFirst hjoiningSecond hnopure
  have hroot := quittingRoot_eq_pairedRoot_of_support_eq_pair root hne hsupport
  have hpairNash : IsεQuittingRootNash reward tail 0
      (PairedCycle.root first second (root first) (root second)) := by rwa [← hroot]
  have hnegative : ∀ player, player ≠ first → player ≠ second →
      quittingRootEndpointDifference reward tail
        (PairedCycle.root first second (root first) (root second)) player < 0 := by
    intro player hfirstNe hsecondNe
    rw [← hroot]
    exact exactRoot_bad_successor_inactive_gap_neg_of_pair_core reward tail first second
      hcore root hsupport hbad player hfirstNe hsecondNe
  simpa only [← hroot] using
    pairNash_hasFDerivAt_and_negative_det_fullClippedDisplacement reward tail hne
      (root first) (root second) hfirst hsecond hpairNash hnegative hjoining

end GameTheory
