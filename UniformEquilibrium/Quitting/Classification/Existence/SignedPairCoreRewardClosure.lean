import UniformEquilibrium.Quitting.Classification.Existence.SignedPairCoreUniformPayoff
import UniformEquilibrium.Quitting.Classification.SignedPairPassivePerturbation
import UniformEquilibrium.Quitting.Terminal.TerminalExploitabilityRewardRobustness

/-! # The weak same-sign boundary of the signed pair criterion

Only two passive singleton entries are perturbed. Reward closure selects one
fixed target for the original game; no weak analytic exclusion is asserted.
-/

noncomputable section

namespace GameTheory

private theorem exists_small_shifts_positive_product
    (first second delta : ℝ) (hproduct : 0 ≤ first * second) (hdelta : 0 < delta) :
    ∃ firstShift secondShift : ℝ, |firstShift| ≤ delta ∧ |secondShift| ≤ delta ∧
      0 < (first + firstShift) * (second + secondShift) := by
  have hpositiveBound : |delta| ≤ delta := le_of_eq (abs_of_pos hdelta)
  have hnegativeBound : |-delta| ≤ delta := by rwa [abs_neg]
  have hzeroBound : |(0 : ℝ)| ≤ delta := by simpa only [abs_zero] using hdelta.le
  by_cases hfirst : first = 0
  · subst first
    by_cases hsecond : second = 0
    · subst second
      exact ⟨delta, delta, hpositiveBound, hpositiveBound,
        by simpa only [zero_add] using mul_pos hdelta hdelta⟩
    · by_cases hpositive : 0 < second
      · exact ⟨delta, 0, hpositiveBound, hzeroBound,
          by simpa only [zero_add, add_zero] using mul_pos hdelta hpositive⟩
      · have hnegative : second < 0 := lt_of_le_of_ne (le_of_not_gt hpositive) hsecond
        exact ⟨-delta, 0, hnegativeBound, hzeroBound,
          by simpa only [zero_add, add_zero] using
            (mul_pos_of_neg_of_neg (neg_neg_of_pos hdelta) hnegative)⟩
  · by_cases hsecond : second = 0
    · subst second
      by_cases hpositive : 0 < first
      · exact ⟨0, delta, hzeroBound, hpositiveBound,
          by simpa only [zero_add, add_zero] using mul_pos hpositive hdelta⟩
      · have hnegative : first < 0 := lt_of_le_of_ne (le_of_not_gt hpositive) hfirst
        exact ⟨0, -delta, hzeroBound, hnegativeBound,
          by simpa only [zero_add, add_zero] using
            (mul_pos_of_neg_of_neg hnegative (neg_neg_of_pos hdelta))⟩
    · exact ⟨0, 0, hzeroBound, hzeroBound,
        by simpa only [add_zero] using
          lt_of_le_of_ne hproduct (Ne.symm (mul_ne_zero hfirst hsecond))⟩

theorem exists_uniformEquilibriumPayoff_of_signed_pair_core_weakSameSign
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (hsingleton : ∀ player, 0 ≤ reward (quittingSingletonTerminal player) player)
    {first second : Fin 4} (hne : first ≠ second)
    (hcore : quittingPremiumCore reward = {first, second})
    (hjoining : 0 ≤ quittingPairJoiningGap reward first second *
      quittingPairJoiningGap reward second first) :
    ∃ payoff : Payoff (Fin 4),
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff := by
  apply exists_uniformEquilibriumPayoff_of_arbitrarily_close_reward_tables reward
  intro delta hdelta
  obtain ⟨firstShift, secondShift, hfirst, hsecond, hpositive⟩ :=
    exists_small_shifts_positive_product (quittingPairJoiningGap reward first second)
      (quittingPairJoiningGap reward second first) delta hjoining hdelta
  let nearby := signedPairPassivePerturbation reward first second firstShift secondShift
  refine ⟨nearby, ?_, ?_⟩
  · exact abs_signedPairPassivePerturbation_sub_le reward first second firstShift secondShift
      delta hfirst hsecond
  · refine exists_uniformEquilibriumPayoff_of_signed_pair_core_strictSameSign nearby
      ?_ hne (by
        change quittingPremiumCore
          (signedPairPassivePerturbation reward first second firstShift secondShift) =
            {first, second}
        rw [signedPairPassivePerturbation_core reward hne, hcore]) ?_
    · intro player
      change 0 ≤ signedPairPassivePerturbation reward first second firstShift secondShift
        (quittingSingletonTerminal player) player
      rw [signedPairPassivePerturbation_singleton reward hne]
      exact hsingleton player
    · obtain ⟨hgapFirst, hgapSecond⟩ :=
        signedPairPassivePerturbation_joiningGap reward hne firstShift secondShift
      change 0 < quittingPairJoiningGap
        (signedPairPassivePerturbation reward first second firstShift secondShift)
          first second * quittingPairJoiningGap
        (signedPairPassivePerturbation reward first second firstShift secondShift) second first
      rw [hgapFirst, hgapSecond]
      exact hpositive

theorem exists_uniformEquilibriumPayoff_of_empty_or_signed_pair_core_weakSameSign
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (hsingleton : ∀ player, 0 ≤ reward (quittingSingletonTerminal player) player)
    (hcore : quittingPremiumCore reward = ∅ ∨
      ∃ first second : Fin 4, first ≠ second ∧
        quittingPremiumCore reward = {first, second} ∧
        0 ≤ quittingPairJoiningGap reward first second *
          quittingPairJoiningGap reward second first) :
    ∃ payoff : Payoff (Fin 4),
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff := by
  rcases hcore with hempty | ⟨first, second, hne, hpair, hjoining⟩
  · exact exists_uniformEquilibriumPayoff_of_empty_quittingPremiumCore reward hsingleton hempty
  · exact exists_uniformEquilibriumPayoff_of_signed_pair_core_weakSameSign
      reward hsingleton hne hpair hjoining

end GameTheory
