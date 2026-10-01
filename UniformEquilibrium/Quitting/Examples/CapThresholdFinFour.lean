import UniformEquilibrium.Quitting.Examples.CapThresholdRegressionCommon

/-! # Exact fifty-nine-date first cap hit at the literal four-player table -/

namespace GameTheory.CapThresholdFinFour

open CapThresholdRegression QuittingSureSetOwnerRepair

def singleton : Fin 4 → ℚ := ![1, 0, 0, 0]

def reward : RationalQuittingReward 4 := fun terminal who =>
  if terminal.1 = {1, 2} then 1
  else if terminal.1 = {0, 1, 2} then (![2, -1, -1, -1] : Fin 4 → ℚ) who
  else if who ∈ terminal.1 then singleton who else -1

def source : List (RationalQuittingRoot 4) := [pureRoot {1, 2}]

def word (steps : ℕ) : List (RationalQuittingRoot 4) :=
  List.replicate steps (rationalQuittingSoloRoot 0 (1 / 96)) ++ source

theorem reward_bound : ∀ terminal who, |reward terminal who| ≤ 2 := by decide

theorem source_pair : rationalQuittingFiniteWordSemanticPair reward source =
    (![1, 1, 1, 1], ![2, 1, 1, 1]) := by
  have hactual :
      quittingTerminalSemanticPair (rationalQuittingRewardToReal reward)
          (profile reward source) =
        RationalQuittingSemanticPair.toReal
          ((![1, 1, 1, 1], ![2, 1, 1, 1]) : RationalQuittingSemanticPair 4) := by
    unfold profile source
    rw [List.map_cons, List.map_nil, pureRoot_toPMF, quittingLiteralRootStackProfile_cons]
    rw [quittingTerminalSemanticPair_pureSetRootThenContinuation_eq_of_two_le_card
      _ {1, 2} (by decide)]
    apply Prod.ext <;> funext who <;> fin_cases who <;>
      norm_num +decide [RationalQuittingSemanticPair.toReal, quittingSetReward,
        rationalQuittingRewardToReal, reward, singleton]
  apply RationalQuittingSemanticPair.toReal_injective
  exact (quittingTerminalSemanticPair_rationalFiniteWord_eq_cast reward source).symm.trans hactual

theorem source_parameters :
    rationalFiniteSourceDebt reward source = 1 ∧
    rationalFiniteSourceCapThresholdScale reward source 0 = 1 ∧
    rationalCapThresholdSoloHazard 2 1 = 1 / 96 ∧
    (3 * (1 : ℚ) ^ 2 / (32 * 2 + 6 * 1)) = 3 / 70 := by
  simp only [rationalFiniteSourceDebt, rationalFiniteSourceCapThresholdScale, source_pair]
  norm_num +decide [rationalQuittingSemanticDebtSum, rationalCapThresholdSoloHazard,
    reward, singleton, quittingSingletonTerminal, Fin.sum_univ_succ]

noncomputable section

abbrev realReward := rationalQuittingRewardToReal reward

theorem actual_source_pair :
    quittingTerminalSemanticPair realReward (profile reward source) =
      RationalQuittingSemanticPair.toReal
        ((![1, 1, 1, 1], ![2, 1, 1, 1]) : RationalQuittingSemanticPair 4) :=
  actual_pair reward source _ source_pair

private theorem real_reward_bound : ∀ terminal who, |realReward terminal who| ≤ 2 := by
  intro terminal who
  change |(reward terminal who : ℝ)| ≤ 2
  exact_mod_cast reward_bound terminal who

private theorem before_scalar (k : ℕ) (hk : k < 59) :
    (1 / 12 : ℝ) < -1 + 2 * (95 / 96 : ℝ) ^ k := by
  have hmono := pow_le_pow_of_le_one
    (by norm_num : (0 : ℝ) ≤ 95 / 96) (by norm_num : (95 / 96 : ℝ) ≤ 1)
    (show k ≤ 58 by omega)
  have hlast : (1 / 12 : ℝ) < -1 + 2 * (95 / 96 : ℝ) ^ 58 := by norm_num
  linarith

/-- Every displayed pair is the actual prescribed payoff and complete behavioral cap
of exactly these solo rows followed by the original pure {1,2} row and Never. -/
theorem actual_pair_through_hit (k : ℕ) (hk : k ≤ 59) :
    quittingTerminalSemanticPair realReward (profile reward (word k)) =
      (fun who => if who = 0 then 1 else -1 + 2 * (95 / 96 : ℝ) ^ k,
       fun who => if who = 0 then 2 else -1 + 2 * (95 / 96 : ℝ) ^ k) := by
  have hmodel : ∀ m < 59, ∀ who : Fin 4,
      4 * 2 * (1 / 96 : ℝ) <
        (if who = 0 then
          (quittingTerminalSemanticPair realReward (profile reward source)).2 0 else
          realReward (quittingSingletonTerminal 0) who + (1 - (1 / 96 : ℝ)) ^ m *
            ((quittingTerminalSemanticPair realReward (profile reward source)).2 who -
              realReward (quittingSingletonTerminal 0) who)) -
          realReward (quittingSingletonTerminal who) who := by
    intro m hm who
    rw [actual_source_pair]
    have hbefore := before_scalar m hm
    fin_cases who <;>
      norm_num +decide [RationalQuittingSemanticPair.toReal, realReward,
        rationalQuittingRewardToReal, reward, singleton, quittingSingletonTerminal] <;>
      linarith
  have hledger := solo_affine_up_to realReward
    (quittingTerminalSemanticPair realReward (profile reward source)) 0
    real_reward_bound (subset_closure (Set.mem_range_self (profile reward source)))
    (by norm_num : (0 : ℝ) < 1 / 96) (by norm_num : (1 / 96 : ℝ) < 1) 59 hmodel k hk
  rw [word, actual_solo_word_pair reward source 0 (1 / 96) (by norm_num)]
  norm_num only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
  rw [hledger, actual_source_pair]
  apply Prod.ext <;> funext who <;> fin_cases who <;>
    norm_num +decide [RationalQuittingSemanticPair.toReal, realReward,
      rationalQuittingRewardToReal, reward, singleton, quittingSingletonTerminal] <;> ring_nf

/-- This is a first hit, not just an upper bound on some crossing date. -/
theorem first_hit :
    (∀ k < 59, ∀ who : Fin 4, (1 / 12 : ℝ) <
      (quittingTerminalSemanticPair realReward (profile reward (word k))).2 who -
        realReward (quittingSingletonTerminal who) who) ∧
    (∀ who : Fin 4, who ≠ 0 →
      (1 / 24 : ℝ) <
        (quittingTerminalSemanticPair realReward (profile reward (word 59))).2 who ∧
      (quittingTerminalSemanticPair realReward (profile reward (word 59))).2 who ≤ 1 / 12) := by
  constructor
  · intro k hk who
    rw [actual_pair_through_hit k hk.le]
    have hbefore := before_scalar k hk
    fin_cases who <;>
      norm_num +decide [realReward, rationalQuittingRewardToReal, reward, singleton,
        quittingSingletonTerminal] <;> linarith
  · intro who hwho
    rw [actual_pair_through_hit 59 le_rfl]
    simp only [ite_eq_right hwho]
    norm_num

theorem debt_through_hit (k : ℕ) (hk : k ≤ 59) :
    quittingTerminalSemanticDebtSum
      (quittingTerminalSemanticPair realReward (profile reward (word k))) = 1 := by
  rw [actual_pair_through_hit k hk]
  norm_num [quittingTerminalSemanticDebtSum, quittingTerminalSemanticDebt,
    Fin.sum_univ_succ]

private theorem allQuit_quit (tail : Payoff (Fin 4)) (who : Fin 4) :
    quittingRootQuitPayoff realReward tail (quittingPureSetRoot Finset.univ) who =
      if who = 0 then 1 else 0 := by
  rw [quittingRootQuitPayoff_pureSetRoot_eq_insert]
  fin_cases who <;> norm_num +decide [quittingSetReward, realReward,
    rationalQuittingRewardToReal, reward, singleton,
    show (Finset.univ : Finset (Fin 4)) = {0, 1, 2, 3} by decide]

private theorem allQuit_continue (tail : Payoff (Fin 4)) (who : Fin 4) :
    quittingRootContinuePayoff realReward tail (quittingPureSetRoot Finset.univ) who = -1 := by
  rw [quittingRootContinuePayoff_pureSetRoot_eq_erase_of_nonempty]
  · fin_cases who <;> norm_num +decide [quittingSetReward, realReward,
      rationalQuittingRewardToReal, reward, singleton,
      show (Finset.univ : Finset (Fin 4)) = {0, 1, 2, 3} by decide]
  · fin_cases who <;> decide

/-- Stronger than the required B-1/2 instance: the all-Quit root is exact for any tail. -/
theorem allQuit_exact (tail : Payoff (Fin 4)) :
    IsεQuittingRootNash realReward tail 0 (pureRoot Finset.univ).toPMF := by
  rw [pureRoot_toPMF]
  apply (isZeroQuittingRootEndpointNash_iff_isZeroQuittingRootNash _ _ _).mp
  intro who
  rw [quittingRootEndpointDifference, allQuit_quit, allQuit_continue]
  fin_cases who <;> norm_num [quittingPureSetRoot, quittingSetAction]

private theorem allQuit_prefix (pair : QuittingTerminalSemanticPair (Fin 4)) :
    quittingTerminalSemanticPrefix realReward (pureRoot Finset.univ).toPMF pair =
      (fun who => if who = 0 then 1 else 0,
       fun who => if who = 0 then 1 else 0) := by
  rw [pureRoot_toPMF]
  apply Prod.ext
  · funext who
    change quittingRootSuccessorPayoff realReward pair.1
      (quittingPureSetRoot Finset.univ) who = _
    rw [quittingRootSuccessorPayoff_eq_endpointMix, allQuit_quit, allQuit_continue]
    simp [quittingPureSetRoot, quittingSetAction]
  · funext who
    change max _ _ = _
    rw [allQuit_quit, allQuit_continue]
    fin_cases who <;> norm_num

theorem auxiliary_at_crossing_exact :
    IsεQuittingRootNash realReward
      (fun who =>
        (quittingTerminalSemanticPair realReward (profile reward (word 59))).2 who - 1 / 2)
      0 (pureRoot Finset.univ).toPMF := allQuit_exact _

/-- The actual auxiliary prefix has zero full debt; the old fifty-nine-row tail
is preserved literally even though the new root absorbs surely. -/
theorem actual_exit_pair :
    quittingTerminalSemanticPair realReward
      (profile reward (pureRoot Finset.univ :: word 59)) =
      (fun who => if who = 0 then 1 else 0,
       fun who => if who = 0 then 1 else 0) := by
  unfold profile
  rw [List.map_cons, quittingLiteralRootStackProfile_cons,
    quittingTerminalSemanticPair_rootThenContinuation, allQuit_prefix]

theorem actual_exit_debt_zero :
    quittingTerminalSemanticDebtSum
      (quittingTerminalSemanticPair realReward
        (profile reward (pureRoot Finset.univ :: word 59))) = 0 := by
  rw [actual_exit_pair]
  simp [quittingTerminalSemanticDebtSum, quittingTerminalSemanticDebt]

end

end GameTheory.CapThresholdFinFour
