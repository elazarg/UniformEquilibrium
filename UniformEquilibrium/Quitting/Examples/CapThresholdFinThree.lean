import UniformEquilibrium.Quitting.Examples.CapThresholdRegressionCommon

/-! # Signed thirty-date regression: total debt rises before the first hit -/

namespace GameTheory.CapThresholdFinThree

open CapThresholdRegression QuittingSureSetOwnerRepair

def singleton : Fin 3 → ℚ := ![-1, 0, 0]

def reward : RationalQuittingReward 3 := fun terminal who =>
  if terminal.1 = {1, 2} then 1
  else if terminal.1 = {0, 1, 2} then (![2, -1, -1] : Fin 3 → ℚ) who
  else if who ∈ terminal.1 then singleton who else -1

def source : List (RationalQuittingRoot 3) := [pureRoot {1, 2}]

def word (steps : ℕ) : List (RationalQuittingRoot 3) :=
  List.replicate steps (rationalQuittingSoloRoot 0 (3 / 160)) ++ source

theorem reward_bound : ∀ terminal who, |reward terminal who| ≤ 2 := by decide

theorem source_pair : rationalQuittingFiniteWordSemanticPair reward source =
    (![1, 1, 1], ![2, 1, 1]) := by
  have hactual :
      quittingTerminalSemanticPair (rationalQuittingRewardToReal reward)
          (profile reward source) =
        RationalQuittingSemanticPair.toReal
          ((![1, 1, 1], ![2, 1, 1]) : RationalQuittingSemanticPair 3) := by
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
    (rationalQuittingFiniteWordSemanticPair reward source).2 0 -
      reward (quittingSingletonTerminal 0) 0 = 3 ∧
    rationalFiniteSourceCapThresholdScale reward source 0 = 3 ∧
    rationalCapThresholdSoloHazard 2 3 = 3 / 160 ∧
    reward (quittingSingletonTerminal 1) 1 -
      reward (quittingSingletonTerminal 0) 1 = 1 := by
  simp only [rationalFiniteSourceDebt, rationalFiniteSourceCapThresholdScale, source_pair]
  norm_num +decide [rationalQuittingSemanticDebtSum, rationalCapThresholdSoloHazard,
    reward, singleton, quittingSingletonTerminal, Fin.sum_univ_succ]

noncomputable section

abbrev realReward := rationalQuittingRewardToReal reward

theorem actual_source_pair :
    quittingTerminalSemanticPair realReward (profile reward source) =
      RationalQuittingSemanticPair.toReal
        ((![1, 1, 1], ![2, 1, 1]) : RationalQuittingSemanticPair 3) :=
  actual_pair reward source _ source_pair

private theorem real_reward_bound : ∀ terminal who, |realReward terminal who| ≤ 2 := by
  intro terminal who
  change |(reward terminal who : ℝ)| ≤ 2
  exact_mod_cast reward_bound terminal who

private theorem before_scalar (k : ℕ) (hk : k < 30) :
    (3 / 20 : ℝ) < -1 + 2 * (157 / 160 : ℝ) ^ k := by
  have hmono := pow_le_pow_of_le_one
    (by norm_num : (0 : ℝ) ≤ 157 / 160) (by norm_num : (157 / 160 : ℝ) ≤ 1)
    (show k ≤ 29 by omega)
  have hlast : (3 / 20 : ℝ) < -1 + 2 * (157 / 160 : ℝ) ^ 29 := by norm_num
  linarith

theorem actual_pair_through_hit (k : ℕ) (hk : k ≤ 30) :
    quittingTerminalSemanticPair realReward (profile reward (word k)) =
      (fun _ => -1 + 2 * (157 / 160 : ℝ) ^ k,
       fun who => if who = 0 then 2 else -1 + 2 * (157 / 160 : ℝ) ^ k) := by
  have hmodel : ∀ m < 30, ∀ who : Fin 3,
      4 * 2 * (3 / 160 : ℝ) <
        (if who = 0 then
          (quittingTerminalSemanticPair realReward (profile reward source)).2 0 else
          realReward (quittingSingletonTerminal 0) who + (1 - (3 / 160 : ℝ)) ^ m *
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
    (by norm_num : (0 : ℝ) < 3 / 160) (by norm_num : (3 / 160 : ℝ) < 1) 30 hmodel k hk
  rw [word, actual_solo_word_pair reward source 0 (3 / 160) (by norm_num)]
  norm_num only [Rat.cast_div, Rat.cast_ofNat]
  rw [hledger, actual_source_pair]
  apply Prod.ext <;> funext who <;> fin_cases who <;>
    norm_num +decide [RationalQuittingSemanticPair.toReal, realReward,
      rationalQuittingRewardToReal, reward, singleton, quittingSingletonTerminal] <;> ring_nf

theorem first_hit :
    (∀ k < 30, ∀ who : Fin 3, (3 / 20 : ℝ) <
      (quittingTerminalSemanticPair realReward (profile reward (word k))).2 who -
        realReward (quittingSingletonTerminal who) who) ∧
    (∀ who : Fin 3, who ≠ 0 →
      (3 / 40 : ℝ) <
        (quittingTerminalSemanticPair realReward (profile reward (word 30))).2 who ∧
      (quittingTerminalSemanticPair realReward (profile reward (word 30))).2 who ≤ 3 / 20) := by
  constructor
  · intro k hk who
    rw [actual_pair_through_hit k hk.le]
    have hbefore := before_scalar k hk
    fin_cases who <;>
      norm_num +decide [realReward, rationalQuittingRewardToReal, reward, singleton,
        quittingSingletonTerminal] <;> linarith
  · intro who hwho
    rw [actual_pair_through_hit 30 le_rfl]
    simp only [ite_eq_right hwho]
    norm_num

theorem debt_through_hit (k : ℕ) (hk : k ≤ 30) :
    quittingTerminalSemanticDebtSum
      (quittingTerminalSemanticPair realReward (profile reward (word k))) =
      3 - 2 * (157 / 160 : ℝ) ^ k := by
  rw [actual_pair_through_hit k hk]
  norm_num [quittingTerminalSemanticDebtSum, quittingTerminalSemanticDebt,
    Fin.sum_univ_succ]
  ring_nf

theorem debt_strictly_above_initial (k : ℕ) (hk0 : 0 < k) (hk : k ≤ 30) :
    1 < quittingTerminalSemanticDebtSum
      (quittingTerminalSemanticPair realReward (profile reward (word k))) := by
  rw [debt_through_hit k hk]
  have hpow := pow_lt_one₀ (by norm_num : (0 : ℝ) ≤ 157 / 160)
    (by norm_num : (157 / 160 : ℝ) < 1) hk0.ne'
  linarith

/-- At every nonempty solo prefix player one can Quit immediately for exactly zero,
so its complete cap cannot follow a negative affine extrapolation. -/
theorem actual_outsider_cap_nonnegative (k : ℕ) :
    0 ≤ (quittingTerminalSemanticPair realReward (profile reward (word (k + 1)))).2 1 := by
  rw [word, actual_solo_word_pair reward source 0 (3 / 160) (by norm_num)]
  norm_num only [Rat.cast_div, Rat.cast_ofNat]
  rw [quittingSoloSemanticIterate_succ]
  change 0 ≤ max _ _
  have hquit (tail : Payoff (Fin 3)) :
      quittingRootQuitPayoff realReward tail
        (quittingSoloStationaryRoot 0
          (quittingHazardCoin (3 / 160) (by norm_num) (by norm_num))) 1 = 0 := by
    rw [quittingRootQuitPayoff_soloStationaryRoot_other realReward (by decide)]
    norm_num +decide [quittingSoloReward, quittingSingletonCollisionReward, realReward,
      rationalQuittingRewardToReal, reward, singleton, quittingSingletonTerminal]
  rw [hquit]
  exact le_max_left _ _

/-- A literal eventual failure of extending the affine cap ledger past its domain. -/
theorem affine_cap_eventually_false (k : ℕ) (hk : 100 ≤ k) :
    -1 + 2 * (157 / 160 : ℝ) ^ k < 0 ∧
    -1 + 2 * (157 / 160 : ℝ) ^ k <
      (quittingTerminalSemanticPair realReward (profile reward (word k))).2 1 := by
  have hmono := pow_le_pow_of_le_one
    (by norm_num : (0 : ℝ) ≤ 157 / 160) (by norm_num : (157 / 160 : ℝ) ≤ 1) hk
  have hnegative : -1 + 2 * (157 / 160 : ℝ) ^ 100 < 0 := by norm_num
  have hpredicted : -1 + 2 * (157 / 160 : ℝ) ^ k < 0 := by linarith
  refine ⟨hpredicted, hpredicted.trans_le ?_⟩
  cases k with
  | zero => omega
  | succ k => exact actual_outsider_cap_nonnegative k

end

end GameTheory.CapThresholdFinThree
