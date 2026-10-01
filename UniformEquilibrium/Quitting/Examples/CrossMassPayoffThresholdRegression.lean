import UniformEquilibrium.Quitting.Examples.CrossMassDeterminantFixture
import UniformEquilibrium.Quitting.Examples.CapThresholdRegressionCommon
import UniformEquilibrium.Quitting.Paths.ExecutableRationalPayoffDebtThresholdBlock

/-! # The literal first payoff crossing at one hundred fifty-five solo rows

All caps and debts are those of the original two-row source and its literal
solo prefixes. The executable first hit uses payoff/debt, not a cap threshold.
The final exact root retains the entire reached word, including its old tail.
-/

namespace GameTheory.CrossMassPayoffThresholdRegression

open CrossMassDeterminantFixture CapThresholdRegression QuittingSureSetOwnerRepair

def source : List (RationalQuittingRoot 4) :=
  [rationalQuittingSoloRoot 1 (1 / 200), pureRoot {2, 3}]

def word (steps : ℕ) : List (RationalQuittingRoot 4) :=
  List.replicate steps (rationalQuittingSoloRoot 0 (1 / 3360)) ++ source

def finalWord : List (RationalQuittingRoot 4) := exitRoot :: word 155

noncomputable section

private theorem pair_row_pair :
    quittingTerminalSemanticPair realReward (wordProfile [pureRoot {2, 3}]) =
      RationalQuittingSemanticPair.toReal
        ((![1, 1, 1, 1], ![1, 1, 1, 1001 / 1000]) : RationalQuittingSemanticPair 4) := by
  unfold wordProfile
  rw [List.map_cons, List.map_nil, pureRoot_toPMF, quittingLiteralRootStackProfile_cons]
  rw [quittingTerminalSemanticPair_pureSetRootThenContinuation_eq_of_two_le_card
    _ {2, 3} (by decide)]
  apply Prod.ext <;> funext who <;> fin_cases who <;>
    norm_num +decide [RationalQuittingSemanticPair.toReal, quittingSetReward,
      realReward, rationalQuittingRewardToReal, reward]

theorem actual_source_pair :
    quittingTerminalSemanticPair realReward (wordProfile source) =
      RationalQuittingSemanticPair.toReal
        ((![199 / 200, 199 / 200, 1, 1],
          ![11 / 10, 1, 1, 200199 / 200000]) : RationalQuittingSemanticPair 4) := by
  unfold source
  unfold wordProfile
  rw [List.map_cons, quittingLiteralRootStackProfile_cons,
    quittingTerminalSemanticPair_rootThenContinuation]
  change quittingTerminalSemanticPrefix realReward
    (rationalQuittingSoloRoot 1 (1 / 200)).toPMF
    (quittingTerminalSemanticPair realReward (wordProfile [pureRoot {2, 3}])) = _
  rw [pair_row_pair, rationalQuittingSoloRoot_toPMF_eq 1 (by norm_num)]
  apply Prod.ext
  · funext who
    change quittingRootSuccessorPayoff realReward _ _ who = _
    rw [quittingRootSuccessorPayoff_solo]
    fin_cases who <;>
      norm_num +decide [RationalQuittingSemanticPair.toReal, quittingSoloReward,
        realReward, rationalQuittingRewardToReal, reward, quittingSingletonTerminal]
  · funext who
    fin_cases who
    · change max (quittingRootQuitPayoff realReward _ _ 0)
        (quittingRootContinuePayoff realReward _ _ 0) = _
      rw [quittingRootQuitPayoff_soloStationaryRoot_other _ (by decide),
        quittingRootContinuePayoff_soloStationaryRoot_other _ (by decide)]
      norm_num +decide [RationalQuittingSemanticPair.toReal, quittingSoloReward,
        quittingSingletonCollisionReward, realReward, rationalQuittingRewardToReal,
        reward, quittingSingletonTerminal]
    · change max (quittingRootQuitPayoff realReward _ _ 1)
        (quittingRootContinuePayoff realReward _ _ 1) = _
      rw [quittingRootQuitPayoff_soloStationaryRoot_owner,
        quittingRootContinuePayoff_soloStationaryRoot_owner]
      norm_num +decide [RationalQuittingSemanticPair.toReal, quittingSoloReward,
        realReward, rationalQuittingRewardToReal, reward, quittingSingletonTerminal]
    · change max (quittingRootQuitPayoff realReward _ _ 2)
        (quittingRootContinuePayoff realReward _ _ 2) = _
      rw [quittingRootQuitPayoff_soloStationaryRoot_other _ (by decide),
        quittingRootContinuePayoff_soloStationaryRoot_other _ (by decide)]
      norm_num +decide [RationalQuittingSemanticPair.toReal, quittingSoloReward,
        quittingSingletonCollisionReward, realReward, rationalQuittingRewardToReal,
        reward, quittingSingletonTerminal]
    · change max (quittingRootQuitPayoff realReward _ _ 3)
        (quittingRootContinuePayoff realReward _ _ 3) = _
      rw [quittingRootQuitPayoff_soloStationaryRoot_other _ (by decide),
        quittingRootContinuePayoff_soloStationaryRoot_other _ (by decide)]
      norm_num +decide [RationalQuittingSemanticPair.toReal, quittingSoloReward,
        quittingSingletonCollisionReward, realReward, rationalQuittingRewardToReal,
        reward, quittingSingletonTerminal]

theorem source_pair : rationalQuittingFiniteWordSemanticPair reward source =
    (![199 / 200, 199 / 200, 1, 1], ![11 / 10, 1, 1, 200199 / 200000]) := by
  apply RationalQuittingSemanticPair.toReal_injective
  exact (quittingTerminalSemanticPair_rationalFiniteWord_eq_cast reward source).symm.trans
    actual_source_pair

theorem source_debt : rationalFiniteSourceDebt reward source = 22199 / 200000 := by
  rw [rationalFiniteSourceDebt, source_pair]
  norm_num [rationalQuittingSemanticDebtSum, Fin.sum_univ_succ]

/-- Every charged-margin inequality fails on the computed original source. -/
theorem source_concentrated : RationalQuittingConcentratedPayoffSource reward source (1 / 10) := by
  change (1 / 10 : ℚ) ≤ rationalFiniteSourceDebt reward source ∧ _
  rw [source_debt]
  constructor
  · norm_num
  · intro who
    rw [source_pair]
    fin_cases who <;> norm_num +decide [rationalQuittingSemanticDebtSum, Fin.sum_univ_succ,
      reward, quittingSingletonTerminal]

theorem source_owner_payoff :
    (rationalQuittingFiniteWordSemanticPair reward source).1 0 ≤
      reward (quittingSingletonTerminal 0) 0 := by
  rw [source_pair]
  norm_num +decide [reward, quittingSingletonTerminal]

theorem source_failed_column :
    ¬RationalQuittingPositiveSingletonColumnAt reward 0 (1 / 10) := by
  intro hcolumn
  have h := hcolumn 1 (by decide)
  norm_num +decide [reward, quittingSingletonTerminal] at h

theorem working_hazard : rationalPositiveColumnWorkingHazard 21 (1 / 10) = 1 / 3360 := by
  norm_num [rationalPositiveColumnWorkingHazard]

private theorem payoff_before_scalar (k : ℕ) (hk : k < 155) :
    (1 / 20 : ℝ) < -20 + (4199 / 200 : ℝ) * (3359 / 3360 : ℝ) ^ k := by
  have hmono := pow_le_pow_of_le_one
    (by norm_num : (0 : ℝ) ≤ 3359 / 3360)
    (by norm_num : (3359 / 3360 : ℝ) ≤ 1) (show k ≤ 154 by omega)
  have hlast :
      (1 / 20 : ℝ) < -20 + (4199 / 200 : ℝ) * (3359 / 3360 : ℝ) ^ 154 := by
    norm_num
  linarith

/-- The complete cap remains on the affine Continue branch before the PAYOFF hit. -/
theorem actual_pair_through_hit (k : ℕ) (hk : k ≤ 155) :
    quittingTerminalSemanticPair realReward (wordProfile (word k)) =
      (![1 - (3359 / 3360 : ℝ) ^ k / 200,
          -20 + (4199 / 200) * (3359 / 3360 : ℝ) ^ k, 1, 1],
       ![11 / 10, -20 + 21 * (3359 / 3360 : ℝ) ^ k,
          1, 1 + (199 / 200000) * (3359 / 3360 : ℝ) ^ k]) := by
  have hmodel : ∀ m < 155, ∀ who : Fin 4,
      4 * 21 * (1 / 3360 : ℝ) <
        (if who = 0 then
          (quittingTerminalSemanticPair realReward (wordProfile source)).2 0 else
          realReward (quittingSingletonTerminal 0) who + (1 - (1 / 3360 : ℝ)) ^ m *
            ((quittingTerminalSemanticPair realReward (wordProfile source)).2 who -
              realReward (quittingSingletonTerminal 0) who)) -
          realReward (quittingSingletonTerminal who) who := by
    intro m hm who
    rw [actual_source_pair]
    have hbefore := payoff_before_scalar m hm
    have hpower : 0 ≤ (3359 / 3360 : ℝ) ^ m := pow_nonneg (by norm_num) _
    fin_cases who <;>
      norm_num +decide [RationalQuittingSemanticPair.toReal, realReward,
        rationalQuittingRewardToReal, reward, quittingSingletonTerminal] <;> linarith
  have hledger := solo_affine_up_to realReward
    (quittingTerminalSemanticPair realReward (wordProfile source)) 0
    real_reward_bound (subset_closure (Set.mem_range_self (wordProfile source)))
    (by norm_num : (0 : ℝ) < 1 / 3360)
    (by norm_num : (1 / 3360 : ℝ) < 1) 155 hmodel k hk
  have hword := actual_solo_word_pair reward source 0 (1 / 3360) (by norm_num) k
  have hwordReal :
      quittingTerminalSemanticPair realReward (wordProfile (word k)) =
        quittingSoloSemanticIterate realReward 0
          (quittingHazardCoin (1 / 3360) (by norm_num) (by norm_num))
          (quittingTerminalSemanticPair realReward (wordProfile source)) k := by
    simpa only [word, realReward, wordProfile, profile,
      Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] using hword
  rw [hwordReal]
  rw [hledger, actual_source_pair]
  apply Prod.ext <;> funext who <;> fin_cases who <;>
    norm_num +decide [RationalQuittingSemanticPair.toReal, realReward,
      rationalQuittingRewardToReal, reward, quittingSingletonTerminal] <;> ring

theorem debt_through_hit (k : ℕ) (hk : k ≤ 155) :
    quittingTerminalSemanticDebtSum
      (quittingTerminalSemanticPair realReward (wordProfile (word k))) =
        1 / 10 + (2199 / 200000 : ℝ) * (3359 / 3360 : ℝ) ^ k := by
  rw [actual_pair_through_hit k hk]
  norm_num [quittingTerminalSemanticDebtSum, quittingTerminalSemanticDebt, Fin.sum_univ_succ]
  ring

/-- Both disjuncts of the stopping test are excluded before 155. -/
theorem first_payoff_hit :
    (∀ k < 155,
      (1 / 10 : ℝ) ≤ quittingTerminalSemanticDebtSum
        (quittingTerminalSemanticPair realReward (wordProfile (word k))) ∧
      ∀ who : Fin 4, who ≠ 0 →
        realReward (quittingSingletonTerminal who) who + 1 / 20 <
          quittingTerminalPayoff realReward (wordProfile (word k)) who) ∧
    quittingTerminalPayoff realReward (wordProfile (word 155)) 1 ≤ 1 / 20 := by
  constructor
  · intro k hk
    constructor
    · rw [debt_through_hit k hk.le]
      have hpower : 0 ≤ (3359 / 3360 : ℝ) ^ k := pow_nonneg (by norm_num) _
      linarith [mul_nonneg (by norm_num : (0 : ℝ) ≤ 2199 / 200000) hpower]
    · intro who hne
      have hpair := congrArg (fun pair : QuittingTerminalSemanticPair (Fin 4) =>
        pair.1 who) (actual_pair_through_hit k hk.le)
      have hbefore := payoff_before_scalar k hk
      fin_cases who <;>
        norm_num +decide [quittingTerminalSemanticPair, realReward,
          rationalQuittingRewardToReal, reward, quittingSingletonTerminal] at hpair ⊢ <;>
        first | exact (hne rfl).elim | linarith
  · have hpair := congrArg (fun pair : QuittingTerminalSemanticPair (Fin 4) =>
      pair.1 1) (actual_pair_through_hit 155 le_rfl)
    have hlast :
        -20 + (4199 / 200 : ℝ) * (3359 / 3360 : ℝ) ^ 155 ≤ 1 / 20 := by norm_num
    change quittingTerminalPayoff realReward (wordProfile (word 155)) 1 =
      -20 + (4199 / 200 : ℝ) * (3359 / 3360 : ℝ) ^ 155 at hpair
    linarith

private theorem hit_iff_actual (k : ℕ) :
    rationalSoloPayoffDebtThresholdHit reward 0 (1 / 3360) (1 / 10)
      (rationalQuittingFiniteWordSemanticPair reward source) k ↔
    quittingTerminalSemanticDebtSum
        (quittingTerminalSemanticPair realReward (wordProfile (word k))) < 1 / 10 ∨
      ∃ who : Fin 4, who ≠ 0 ∧
        quittingTerminalPayoff realReward (wordProfile (word k)) who ≤
          realReward (quittingSingletonTerminal who) who + 1 / 20 := by
  have h := rationalSoloPayoffDebtThresholdHit_iff_real reward 0
    (by norm_num : (1 / 3360 : ℚ) ∈ Set.Icc 0 1) (1 / 10)
    (rationalQuittingFiniteWordSemanticPair reward source) k
  have hsource : (rationalQuittingFiniteWordSemanticPair reward source).toReal =
      quittingTerminalSemanticPair realReward (wordProfile source) :=
    (quittingTerminalSemanticPair_rationalFiniteWord_eq_cast reward source).symm
  have hword := actual_solo_word_pair reward source 0 (1 / 3360) (by norm_num) k
  change quittingTerminalSemanticPair realReward (wordProfile (word k)) =
    quittingSoloSemanticIterate (rationalQuittingRewardToReal reward) 0
      (quittingHazardCoin ((1 / 3360 : ℚ) : ℝ) _ _)
      (quittingTerminalSemanticPair realReward (wordProfile source)) k at hword
  unfold quittingSoloPayoffDebtThresholdHit at h
  rw [hsource, ← hword] at h
  simpa only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat, quittingTerminalSemanticPair,
    show (1 / 10 : ℝ) / 2 = 1 / 20 by norm_num] using h

/-- The canonical executable least index is EXACTLY 155. -/
theorem executable_index_eq :
    executableRationalPayoffDebtThresholdIndex reward source 0 21 (1 / 10)
      (by norm_num) (by norm_num) (by norm_num) reward_bound source_concentrated
      source_owner_payoff source_failed_column = 155 := by
  have hhit : rationalSoloPayoffDebtThresholdHit reward 0 (1 / 3360) (1 / 10)
      (rationalQuittingFiniteWordSemanticPair reward source) 155 :=
    (hit_iff_actual 155).mpr (Or.inr ⟨1, by decide, by
      simpa +decide [realReward, rationalQuittingRewardToReal, reward,
        quittingSingletonTerminal] using first_payoff_hit.2⟩)
  have hbefore : ∀ k < 155, ¬rationalSoloPayoffDebtThresholdHit reward 0 (1 / 3360) (1 / 10)
      (rationalQuittingFiniteWordSemanticPair reward source) k := by
    intro k hk h
    rcases (hit_iff_actual k).mp h with hsmall | ⟨who, hne, hpayoff⟩
    · exact not_lt_of_ge (first_payoff_hit.1 k hk).1 hsmall
    · exact not_le_of_gt ((first_payoff_hit.1 k hk).2 who hne) hpayoff
  have hs := executableRationalPayoffDebtThresholdIndex_spec reward source 0 21 (1 / 10)
    (by norm_num) (by norm_num) (by norm_num) reward_bound source_concentrated
    source_owner_payoff source_failed_column
  rw [working_hazard] at hs
  apply le_antisymm
  · apply le_of_not_gt
    intro hgt
    exact hs.2.2.2 155 hgt hhit
  · apply le_of_not_gt
    intro hlt
    exact hbefore _ hlt hs.2.2.1

/-- The selected q is also auxiliary Nash at this actual reached cap annotation. -/
theorem auxiliary_at_crossing_exact :
    IsεQuittingRootNash realReward
      (fun who => (quittingTerminalSemanticPair realReward (wordProfile (word 155))).2 who -
        (quittingTerminalSemanticDebtSum
          (quittingTerminalSemanticPair realReward (wordProfile (word 155))) - 1 / 160))
      0 exitRoot.toPMF := by
  apply exitRoot_exact_of_continue_bound
  rw [debt_through_hit 155 le_rfl, actual_pair_through_hit 155 le_rfl]
  have hpower : 0 ≤ (3359 / 3360 : ℝ) ^ 155 := pow_nonneg (by norm_num) _
  change (2 / 33 : ℝ) *
    (11 / 10 - (1 / 10 + (2199 / 200000) * (3359 / 3360 : ℝ) ^ 155 - 1 / 160)) ≤ 53 / 33
  nlinarith

/-- The original owner Continue cap 11/10 is retained in the full prefix calculation. -/
theorem actual_final_pair :
    quittingTerminalSemanticPair realReward (wordProfile finalWord) =
      (fun who => (exactValue who : ℝ), fun who => (exactValue who : ℝ)) := by
  unfold finalWord wordProfile
  rw [List.map_cons, quittingLiteralRootStackProfile_cons,
    quittingTerminalSemanticPair_rootThenContinuation]
  apply exitRoot_prefix
  change (2 / 33 : ℝ) *
    (quittingTerminalSemanticPair realReward (wordProfile (word 155))).2 0 ≤ _
  rw [actual_pair_through_hit 155 le_rfl]
  norm_num

theorem rational_final_pair :
    rationalQuittingFiniteWordSemanticPair reward finalWord = (exactValue, exactValue) := by
  apply RationalQuittingSemanticPair.toReal_injective
  exact (quittingTerminalSemanticPair_rationalFiniteWord_eq_cast reward finalWord).symm.trans
    actual_final_pair

theorem finalWord_length : finalWord.length = 158 := by
  simp [finalWord, word, source]

theorem actual_final_debt_zero :
    quittingTerminalSemanticDebtSum
      (quittingTerminalSemanticPair realReward (wordProfile finalWord)) = 0 := by
  rw [actual_final_pair]
  simp [quittingTerminalSemanticDebtSum, quittingTerminalSemanticDebt]

theorem actual_final_isTerminalNash :
    (quittingGame realReward).IsεAsymptoticNash
      (quittingTerminalPayoff realReward) 0 (wordProfile finalWord) := by
  apply isEpsilonAsymptoticNash_of_terminalSemanticDebtSum_le
  exact actual_final_debt_zero.le

/-- SAME 158-date independent laws, with their exact rational finite and Never masses. -/
theorem actual_final_finiteLaws :
    ∃ mixed : Fin 4 → PMF (Option (Fin finalWord.length)),
      (∀ who choice, (mixed who choice).toReal =
        (rationalFiniteClockMass (rationalQuittingFiniteWordSequence finalWord)
          finalWord.length who choice : ℝ)) ∧
      quittingTerminalSemanticPair realReward
        (quittingFiniteDeadlineTimingProfile realReward finalWord.length mixed) =
        (fun who => (exactValue who : ℝ), fun who => (exactValue who : ℝ)) := by
  obtain ⟨mixed, hmass, hpair⟩ := exists_rationalQuittingFiniteWordLaws_exact reward finalWord
  refine ⟨mixed, hmass, ?_⟩
  simpa only [rational_final_pair] using hpair

end

end GameTheory.CrossMassPayoffThresholdRegression
