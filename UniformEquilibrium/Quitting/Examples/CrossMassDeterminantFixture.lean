import UniformEquilibrium.Quitting.Root.RationalPayoffDebtThresholdScan
import UniformEquilibrium.Quitting.Root.RationalFiniteWordSearch
import UniformEquilibrium.Quitting.Root.FinFourEndpointRowSum
import UniformEquilibrium.Quitting.Paths.TwoPairCrossMassRewardExclusion
import UniformEquilibrium.Quitting.Paths.SureExitSet
import UniformEquilibrium.Quitting.Paths.FiniteCalendarFiniteWordPayoffEquivalence
import UniformEquilibrium.Quitting.Classification.Existence.PerfectAbsorbingRow
import UniformEquilibrium.Quitting.Root.PlayerwiseAffineReward
import UniformEquilibrium.Quitting.Terminal.PositiveMinimumSemanticDebt

/-! # A complete cross-mass reward fixture and its actual semantic comparisons

The table is literal, including its exceptional singleton entry 1001/1000.
All comparisons concern the same original table and the same displayed roots.
The correlated half-row vector is not asserted to be independently attainable.
-/

namespace GameTheory.CrossMassDeterminantFixture

open QuittingSureSetOwnerRepair QuittingFinFourEndpointRows

def reward : RationalQuittingReward 4 := fun terminal =>
  if terminal.1 = {0} then ![1, -20, 1, 1]
  else if terminal.1 = {1} then ![0, 0, 1, 1]
  else if terminal.1 = {0, 1} then ![21, 0, 0, 0]
  else if terminal.1 = {2} then ![0, 0, 0, 1001 / 1000]
  else if terminal.1 = {0, 2} then ![1, 0, 0, 1]
  else if terminal.1 = {1, 2} then ![0, 0, 3, -2]
  else if terminal.1 = {0, 1, 2} then ![1, -2, 2, 2]
  else if terminal.1 = {3} then ![1, -20, 1, 0]
  else if terminal.1 = {0, 3} then ![1, -20, 2, 0]
  else if terminal.1 = {1, 3} then ![1, 0, -1, 3]
  else if terminal.1 = {0, 1, 3} then ![1, 0, -1, 2]
  else if terminal.1 = {2, 3} then ![1, 1, 1, 1]
  else if terminal.1 = {0, 2, 3} then ![1, 0, -2, 1]
  else if terminal.1 = {1, 2, 3} then ![1, 0, 1, 3]
  else ![1, 0, 3, -2]

def singleton : Fin 4 → ℚ := ![1, 0, 0, 0]

theorem reward_rows (row : Fin 15) :
    reward (Math.Finset.finFourCoalitionRowEquiv row) =
      (![![1, -20, 1, 1], ![0, 0, 1, 1], ![21, 0, 0, 0],
        ![0, 0, 0, 1001 / 1000], ![1, 0, 0, 1], ![0, 0, 3, -2],
        ![1, -2, 2, 2], ![1, -20, 1, 0], ![1, -20, 2, 0],
        ![1, 0, -1, 3], ![1, 0, -1, 2], ![1, 1, 1, 1],
        ![1, 0, -2, 1], ![1, 0, 1, 3], ![1, 0, 3, -2]]
        : Fin 15 → Fin 4 → ℚ) row := by
  fin_cases row <;> rfl

theorem reward_singleton (who : Fin 4) :
    reward (quittingSingletonTerminal who) who = singleton who := by
  fin_cases who <;> decide

theorem reward_bound : ∀ terminal who, |reward terminal who| ≤ 21 := by
  intro terminal who
  obtain ⟨row, rfl⟩ := Math.Finset.finFourCoalitionRowEquiv.surjective terminal
  rw [reward_rows]
  fin_cases row <;> fin_cases who <;> norm_num

theorem reward_bound_attained : reward ⟨{0, 1}, by simp⟩ 0 = 21 := by decide

private theorem zero_row_bound : ∀ terminal,
    reward terminal 0 - reward (quittingSingletonTerminal 0) 0 ≤
      20 * (if terminal = ⟨{0, 1}, by simp⟩ then 1 else 0) -
        ((if terminal = ⟨{1}, by simp⟩ then 1 else 0) +
          (if terminal = ⟨{2}, by simp⟩ then 1 else 0) +
          (if terminal = ⟨{1, 2}, by simp⟩ then 1 else 0)) := by
  intro terminal
  obtain ⟨row, rfl⟩ := Math.Finset.finFourCoalitionRowEquiv.surjective terminal
  fin_cases row <;> norm_num +decide [reward, quittingSingletonTerminal,
    Math.Finset.finFourCoalitionRowEquiv, Math.Finset.finFourCoalitionOfRow]

private theorem one_row_bound : ∀ terminal,
    reward terminal 1 - reward (quittingSingletonTerminal 1) 1 ≤
      (if terminal = ⟨{2, 3}, by simp⟩ then 1 else 0) -
        20 * ((if terminal = ⟨{0}, by simp⟩ then 1 else 0) +
          (if terminal = ⟨{3}, by simp⟩ then 1 else 0) +
          (if terminal = ⟨{0, 3}, by simp⟩ then 1 else 0)) := by
  intro terminal
  obtain ⟨row, rfl⟩ := Math.Finset.finFourCoalitionRowEquiv.surjective terminal
  fin_cases row <;> norm_num +decide [reward, quittingSingletonTerminal,
    Math.Finset.finFourCoalitionRowEquiv, Math.Finset.finFourCoalitionOfRow]

def exitRoot : RationalQuittingRoot 4 where
  probability := ![1, 1 / 3, 10 / 11, 0]
  nonnegative := by intro who; fin_cases who <;> norm_num
  le_one := by intro who; fin_cases who <;> norm_num

def exactValue : Fin 4 → ℚ := ![53 / 33, -20 / 11, 2 / 3, 14 / 11]

noncomputable section

abbrev realReward := rationalQuittingRewardToReal reward

def wordProfile (word : List (RationalQuittingRoot 4)) :
    (quittingGame realReward).BehaviorProfile :=
  quittingLiteralRootStackProfile realReward (word.map RationalQuittingRoot.toPMF)
    (quittingAlwaysContinueProfile realReward)

theorem real_reward_bound : ∀ terminal who, |realReward terminal who| ≤ 21 := by
  intro terminal who
  change |(reward terminal who : ℝ)| ≤ 21
  exact_mod_cast reward_bound terminal who

/-- All thirty row inequalities feed the original independent-clock determinant. -/
theorem actual_weakSubsetExclusion :
    HasQuittingActualWeakSubsetExclusion realReward {0, 1} := by
  apply hasQuittingActualWeakSubsetExclusion_zero_one_of_crossMassBounds
    (20 : ℝ) 1 1 20 (by norm_num) (by norm_num) (by norm_num)
  · norm_num +decide [realReward, rationalQuittingRewardToReal, reward,
      quittingSingletonTerminal]
  · norm_num +decide [realReward, rationalQuittingRewardToReal, reward,
      quittingSingletonTerminal]
  · intro terminal
    change (reward terminal 0 : ℝ) - (reward (quittingSingletonTerminal 0) 0 : ℝ) ≤ _
    simp only [one_mul]
    exact_mod_cast zero_row_bound terminal
  · intro terminal
    change (reward terminal 1 : ℝ) - (reward (quittingSingletonTerminal 1) 1 : ℝ) ≤ _
    simp only [one_mul]
    exact_mod_cast one_row_bound terminal

private theorem raw_one_quit_le_one (root : Fin 4 → PMF Bool) :
    quittingRootQuitPayoff realReward 0 root 1 ≤ 1 := by
  have hbound : ∀ terminal, reward terminal 1 ≤ 1 := by decide
  unfold quittingRootQuitPayoff quittingRootExpectedPayoff
  calc
    _ ≤ _root_.Math.Probability.expect
        (_root_.Math.PMFProduct.pmfPi (Function.update root 1 (PMF.pure true)))
        (fun _ => (1 : ℝ)) := by
      apply _root_.Math.Probability.expect_mono
      intro action
      unfold quittingRootPayoff
      split
      · change (reward _ 1 : ℝ) ≤ 1
        exact_mod_cast hbound _
      · norm_num
    _ = 1 := _root_.Math.Probability.expect_const _ _

private theorem raw_zero_quit_of_one_zero (root : Fin 4 → PMF Bool)
    (hzero : (root 1 true).toReal = 0) :
    quittingRootQuitPayoff realReward 0 root 0 = 1 := by
  rw [quittingRootQuitPayoff_eq_sigmaValue, sigmaValue_eq_pureQuitEndpointRowSum]
  norm_num +decide [pureQuitEndpointRowSum, Fin.sum_univ_succ, opponentCoalitionMass,
    Math.Finset.finFourCoalitionOfRow, Fin.prod_univ_succ, hazardOfRoot,
    weightOfReward, realReward, rationalQuittingRewardToReal, reward, hzero]
  ring

private theorem raw_two_quit_of_one_zero (root : Fin 4 → PMF Bool)
    (hzero : (root 1 true).toReal = 0) :
    quittingRootQuitPayoff realReward 0 root 2 =
      (root 3 true).toReal - 3 * (root 0 true).toReal * (root 3 true).toReal := by
  rw [quittingRootQuitPayoff_eq_sigmaValue, sigmaValue_eq_pureQuitEndpointRowSum]
  norm_num +decide [pureQuitEndpointRowSum, Fin.sum_univ_succ, opponentCoalitionMass,
    Math.Finset.finFourCoalitionOfRow, Fin.prod_univ_succ, hazardOfRoot,
    weightOfReward, realReward, rationalQuittingRewardToReal, reward, hzero]
  ring

private theorem raw_three_quit_of_one_zero (root : Fin 4 → PMF Bool)
    (hzero : (root 1 true).toReal = 0) :
    quittingRootQuitPayoff realReward 0 root 3 = (root 2 true).toReal := by
  rw [quittingRootQuitPayoff_eq_sigmaValue, sigmaValue_eq_pureQuitEndpointRowSum]
  norm_num +decide [pureQuitEndpointRowSum, Fin.sum_univ_succ, opponentCoalitionMass,
    Math.Finset.finFourCoalitionOfRow, Fin.prod_univ_succ, hazardOfRoot,
    weightOfReward, realReward, rationalQuittingRewardToReal, reward, hzero]
  ring

/-- The RAW table satisfies the unit-level low-active condition at every absorbing
product root, although it does not have unit singleton rewards. -/
theorem raw_hasLowActiveQuittingRootQuitPayoff :
    HasLowActiveQuittingRootQuitPayoff realReward := by
  intro root habsorption
  by_cases hone : 0 < (root 1 true).toReal
  · exact ⟨1, hone, raw_one_quit_le_one root⟩
  have hzero : (root 1 true).toReal = 0 :=
    le_antisymm (le_of_not_gt hone) ENNReal.toReal_nonneg
  have hmass : quittingStationaryContinueMass root < 1 := by
    unfold quittingRootAbsorptionMass at habsorption
    linarith
  obtain ⟨who, hactive⟩ := exists_quitProbability_pos_of_continueMass_lt_one hmass
  refine ⟨who, hactive, ?_⟩
  fin_cases who
  · change quittingRootQuitPayoff realReward 0 root 0 ≤ 1
    exact (raw_zero_quit_of_one_zero root hzero).le
  · change 0 < (root 1 true).toReal at hactive
    exact (hone hactive).elim
  · change quittingRootQuitPayoff realReward 0 root 2 ≤ 1
    rw [raw_two_quit_of_one_zero root hzero]
    have hupper : (root 3 true).toReal ≤ 1 := hazardOfRoot_le_one root 3
    have hproduct : 0 ≤ (root 0 true).toReal * (root 3 true).toReal :=
      mul_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg
    nlinarith
  · change quittingRootQuitPayoff realReward 0 root 3 ≤ 1
    rw [raw_three_quit_of_one_zero root hzero]
    exact hazardOfRoot_le_one root 2

/-- The raw low-active condition alone does not supply the unit-singleton premise. -/
theorem raw_not_unitSoloExit : ¬QuittingUnitSoloExit realReward := by
  intro hunit
  have h := hunit (1 : Fin 4)
  rw [quittingSoloReward_self] at h
  norm_num +decide [realReward, rationalQuittingRewardToReal, reward,
    quittingSingletonTerminal] at h

private def exitHazard : Fin 4 → ℝ := ![1, 1 / 3, 10 / 11, 0]

private theorem exit_hazard : hazardOfRoot exitRoot.toPMF = exitHazard := by
  funext who
  fin_cases who <;> norm_num [hazardOfRoot, exitRoot, exitHazard]

private theorem exit_quit_0 :
    pureQuitEndpointRowSum realReward exitHazard 0 = 53 / 33 := by
  norm_num +decide [pureQuitEndpointRowSum, Fin.sum_univ_succ, opponentCoalitionMass,
    Math.Finset.finFourCoalitionOfRow, Fin.prod_univ_succ, exitHazard,
    weightOfReward, realReward, rationalQuittingRewardToReal, reward]

private theorem exit_quit_1 :
    pureQuitEndpointRowSum realReward exitHazard 1 = -20 / 11 := by
  norm_num +decide [pureQuitEndpointRowSum, Fin.sum_univ_succ, opponentCoalitionMass,
    Math.Finset.finFourCoalitionOfRow, Fin.prod_univ_succ, exitHazard,
    weightOfReward, realReward, rationalQuittingRewardToReal, reward]

private theorem exit_quit_2 :
    pureQuitEndpointRowSum realReward exitHazard 2 = 2 / 3 := by
  norm_num +decide [pureQuitEndpointRowSum, Fin.sum_univ_succ, opponentCoalitionMass,
    Math.Finset.finFourCoalitionOfRow, Fin.prod_univ_succ, exitHazard,
    weightOfReward, realReward, rationalQuittingRewardToReal, reward]

private theorem exit_quit_3 :
    pureQuitEndpointRowSum realReward exitHazard 3 = 2 / 33 := by
  norm_num +decide [pureQuitEndpointRowSum, Fin.sum_univ_succ, opponentCoalitionMass,
    Math.Finset.finFourCoalitionOfRow, Fin.prod_univ_succ, exitHazard,
    weightOfReward, realReward, rationalQuittingRewardToReal, reward]

private theorem exit_excluded_0 :
    excludedEndpointRowSum realReward exitHazard 0 = 0 := by
  norm_num +decide [excludedEndpointRowSum, Fin.sum_univ_succ, opponentCoalitionMass,
    Math.Finset.finFourCoalitionOfRow, Fin.prod_univ_succ, exitHazard,
    weightOfReward, realReward, rationalQuittingRewardToReal, reward]

private theorem exit_excluded_1 :
    excludedEndpointRowSum realReward exitHazard 1 = -20 / 11 := by
  norm_num +decide [excludedEndpointRowSum, Fin.sum_univ_succ, opponentCoalitionMass,
    Math.Finset.finFourCoalitionOfRow, Fin.prod_univ_succ, exitHazard,
    weightOfReward, realReward, rationalQuittingRewardToReal, reward]

private theorem exit_excluded_2 :
    excludedEndpointRowSum realReward exitHazard 2 = 2 / 3 := by
  norm_num +decide [excludedEndpointRowSum, Fin.sum_univ_succ, opponentCoalitionMass,
    Math.Finset.finFourCoalitionOfRow, Fin.prod_univ_succ, exitHazard,
    weightOfReward, realReward, rationalQuittingRewardToReal, reward]

private theorem exit_excluded_3 :
    excludedEndpointRowSum realReward exitHazard 3 = 14 / 11 := by
  norm_num +decide [excludedEndpointRowSum, Fin.sum_univ_succ, opponentCoalitionMass,
    Math.Finset.finFourCoalitionOfRow, Fin.prod_univ_succ, exitHazard,
    weightOfReward, realReward, rationalQuittingRewardToReal, reward]

private theorem exit_mass (who : Fin 4) :
    continueMassExcl exitHazard who = (![2 / 33, 0, 0, 0] : Fin 4 → ℝ) who := by
  fin_cases who
  · change (∏ player ∈ Finset.univ.erase (0 : Fin 4),
        (1 - exitHazard player)) = 2 / 33
    rw [show Finset.univ.erase (0 : Fin 4) = {1, 2, 3} by decide]
    norm_num [exitHazard]
  · change (∏ player ∈ Finset.univ.erase (1 : Fin 4),
        (1 - exitHazard player)) = 0
    rw [show Finset.univ.erase (1 : Fin 4) = {0, 2, 3} by decide]
    norm_num [exitHazard]
  · change (∏ player ∈ Finset.univ.erase (2 : Fin 4),
        (1 - exitHazard player)) = 0
    rw [show Finset.univ.erase (2 : Fin 4) = {0, 1, 3} by decide]
    norm_num [exitHazard]
  · change (∏ player ∈ Finset.univ.erase (3 : Fin 4),
        (1 - exitHazard player)) = 0
    rw [show Finset.univ.erase (3 : Fin 4) = {0, 1, 2} by decide]
    norm_num [exitHazard]

/-- Pure Quit reads no continuation; these are the four actual endpoint values. -/
theorem exitRoot_quit (tail : Payoff (Fin 4)) (who : Fin 4) :
    quittingRootQuitPayoff realReward tail exitRoot.toPMF who =
      (![53 / 33, -20 / 11, 2 / 3, 2 / 33] : Fin 4 → ℝ) who := by
  rw [quittingRootQuitPayoff_eq_sigmaValue, sigmaValue_eq_pureQuitEndpointRowSum,
    exit_hazard]
  fin_cases who
  · exact exit_quit_0
  · exact exit_quit_1
  · exact exit_quit_2
  · exact exit_quit_3

/-- Only player zero can reach the declared continuation after forcing Continue. -/
theorem exitRoot_continue (tail : Payoff (Fin 4)) (who : Fin 4) :
    quittingRootContinuePayoff realReward tail exitRoot.toPMF who =
      (if who = 0 then (2 / 33) * tail 0 else
        (![(0 : ℝ), -20 / 11, 2 / 3, 14 / 11] : Fin 4 → ℝ) who) := by
  rw [quittingRootContinuePayoff_eq_gammaValue, gammaValue,
    excludedValue_eq_excludedEndpointRowSum, exit_hazard, exit_mass]
  fin_cases who
  · change excludedEndpointRowSum realReward exitHazard 0 +
      (2 / 33) * tail 0 = (2 / 33) * tail 0
    rw [exit_excluded_0, zero_add]
  · change excludedEndpointRowSum realReward exitHazard 1 + 0 * tail 1 = -20 / 11
    rw [exit_excluded_1, zero_mul, add_zero]
  · change excludedEndpointRowSum realReward exitHazard 2 + 0 * tail 2 = 2 / 3
    rw [exit_excluded_2, zero_mul, add_zero]
  · change excludedEndpointRowSum realReward exitHazard 3 + 0 * tail 3 = 14 / 11
    rw [exit_excluded_3, zero_mul, add_zero]

/-- Exact auxiliary Nash is checked against the caller's actual annotation,
with the player-zero Continue endpoint retained explicitly. -/
theorem exitRoot_exact_of_continue_bound (tail : Payoff (Fin 4))
    (htail : (2 / 33 : ℝ) * tail 0 ≤ 53 / 33) :
    IsεQuittingRootNash realReward tail 0 exitRoot.toPMF := by
  apply (isZeroQuittingRootEndpointNash_iff_isZeroQuittingRootNash _ _ _).mp
  intro who
  rw [quittingRootEndpointDifference, exitRoot_quit, exitRoot_continue]
  fin_cases who <;> norm_num [exitRoot]
  linarith

/-- The actual old-tail Continue cap is checked, not replaced by auxiliary Nash. -/
theorem exitRoot_prefix (pair : QuittingTerminalSemanticPair (Fin 4))
    (hcap : (2 / 33 : ℝ) * pair.2 0 ≤ 53 / 33) :
    quittingTerminalSemanticPrefix realReward exitRoot.toPMF pair =
      (fun who => (exactValue who : ℝ), fun who => (exactValue who : ℝ)) := by
  apply Prod.ext
  · funext who
    change quittingRootSuccessorPayoff realReward pair.1 exitRoot.toPMF who = _
    rw [quittingRootSuccessorPayoff_eq_endpointMix, exitRoot_quit, exitRoot_continue]
    fin_cases who <;> norm_num [exitRoot, exactValue]
  · funext who
    change max _ _ = _
    rw [exitRoot_quit, exitRoot_continue]
    fin_cases who
    · norm_num [exactValue]
      change (2 / 33 : ℝ) * (Function.update pair.1 (0 : Fin 4) (pair.2 0)) 0 ≤ 53 / 33
      rw [Function.update_self]
      exact hcap
    · norm_num [exactValue]
    · norm_num [exactValue]
    · norm_num [exactValue]

theorem exact_word_pair :
    quittingTerminalSemanticPair realReward (wordProfile [exitRoot]) =
      (fun who => (exactValue who : ℝ), fun who => (exactValue who : ℝ)) := by
  unfold wordProfile
  rw [List.map_cons, List.map_nil, quittingLiteralRootStackProfile_cons,
    quittingTerminalSemanticPair_rootThenContinuation]
  apply exitRoot_prefix
  change (2 / 33 : ℝ) *
    quittingContinuationBestResponseValue realReward
      (quittingAlwaysContinueProfile realReward) 0 ≤ _
  rw [quittingContinuationBestResponseValue_quittingAlwaysContinueProfile]
  norm_num +decide [realReward, rationalQuittingRewardToReal, reward,
    quittingSingletonTerminal]

theorem rational_exact_word_pair :
    rationalQuittingFiniteWordSemanticPair reward [exitRoot] = (exactValue, exactValue) := by
  apply RationalQuittingSemanticPair.toReal_injective
  exact (quittingTerminalSemanticPair_rationalFiniteWord_eq_cast
    reward [exitRoot]).symm.trans exact_word_pair

theorem exact_word_isTerminalNash :
    (quittingGame realReward).IsεAsymptoticNash
      (quittingTerminalPayoff realReward) 0 (wordProfile [exitRoot]) := by
  apply isEpsilonAsymptoticNash_of_terminalSemanticDebtSum_le
  rw [exact_word_pair]
  simp [quittingTerminalSemanticDebtSum, quittingTerminalSemanticDebt]


theorem exactValue_isUniformEquilibriumPayoff :
    (quittingGame realReward).IsUniformEquilibriumPayoff none
      (fun who => (exactValue who : ℝ)) := by
  have hpayoff := congrArg Prod.fst exact_word_pair
  change quittingTerminalPayoff realReward (wordProfile [exitRoot]) =
    (fun who => (exactValue who : ℝ)) at hpayoff
  rw [← hpayoff]
  exact quittingGame_isUniformEquilibriumPayoff_of_terminalNash_exact realReward
    (wordProfile [exitRoot]) exact_word_isTerminalNash

/-- The same root has independent finite-date/Never laws and the exact full cap. -/
theorem exact_word_finiteLaws :
    ∃ mixed : Fin 4 → PMF (Option (Fin 1)),
      (∀ who choice, (mixed who choice).toReal =
        (rationalFiniteClockMass (rationalQuittingFiniteWordSequence [exitRoot])
          1 who choice : ℝ)) ∧
      quittingTerminalSemanticPair realReward
        (quittingFiniteDeadlineTimingProfile realReward 1 mixed) =
        (fun who => (exactValue who : ℝ), fun who => (exactValue who : ℝ)) := by
  obtain ⟨mixed, hmass, hpair⟩ :=
    exists_rationalQuittingFiniteWordLaws_exact reward [exitRoot]
  refine ⟨mixed, hmass, ?_⟩
  simpa only [List.length_cons, List.length_nil, rational_exact_word_pair] using hpair

def purePairProfile : (quittingGame realReward).BehaviorProfile :=
  quittingStationaryProfile realReward (quittingPureSetRoot {2, 3})

theorem purePair_payoff : quittingTerminalPayoff realReward purePairProfile = ![1, 1, 1, 1] := by
  funext who
  unfold purePairProfile
  rw [quittingTerminalPayoff_pureSetRoot]
  fin_cases who <;> norm_num +decide [quittingSetReward, realReward,
    rationalQuittingRewardToReal, reward]

theorem not_actualStrictSingletonDeficit (gap : ℝ) (hgap : 0 < gap) :
    ¬HasQuittingActualStrictSingletonDeficit realReward gap := by
  intro hdeficit
  obtain ⟨who, hwho⟩ := hdeficit purePairProfile
  have hpayoff := congrFun purePair_payoff who
  fin_cases who <;> norm_num +decide [realReward, rationalQuittingRewardToReal,
    reward, quittingSingletonTerminal] at hpayoff hwho ⊢ <;> linarith

theorem not_actualNonconcentratedGroupExclusion (beta : ℝ) (hbeta : beta < 1) :
    ¬HasQuittingActualNonconcentratedGroupExclusion realReward beta := by
  intro hgroup
  obtain ⟨weight, _, hsum, hcapped, hweighted⟩ := hgroup purePairProfile
  have hpayoff (who : Fin 4) : quittingTerminalPayoff realReward purePairProfile who = 1 := by
    have h := congrFun purePair_payoff who
    fin_cases who <;> simpa using h
  simp_rw [hpayoff] at hweighted
  simp only [Fin.sum_univ_four] at hsum hweighted
  norm_num +decide [realReward, rationalQuittingRewardToReal, reward,
    quittingSingletonTerminal] at hweighted
  have hzero := hcapped 0
  linarith

/-- The separating payoff is already produced by the displayed one-row finite word. -/
theorem purePair_finiteWord_payoff :
    quittingFiniteRootWordPayoff realReward [quittingPureSetRoot {2, 3}] 0 =
      ![1, 1, 1, 1] := by
  have hzero : quittingTerminalPayoff realReward
      (quittingAlwaysContinueProfile realReward) = 0 := by
    funext who
    exact quittingTerminalPayoff_quittingAlwaysContinue realReward who
  funext who
  have h := quittingTerminalPayoff_pureSetRootThenContinuation_eq_setReward
    (reward := realReward) {2, 3} (by decide)
    (quittingAlwaysContinueProfile realReward) who
  rw [quittingTerminalPayoff_rootThenContinuation_eq, hzero] at h
  change quittingRootExpectedPayoff realReward
    (fun player => (0 : Payoff (Fin 4)) player) (quittingPureSetRoot {2, 3}) who =
      (![1, 1, 1, 1] : Fin 4 → ℝ) who
  rw [h]
  fin_cases who <;> norm_num +decide [quittingSetReward, realReward,
    rationalQuittingRewardToReal, reward]

theorem not_finiteWordStrictSingletonDeficit (gap : ℝ) (hgap : 0 < gap) :
    ¬(∀ roots : List (Fin 4 → PMF Bool), ∃ who,
      quittingFiniteRootWordPayoff realReward roots 0 who ≤
        realReward (quittingSingletonTerminal who) who - gap) := by
  intro hword
  apply not_actualStrictSingletonDeficit gap hgap
  exact (forall_finiteRootWordPayoff_iff_forall_actualTerminalPayoff realReward
    (fun value => ∃ who, value who ≤
      realReward (quittingSingletonTerminal who) who - gap)).mp hword

theorem not_finiteWordNonconcentratedGroupExclusion (beta : ℝ) (hbeta : beta < 1) :
    ¬(∀ roots : List (Fin 4 → PMF Bool), ∃ weight : Fin 4 → ℝ,
      (∀ who, 0 ≤ weight who) ∧ (∑ who, weight who = 1) ∧
      (∀ who, weight who ≤ beta) ∧
      ∑ who, weight who * (quittingFiniteRootWordPayoff realReward roots 0 who -
        realReward (quittingSingletonTerminal who) who) ≤ 0) := by
  intro hword
  apply not_actualNonconcentratedGroupExclusion beta hbeta
  exact (forall_finiteRootWordPayoff_iff_forall_actualTerminalPayoff realReward
    (fun value => ∃ weight : Fin 4 → ℝ, (∀ who, 0 ≤ weight who) ∧
      (∑ who, weight who = 1) ∧ (∀ who, weight who ≤ beta) ∧
      ∑ who, weight who * (value who -
        realReward (quittingSingletonTerminal who) who) ≤ 0)).mp hword

/-- This is an own-singleton failure on the raw table, not the unit-level predicate. -/
theorem purePair_active_quit_above_singleton (who : Fin 4)
    (hactive : 0 < (quittingPureSetRoot {2, 3} who true).toReal) :
    realReward (quittingSingletonTerminal who) who <
      quittingRootQuitPayoff realReward 0 (quittingPureSetRoot {2, 3}) who := by
  rw [quittingRootQuitPayoff_pureSetRoot_eq_insert]
  fin_cases who
  · norm_num +decide [quittingPureSetRoot, quittingSetAction] at hactive
  · norm_num +decide [quittingPureSetRoot, quittingSetAction] at hactive
  · norm_num +decide [quittingSetReward, realReward, rationalQuittingRewardToReal,
      reward, quittingSingletonTerminal]
  · norm_num +decide [quittingSetReward, realReward, rationalQuittingRewardToReal,
      reward, quittingSingletonTerminal]

/-- Only terminal rewards are translated; Never continues to pay zero. -/
def normalizedReward (t : ℝ) :=
  quittingPlayerwiseAffineReward realReward
    (fun who => 1 / (realReward (quittingSingletonTerminal who) who + t))
    (fun who => t / (realReward (quittingSingletonTerminal who) who + t))

theorem normalizedReward_unitSolo (t : ℝ) (ht : 0 < t) :
    QuittingUnitSoloExit (normalizedReward t) := by
  intro who
  fin_cases who
  · norm_num +decide [normalizedReward, quittingPlayerwiseAffineReward,
      realReward, rationalQuittingRewardToReal, reward, quittingSingletonTerminal,
      quittingSoloReward]
    calc
      _ = (1 + t) / (1 + t) := by ring
      _ = 1 := div_self (show (1 : ℝ) + t ≠ 0 by linarith)
  · norm_num +decide [normalizedReward, quittingPlayerwiseAffineReward,
      realReward, rationalQuittingRewardToReal, reward, quittingSingletonTerminal,
      quittingSoloReward, div_self ht.ne']
  · norm_num +decide [normalizedReward, quittingPlayerwiseAffineReward,
      realReward, rationalQuittingRewardToReal, reward, quittingSingletonTerminal,
      quittingSoloReward, div_self ht.ne']
  · norm_num +decide [normalizedReward, quittingPlayerwiseAffineReward,
      realReward, rationalQuittingRewardToReal, reward, quittingSingletonTerminal,
      quittingSoloReward, div_self ht.ne']

theorem normalizedReward_not_lowActive (t : ℝ) (ht : 0 < t) :
    ¬HasLowActiveQuittingRootQuitPayoff (normalizedReward t) := by
  intro hlow
  obtain ⟨who, hactive, hbound⟩ := hlow (quittingPureSetRoot {2, 3})
    (by rw [quittingRootAbsorptionMass_pureSetRoot_of_nonempty (by simp)]; norm_num)
  rw [quittingRootQuitPayoff_pureSetRoot_eq_insert] at hbound
  have hineq : 1 / t + t / t ≤ 1 := by
    fin_cases who <;>
      norm_num +decide [quittingPureSetRoot, quittingSetAction] at hactive <;>
      norm_num +decide [quittingSetReward, normalizedReward, quittingPlayerwiseAffineReward,
        realReward, rationalQuittingRewardToReal, reward, quittingSingletonTerminal] at hbound <;>
      simpa only [one_div] using hbound
  rw [div_self ht.ne'] at hineq
  have hpositive := one_div_pos.mpr ht
  linarith

/-- The displayed half-row vector is a correlated convex-hull witness only. -/
theorem correlated_half_rows :
    (fun who => ((realReward ⟨{0, 1}, by simp⟩ who +
      realReward ⟨{2, 3}, by simp⟩ who) / 2)) = ![11, 1 / 2, 1 / 2, 1 / 2] := by
  funext who
  fin_cases who <;> norm_num +decide [realReward, rationalQuittingRewardToReal, reward]

theorem correlated_half_surplus_pos (who : Fin 4) :
    0 < (realReward ⟨{0, 1}, by simp⟩ who + realReward ⟨{2, 3}, by simp⟩ who) / 2 -
      realReward (quittingSingletonTerminal who) who := by
  have h := congrFun correlated_half_rows who
  rw [h]
  fin_cases who <;> norm_num +decide [realReward, rationalQuittingRewardToReal,
    reward, quittingSingletonTerminal]

/-- Every nonzero nonnegative recipient weight is strictly positive on some raw row. -/
theorem exists_positive_weighted_terminal (weight : Fin 4 → ℝ)
    (hnonnegative : ∀ who, 0 ≤ weight who) (hne : weight ≠ 0) :
    ∃ terminal, 0 < ∑ who, weight who *
      (realReward terminal who - realReward (quittingSingletonTerminal who) who) := by
  have hpositive : ∃ who, 0 < weight who := by
    by_contra hnot
    apply hne
    funext who
    have hle : weight who ≤ 0 := le_of_not_gt (fun h => hnot ⟨who, h⟩)
    exact le_antisymm hle (hnonnegative who)
  obtain ⟨who, hwho⟩ := hpositive
  have hsum : 0 < ∑ player, weight player *
      ((realReward ⟨{0, 1}, by simp⟩ player + realReward ⟨{2, 3}, by simp⟩ player) / 2 -
        realReward (quittingSingletonTerminal player) player) := by
    apply Finset.sum_pos'
    · intro player _
      exact mul_nonneg (hnonnegative player) (correlated_half_surplus_pos player).le
    · exact ⟨who, Finset.mem_univ who, mul_pos hwho (correlated_half_surplus_pos who)⟩
  by_cases hfirst : 0 < ∑ who, weight who *
      (realReward ⟨{0, 1}, by simp⟩ who - realReward (quittingSingletonTerminal who) who)
  · exact ⟨⟨{0, 1}, by simp⟩, hfirst⟩
  refine ⟨⟨{2, 3}, by simp⟩, ?_⟩
  have hidentity :
      (∑ player, weight player *
        ((realReward ⟨{0, 1}, by simp⟩ player + realReward ⟨{2, 3}, by simp⟩ player) / 2 -
          realReward (quittingSingletonTerminal player) player)) =
      ((∑ player, weight player * (realReward ⟨{0, 1}, by simp⟩ player -
        realReward (quittingSingletonTerminal player) player)) +
       (∑ player, weight player * (realReward ⟨{2, 3}, by simp⟩ player -
        realReward (quittingSingletonTerminal player) player))) / 2 := by
    rw [← Finset.sum_add_distrib, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro player _
    ring
  rw [hidentity] at hsum
  have := le_of_not_gt hfirst
  linarith

end

end GameTheory.CrossMassDeterminantFixture
