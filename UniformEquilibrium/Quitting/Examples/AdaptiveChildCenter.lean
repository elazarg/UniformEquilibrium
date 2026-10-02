import UniformEquilibrium.Quitting.Root.OneDateNeverNashDebt
import UniformEquilibrium.Quitting.Terminal.TargetTail.TerminalUniformPayoffSelection
import UniformEquilibrium.Quitting.Classification.PlayerDeletionLift
import UniformEquilibrium.Quitting.Classification.PlayerReindex
import UniformEquilibrium.Quitting.Paths.CounterfactualStoppingLaw
import UniformEquilibrium.Quitting.Paths.StoppingLawReconstruction
import MathUE.Probability.DiscreteHazardMixture

/-! # Center table for the adaptive unchanged-child obstruction -/

noncomputable section

namespace GameTheory.AdaptiveChildCenter

open _root_.Math.Probability Math.PMFProduct _root_.Math.Probability.DiscreteHazard

/-- A signed four-player reward table with three active players and a sure-quitting anchor. -/
def reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4) :=
  fun terminal who =>
    if who = 0 then
      if 0 ∈ terminal.1 then 1 else 2 * if 2 ∈ terminal.1 then 1 else 0
    else if who = 1 then
      (2 * (if 0 ∈ terminal.1 then 1 else 0) - 1) *
        if 1 ∈ terminal.1 then 1 else 0
    else if who = 2 then
      (2 * (if 1 ∈ terminal.1 then 1 else 0) - 1) *
        if 2 ∈ terminal.1 then 1 else 0
    else
      if 3 ∈ terminal.1 then 1 else 0

/-- The canonical increasing equivalence from `Fin 3` to the complement of
one deleted player of `Fin 4`. -/
def deletedEquiv (deleted : Fin 4) : Fin 3 ≃ QuittingDeletedPlayer deleted :=
  finSuccAboveEquiv deleted

/-- The literal three-player child table, first restricted to the survivor
subtype and then reindexed by `Fin 3`. -/
def childReward (deleted : Fin 4) :
    {S : Finset (Fin 3) // S.Nonempty} → Payoff (Fin 3) :=
  quittingRewardReindex (deletedEquiv deleted).symm
    (quittingDeletePlayerReward reward deleted)

/-- Retain each surviving parent's independent stopping law without changing
any atom or its Never mass. -/
def restrictLaws (deleted : Fin 4) (laws : Fin 4 → PMF (Option ℕ)) :
    Fin 3 → PMF (Option ℕ) :=
  fun who => laws (deletedEquiv deleted who).1

/-- Reconstruct an actual child behavioral profile from the unchanged survivor laws. -/
def restrictedProfile (deleted : Fin 4) (laws : Fin 4 → PMF (Option ℕ)) :
    (quittingGame (childReward deleted)).BehaviorProfile :=
  quittingStoppingLawProfile (childReward deleted) (restrictLaws deleted laws)

/-- Restrict an arbitrary parent behavioral profile through its actual
independent stopping laws, not through its differently typed histories. -/
def restrictedProfileOfParent (deleted : Fin 4)
    (parent : (quittingGame reward).BehaviorProfile) :
    (quittingGame (childReward deleted)).BehaviorProfile :=
  restrictedProfile deleted (quittingBehaviorStoppingLaws reward parent)

@[simp] theorem restrictedProfile_stoppingLaw
    (deleted : Fin 4) (laws : Fin 4 → PMF (Option ℕ)) (who : Fin 3) :
    quittingBehaviorStoppingLaw (childReward deleted)
        (restrictedProfile deleted laws who) =
      laws (deletedEquiv deleted who).1 := by
  simp [restrictedProfile, restrictLaws]

@[simp] theorem restrictedProfileOfParent_stoppingLaw
    (deleted : Fin 4) (parent : (quittingGame reward).BehaviorProfile)
    (who : Fin 3) :
    quittingBehaviorStoppingLaw (childReward deleted)
        (restrictedProfileOfParent deleted parent who) =
      quittingBehaviorStoppingLaw reward
        (parent (deletedEquiv deleted who).1) := by
  simp [restrictedProfileOfParent, quittingBehaviorStoppingLaws]

/-- A Boolean fair coin, used as Quit-at-zero versus Never. -/
def halfCoin : PMF Bool :=
  booleanCoin (1 / 2 : ℝ) (by norm_num) (by norm_num)

/-- The center root: the three active players use fair coins and the anchor quits surely. -/
def root : Fin 4 → PMF Bool := ![halfCoin, halfCoin, halfCoin, PMF.pure true]

def continuationBest : Payoff (Fin 4) := ![1, 0, 0, 1]

def target : Payoff (Fin 4) := ![1, 0, 0, 1]

/-- An arbitrary active product row with the fourth player as sure anchor. -/
def rootOf (first second third : PMF Bool) : Fin 4 → PMF Bool :=
  ![first, second, third, PMF.pure true]

@[simp] theorem halfCoin_true : (halfCoin true).toReal = 1 / 2 := by
  simp [halfCoin]

@[simp] theorem halfCoin_false : (halfCoin false).toReal = 1 / 2 := by
  simp [halfCoin]
  norm_num

@[simp] theorem root_anchor : root 3 = PMF.pure true := by
  rfl

theorem root_eq_rootOf : root = rootOf halfCoin halfCoin halfCoin := by
  rfl

theorem root_hasSureQuitter : QuittingRootHasSureQuitter root := by
  exact ⟨3, root_anchor⟩

theorem reward_abs_le_two (terminal : {S : Finset (Fin 4) // S.Nonempty})
    (who : Fin 4) : |reward terminal who| ≤ 2 := by
  fin_cases who <;> simp [reward] <;> split_ifs <;> norm_num

theorem singleton_reward (who : Fin 4) :
    reward (quittingSingletonTerminal who) who = ![1, -1, -1, 1] who := by
  fin_cases who <;> simp [reward, quittingSingletonTerminal]

theorem alwaysContinue_bestResponse :
    quittingContinuationBestResponse reward
      (quittingAlwaysContinueProfile reward) = continuationBest := by
  funext who
  unfold quittingContinuationBestResponse
  rw [quittingContinuationBestResponseValue_quittingAlwaysContinueProfile]
  rw [singleton_reward]
  fin_cases who <;> norm_num [continuationBest]

theorem endpointDifference_zero
    (first second third : PMF Bool) (tail : Payoff (Fin 4)) :
    quittingRootEndpointDifference reward tail (rootOf first second third) 0 =
      1 - 2 * (third true).toReal := by
  unfold quittingRootEndpointDifference quittingRootQuitPayoff
    quittingRootContinuePayoff quittingRootExpectedPayoff
  rw [Math.PMFProduct.expect_pmfPi_fin4, Math.PMFProduct.expect_pmfPi_fin4]
  simp [rootOf, quittingRootPayoff, quittingQuitters, reward]
  rw [expect_eq_sum, Fintype.sum_bool]
  simp
  linarith

theorem endpointDifference_one
    (first second third : PMF Bool) (tail : Payoff (Fin 4)) :
    quittingRootEndpointDifference reward tail (rootOf first second third) 1 =
      2 * (first true).toReal - 1 := by
  have hsum := quittingRoot_continueProbability_add_quitProbability
    (rootOf first second third) 0
  simp [rootOf] at hsum
  unfold quittingRootEndpointDifference quittingRootQuitPayoff
    quittingRootContinuePayoff quittingRootExpectedPayoff
  rw [Math.PMFProduct.expect_pmfPi_fin4, Math.PMFProduct.expect_pmfPi_fin4]
  simp [rootOf, quittingRootPayoff, quittingQuitters, reward]
  rw [expect_eq_sum, Fintype.sum_bool]
  simp
  linarith

theorem endpointDifference_two
    (first second third : PMF Bool) (tail : Payoff (Fin 4)) :
    quittingRootEndpointDifference reward tail (rootOf first second third) 2 =
      2 * (second true).toReal - 1 := by
  have hsum := quittingRoot_continueProbability_add_quitProbability
    (rootOf first second third) 1
  simp [rootOf] at hsum
  unfold quittingRootEndpointDifference quittingRootQuitPayoff
    quittingRootContinuePayoff quittingRootExpectedPayoff
  rw [Math.PMFProduct.expect_pmfPi_fin4, Math.PMFProduct.expect_pmfPi_fin4]
  simp [rootOf, quittingRootPayoff, quittingQuitters, reward]
  rw [expect_eq_sum, Fintype.sum_bool]
  simp
  linarith

private theorem probability_eq_one_of_positive_gap {probability gap : ℝ}
    (hupper : probability ≤ 1) (hgap : 0 < gap)
    (hquit : (1 - probability) * gap ≤ 0) : probability = 1 := by
  by_contra hne
  have hstrict : probability < 1 := lt_of_le_of_ne hupper hne
  have hpositive := mul_pos (sub_pos.mpr hstrict) hgap
  linarith

private theorem probability_eq_zero_of_negative_gap {probability gap : ℝ}
    (hlower : 0 ≤ probability) (hgap : gap < 0)
    (hcontinue : 0 ≤ probability * gap) : probability = 0 := by
  by_contra hne
  have hstrict : 0 < probability := lt_of_le_of_ne hlower (Ne.symm hne)
  have hnegative := mul_neg_of_pos_of_neg hstrict hgap
  linarith

/-- Every Nash point of the finite active game is the fair vector, including
all possible boundary points. Interiority is derived rather than assumed. -/
theorem unique_active_probabilities_of_endpoint_products
    (first second third : ℝ)
    (hfirst : 0 ≤ first ∧ first ≤ 1) (hsecond : 0 ≤ second ∧ second ≤ 1)
    (hthird : 0 ≤ third ∧ third ≤ 1)
    (hzero : (1 - first) * (1 - 2 * third) ≤ 0 ∧
      0 ≤ first * (1 - 2 * third))
    (hone : (1 - second) * (2 * first - 1) ≤ 0 ∧
      0 ≤ second * (2 * first - 1))
    (htwo : (1 - third) * (2 * second - 1) ≤ 0 ∧
      0 ≤ third * (2 * second - 1)) :
    first = 1 / 2 ∧ second = 1 / 2 ∧ third = 1 / 2 := by
  have hfirstHalf : first = 1 / 2 := by
    rcases lt_trichotomy first (1 / 2) with hlt | heq | hgt
    · have hsecondZero : second = 0 :=
        probability_eq_zero_of_negative_gap hsecond.1 (by linarith) hone.2
      have hthirdZero : third = 0 :=
        probability_eq_zero_of_negative_gap hthird.1 (by linarith) htwo.2
      have hfirstOne : first = 1 :=
        probability_eq_one_of_positive_gap hfirst.2 (by linarith) hzero.1
      linarith
    · exact heq
    · have hsecondOne : second = 1 :=
        probability_eq_one_of_positive_gap hsecond.2 (by linarith) hone.1
      have hthirdOne : third = 1 :=
        probability_eq_one_of_positive_gap hthird.2 (by linarith) htwo.1
      have hfirstZero : first = 0 :=
        probability_eq_zero_of_negative_gap hfirst.1 (by linarith) hzero.2
      linarith
  have hsecondHalf : second = 1 / 2 := by
    rcases lt_trichotomy second (1 / 2) with hlt | heq | hgt
    · have hthirdZero : third = 0 :=
        probability_eq_zero_of_negative_gap hthird.1 (by linarith) htwo.2
      have hfirstOne : first = 1 :=
        probability_eq_one_of_positive_gap hfirst.2 (by linarith) hzero.1
      linarith
    · exact heq
    · have hthirdOne : third = 1 :=
        probability_eq_one_of_positive_gap hthird.2 (by linarith) htwo.1
      have hfirstZero : first = 0 :=
        probability_eq_zero_of_negative_gap hfirst.1 (by linarith) hzero.2
      linarith
  refine ⟨hfirstHalf, hsecondHalf, ?_⟩
  rw [hfirstHalf] at hzero
  nlinarith [hzero.1, hzero.2]

/-- Pure Quit and Continue inequalities for the displayed active payoffs
force the fair vector, without a complete-mixing hypothesis. -/
theorem unique_active_probabilities_of_endpoint_inequalities
    (first second third : ℝ)
    (hfirst : 0 ≤ first ∧ first ≤ 1) (hsecond : 0 ≤ second ∧ second ≤ 1)
    (hthird : 0 ≤ third ∧ third ≤ 1)
    (hquitZero : 1 ≤ first + 2 * (1 - first) * third)
    (hcontinueZero : 2 * third ≤ first + 2 * (1 - first) * third)
    (hquitOne : 2 * first - 1 ≤ second * (2 * first - 1))
    (hcontinueOne : 0 ≤ second * (2 * first - 1))
    (hquitTwo : 2 * second - 1 ≤ third * (2 * second - 1))
    (hcontinueTwo : 0 ≤ third * (2 * second - 1)) :
    first = 1 / 2 ∧ second = 1 / 2 ∧ third = 1 / 2 := by
  apply unique_active_probabilities_of_endpoint_products first second third
    hfirst hsecond hthird
  · constructor <;> nlinarith
  · exact ⟨by nlinarith, hcontinueOne⟩
  · exact ⟨by nlinarith, hcontinueTwo⟩

/-- Any exact root equilibrium has the three fair active probabilities. This
uses the actual endpoint formulas and permits pure active marginals as input. -/
theorem unique_active_probabilities
    (first second third : PMF Bool) (tail : Payoff (Fin 4))
    (hnash : IsεQuittingRootNash reward tail 0 (rootOf first second third)) :
    (first true).toReal = 1 / 2 ∧
      (second true).toReal = 1 / 2 ∧ (third true).toReal = 1 / 2 := by
  have hendpoint :=
    (isZeroQuittingRootEndpointNash_iff_isZeroQuittingRootNash
      reward tail (rootOf first second third)).2 hnash
  have hzero := hendpoint 0
  have hone := hendpoint 1
  have htwo := hendpoint 2
  rw [endpointDifference_zero] at hzero
  rw [endpointDifference_one] at hone
  rw [endpointDifference_two] at htwo
  have hfirstSum := quittingRoot_continueProbability_add_quitProbability
    (rootOf first second third) 0
  have hsecondSum := quittingRoot_continueProbability_add_quitProbability
    (rootOf first second third) 1
  have hthirdSum := quittingRoot_continueProbability_add_quitProbability
    (rootOf first second third) 2
  simp [rootOf] at hzero hone htwo hfirstSum hsecondSum hthirdSum
  have hbounds (law : PMF Bool) : 0 ≤ (law true).toReal ∧ (law true).toReal ≤ 1 := by
    refine ⟨ENNReal.toReal_nonneg, ?_⟩
    simpa only [ENNReal.toReal_one] using
      ENNReal.toReal_mono ENNReal.one_ne_top (PMF.coe_le_one law true)
  apply unique_active_probabilities_of_endpoint_products
    (first true).toReal (second true).toReal (third true).toReal
    (hbounds first) (hbounds second) (hbounds third)
  · constructor <;> nlinarith [hzero.1, hzero.2]
  · constructor <;> nlinarith [hone.1, hone.2]
  · constructor <;> nlinarith [htwo.1, htwo.2]

/-- Any completely mixed exact equilibrium of the active finite game has the
three fair quitting probabilities. -/
theorem unique_completelyMixed_active_probabilities
    (first second third : PMF Bool) (tail : Payoff (Fin 4))
    (hfirstContinue : 0 < (first false).toReal)
    (hfirstQuit : 0 < (first true).toReal)
    (hsecondContinue : 0 < (second false).toReal)
    (hsecondQuit : 0 < (second true).toReal)
    (hthirdContinue : 0 < (third false).toReal)
    (hthirdQuit : 0 < (third true).toReal)
    (hnash : IsεQuittingRootNash reward tail 0 (rootOf first second third)) :
    (first true).toReal = 1 / 2 ∧
      (second true).toReal = 1 / 2 ∧
      (third true).toReal = 1 / 2 := by
  have hendpoint : IsεQuittingRootEndpointNash reward tail 0
      (rootOf first second third) :=
    (isZeroQuittingRootEndpointNash_iff_isZeroQuittingRootNash
      reward tail (rootOf first second third)).2 hnash
  have hzero := quittingRootEndpointDifference_eq_zero_of_both_probabilities_pos
    reward tail (rootOf first second third) 0 hendpoint hfirstContinue hfirstQuit
  have hone := quittingRootEndpointDifference_eq_zero_of_both_probabilities_pos
    reward tail (rootOf first second third) 1 hendpoint hsecondContinue hsecondQuit
  have htwo := quittingRootEndpointDifference_eq_zero_of_both_probabilities_pos
    reward tail (rootOf first second third) 2 hendpoint hthirdContinue hthirdQuit
  rw [endpointDifference_zero] at hzero
  rw [endpointDifference_one] at hone
  rw [endpointDifference_two] at htwo
  constructor
  · linarith
  constructor <;> linarith

theorem root_endpointDifference (who : Fin 4) :
    quittingRootEndpointDifference reward continuationBest root who =
      ![0, 0, 0, 7 / 8] who := by
  rw [root_eq_rootOf]
  fin_cases who
  · simpa using endpointDifference_zero halfCoin halfCoin halfCoin continuationBest
  · simpa using endpointDifference_one halfCoin halfCoin halfCoin continuationBest
  · simpa using endpointDifference_two halfCoin halfCoin halfCoin continuationBest
  · unfold quittingRootEndpointDifference quittingRootQuitPayoff
      quittingRootContinuePayoff quittingRootExpectedPayoff
    rw [Math.PMFProduct.expect_pmfPi_fin4, Math.PMFProduct.expect_pmfPi_fin4]
    simp [rootOf, halfCoin, continuationBest, quittingRootPayoff, quittingQuitters, reward]
    repeat' rw [expect_eq_sum, Fintype.sum_bool]
    simp
    norm_num

theorem root_exactNash : IsεQuittingRootNash reward continuationBest 0 root := by
  rw [isZeroQuittingRootNash_iff_coordinateNashDefect_eq_zero]
  intro who
  rw [quittingRootCoordinateNashDefect_eq_actionProbability_mul_posPart,
    root_endpointDifference]
  fin_cases who <;> norm_num [root, halfCoin]

/-- The actual independent-clock profile plays the center root at date zero
and then Continue forever, equivalently Never for every surviving player. -/
def profile : (quittingGame reward).BehaviorProfile :=
  quittingOneDateThenNeverProfile reward root

theorem root_successor_zeroTail :
    quittingRootSuccessorPayoff reward 0 root = target := by
  funext who
  unfold quittingRootSuccessorPayoff quittingRootExpectedPayoff
  rw [Math.PMFProduct.expect_pmfPi_fin4]
  fin_cases who
  · simp [root, halfCoin, target, quittingRootPayoff, quittingQuitters, reward]
    repeat' rw [expect_eq_sum, Fintype.sum_bool]
    simp
  · simp [root, halfCoin, target, quittingRootPayoff, quittingQuitters, reward]
    repeat' rw [expect_eq_sum, Fintype.sum_bool]
    simp
    norm_num
  · simp [root, halfCoin, target, quittingRootPayoff, quittingQuitters, reward]
    repeat' rw [expect_eq_sum, Fintype.sum_bool]
    simp
    norm_num
  · simp [root, halfCoin, target, quittingRootPayoff, quittingQuitters, reward]

theorem profile_terminalPayoff :
    quittingTerminalPayoff reward profile = target := by
  funext who
  unfold profile quittingOneDateThenNeverProfile
  rw [quittingTerminalPayoff_rootThenContinuation_eq]
  simp_rw [quittingTerminalPayoff_quittingAlwaysContinue]
  exact congrFun root_successor_zeroTail who

/-- The literal one-date independent-clock center profile is exact terminal
Nash against every behavioral unilateral deviation. -/
theorem profile_exactTerminalNash :
    (quittingGame reward).IsεAsymptoticNash
      (quittingTerminalPayoff reward) 0 profile := by
  unfold profile quittingOneDateThenNeverProfile
  apply isεAsymptoticNash_quittingRootThenContinuation_of_isεQuittingRootNash
  · exact root_hasSureQuitter
  · rw [alwaysContinue_bestResponse]
    exact root_exactNash

/-- The displayed center payoff is a fixed uniform-equilibrium payoff. -/
theorem target_isUniformEquilibriumPayoff :
    (quittingGame reward).IsUniformEquilibriumPayoff none target := by
  rw [← profile_terminalPayoff]
  exact quittingGame_isUniformEquilibriumPayoff_of_terminalNash_exact
    reward profile profile_exactTerminalNash

end GameTheory.AdaptiveChildCenter
