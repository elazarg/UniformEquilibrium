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

open Math.Probability Math.PMFProduct Math.Probability.DiscreteHazard

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
