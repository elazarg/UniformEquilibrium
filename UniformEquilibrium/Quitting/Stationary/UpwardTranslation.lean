import UniformEquilibrium.Quitting.Root.UpwardTranslation
import UniformEquilibrium.Quitting.Stationary.BestResponse
import UniformEquilibrium.Quitting.Stationary.MinMax
import UniformEquilibrium.Quitting.Stationary.Root
import UniformEquilibrium.ProofView.Concepts.Stochastic.Models.Quitting.SimpleBranches

/-! # Absorption-weighted upward translation of stationary equilibrium payoffs

The annotation is the literal stationary terminal payoff plus twice the
equilibrium error. Its Bellman residual is exactly twice that error times
absorption, and its ordinary root regret satisfies the same upper bound.
-/

noncomputable section

namespace GameTheory

open StochasticGame Math.Probability

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The literal terminal payoff vector of one stationary product root. -/
def quittingStationaryPayoffVector
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool) : Payoff ι :=
  fun who ↦ quittingTerminalPayoff reward (quittingStationaryProfile reward root) who

omit [DecidableEq ι] in
theorem quittingStationaryPayoffVector_fixedPoint
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool) :
    quittingStationaryPayoffVector reward root =
      quittingRootSuccessorPayoff reward (quittingStationaryPayoffVector reward root) root := by
  funext who
  exact quittingTerminalPayoff_stationary_eq_rootExpectedPayoff reward root who

/-- Every stationary terminal approximate equilibrium lies within its error
above the behavioral punishment floor. -/
theorem punishmentValue_le_stationaryPayoff_add
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool) {error : ℝ}
    (hnash : (quittingGame reward).IsεAsymptoticNash
      (quittingTerminalPayoff reward) error (quittingStationaryProfile reward root))
    (who : ι) :
    quittingPunishmentValue reward who ≤
      quittingStationaryPayoffVector reward root who + error := by
  calc
    quittingPunishmentValue reward who ≤
        quittingBestReplyValue reward (quittingStationaryProfile reward root) who :=
      quittingPunishmentValue_le reward who _
    _ ≤ quittingStationaryPayoffVector reward root who + error := by
      apply quittingBestReplyValue_le
      intro deviation
      exact hnash who deviation

/-- The literal Never response sharpens the stationary Continue endpoint gap
by the opponents' one-stage absorption probability. -/
theorem quittingRootContinuePayoff_sub_stationaryPayoff_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool) {error : ℝ}
    (hnash : (quittingGame reward).IsεAsymptoticNash
      (quittingTerminalPayoff reward) error (quittingStationaryProfile reward root))
    (who : ι) :
    quittingRootContinuePayoff reward (quittingStationaryPayoffVector reward root)
        root who - quittingStationaryPayoffVector reward root who ≤
      error * (1 - quittingStationaryFixedOpponentsContinueMass root who) := by
  let value := quittingStationaryPayoffVector reward root
  let continueReward := quittingStationaryFixedOpponentsContinueReward reward root who
  let continueMass := quittingStationaryFixedOpponentsContinueMass root who
  have hmass0 : 0 ≤ continueMass :=
    quittingStationaryFixedOpponentsContinueMass_nonneg root who
  have hmass1 : continueMass ≤ 1 :=
    quittingStationaryFixedOpponentsContinueMass_le_one root who
  have hcontinueEq :
      quittingRootContinuePayoff reward value root who =
        continueReward + continueMass * value who := by
    simpa only [value, continueReward, continueMass,
      quittingStationaryPayoffVector,
      quittingStationaryFixedOpponentsContinueReward,
      quittingStationaryFixedOpponentsContinueMass] using
      (quittingRootContinuePayoff_eq_fixedOpponents
        reward (fun _ ↦ root) who value 0)
  rcases hmass1.eq_or_lt with hmassEq | hcontracts
  · have hrewardZero : continueReward = 0 := by
      apply quittingStationaryFixedOpponentsContinueReward_eq_zero_of_mass_eq_one
      exact hmassEq
    have hmassActual : quittingStationaryFixedOpponentsContinueMass root who = 1 :=
      hmassEq
    rw [hcontinueEq, hrewardZero, hmassEq, hmassActual]
    simp [value]
  · have hnever := hnash who (quittingPureTimeBehaviorStrategy reward who none)
    rw [quittingTerminalPayoff_update_pureTimeBehaviorStrategy,
      quittingProfileLiveRoot_stationary,
      quittingRootSequencePureTimeTerminalValue_const
        reward root who hcontracts none] at hnever
    change quittingStationaryNeverValue continueReward continueMass ≤
      value who + error at hnever
    have hbalance :=
      quittingStationaryNeverValue_balance continueReward continueMass hcontracts
    rw [hcontinueEq]
    nlinarith

/-- Raising every continuation coordinate has the expected affine effect on
the pure-Continue endpoint. -/
theorem quittingRootContinuePayoff_upwardTranslate
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : Payoff ι) (root : ι → PMF Bool) (who : ι) (error : ℝ) :
    quittingRootContinuePayoff reward (quittingPayoffUpwardTranslate tail error)
        root who =
      quittingRootContinuePayoff reward tail root who +
        quittingRootOpponentContinueMass root who * (2 * error) := by
  have hcongr :
      quittingRootContinuePayoff reward (quittingPayoffUpwardTranslate tail error)
          root who =
        quittingRootContinuePayoff reward
          (Function.update tail who (tail who + 2 * error)) root who := by
    apply quittingRootExpectedPayoff_continuation_congr
    simp [quittingPayoffUpwardTranslate]
  rw [hcongr, quittingRootContinuePayoff_update_add]

omit [DecidableEq ι] in
/-- The constant annotation above a stationary payoff has exactly the claimed
absorption-weighted Bellman residual. -/
theorem quittingStationaryUpwardTranslate_sub_successor_eq
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool) (who : ι) (error : ℝ) :
    quittingPayoffUpwardTranslate (quittingStationaryPayoffVector reward root) error who -
        quittingRootSuccessorPayoff reward
          (quittingPayoffUpwardTranslate
            (quittingStationaryPayoffVector reward root) error) root who =
      2 * error * quittingRootAbsorptionMass root := by
  apply quittingPayoffUpwardTranslate_sub_successor_eq
  exact congrFun (quittingStationaryPayoffVector_fixedPoint reward root) who

/-- Translating a stationary approximate-equilibrium payoff upward by twice
its error gives root regret at most two errors per unit absorption. -/
theorem quittingRootCoordinateNashDefect_stationaryUpwardTranslate_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool) {error : ℝ} (herror : 0 ≤ error)
    (hnash : (quittingGame reward).IsεAsymptoticNash
      (quittingTerminalPayoff reward) error (quittingStationaryProfile reward root))
    (who : ι) :
    quittingRootCoordinateNashDefect reward
        (quittingPayoffUpwardTranslate
          (quittingStationaryPayoffVector reward root) error) root who ≤
      2 * error * quittingRootAbsorptionMass root := by
  let value := quittingStationaryPayoffVector reward root
  let translated := quittingPayoffUpwardTranslate value error
  let absorption := quittingRootAbsorptionMass root
  let opponentContinue := quittingRootOpponentContinueMass root who
  have habsorption0 : 0 ≤ absorption := quittingRootAbsorptionMass_nonneg root
  have habsorption1 : absorption ≤ 1 := by
    have := quittingStationaryContinueMass_nonneg root
    dsimp only [absorption, quittingRootAbsorptionMass]
    linarith
  have hopponent0 : 0 ≤ opponentContinue :=
    quittingRootOpponentContinueMass_nonneg root who
  have hopponent1 : opponentContinue ≤ 1 :=
    quittingRootOpponentContinueMass_le_one root who
  have hfixed : value = quittingRootSuccessorPayoff reward value root :=
    quittingStationaryPayoffVector_fixedPoint reward root
  have hrootNash : IsεQuittingRootNash reward value error root := by
    change IsεQuittingRootNash reward
      (fun player ↦ quittingTerminalPayoff reward
        (quittingStationaryProfile reward root) player) error root
    exact isεQuittingRootNash_of_isεAsymptoticNash_stationary
      reward root error hnash
  have hquit : quittingRootQuitPayoff reward value root who ≤ value who + error := by
    have := quittingRootQuitPayoff_le_successor_add_of_isεNash
      reward value error root who hrootNash
    rw [← congrFun hfixed who] at this
    exact this
  have hcontinue :
      quittingRootContinuePayoff reward value root who - value who ≤
        error * (1 - opponentContinue) := by
    have := quittingRootContinuePayoff_sub_stationaryPayoff_le
      reward root hnash who
    change quittingRootContinuePayoff reward value root who - value who ≤
      error * (1 - opponentContinue) at this
    exact this
  have hresidual : translated who -
      quittingRootSuccessorPayoff reward translated root who =
        2 * error * absorption := by
    simpa only [value, translated, absorption] using
      quittingStationaryUpwardTranslate_sub_successor_eq reward root who error
  have hquitTranslated :
      quittingRootQuitPayoff reward translated root who =
        quittingRootQuitPayoff reward value root who :=
    quittingRootQuitPayoff_continuation_invariant reward translated value root who
  have hcontinueTranslated :
      quittingRootContinuePayoff reward translated root who =
        quittingRootContinuePayoff reward value root who + opponentContinue * (2 * error) := by
    simpa only [translated, opponentContinue] using
      quittingRootContinuePayoff_upwardTranslate reward value root who error
  unfold quittingRootCoordinateNashDefect
  apply sub_le_iff_le_add.mpr
  apply max_le
  · rw [hquitTranslated]
    dsimp only [translated, quittingPayoffUpwardTranslate] at hresidual ⊢
    nlinarith
  · rw [hcontinueTranslated]
    dsimp only [translated, quittingPayoffUpwardTranslate] at hresidual ⊢
    nlinarith

/-- The translated stationary annotation lies one full stationary error above
the punishment floor. -/
theorem punishmentValue_add_le_stationaryUpwardTranslate
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool) {error : ℝ}
    (hnash : (quittingGame reward).IsεAsymptoticNash
      (quittingTerminalPayoff reward) error (quittingStationaryProfile reward root))
    (who : ι) :
    quittingPunishmentValue reward who + error ≤
      quittingPayoffUpwardTranslate
        (quittingStationaryPayoffVector reward root) error who := by
  have hfloor := punishmentValue_le_stationaryPayoff_add reward root hnash who
  dsimp only [quittingPayoffUpwardTranslate]
  linarith

omit [DecidableEq ι] in
/-- A reward bound and an error at most one put the translated stationary
annotation in the enlarged coordinate box. -/
theorem abs_stationaryUpwardTranslate_le_rewardBound_add_two
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool) {rewardBound error : ℝ}
    (hreward : ∀ terminal player, |reward terminal player| ≤ rewardBound)
    (herror : 0 ≤ error) (herrorMax : error ≤ 1) (who : ι) :
    |quittingPayoffUpwardTranslate
        (quittingStationaryPayoffVector reward root) error who| ≤ rewardBound + 2 := by
  have hvalue := abs_quittingTerminalPayoff_le reward
    (quittingStationaryProfile reward root) who hreward
  rw [abs_le] at hvalue ⊢
  dsimp only [quittingPayoffUpwardTranslate, quittingStationaryPayoffVector]
  constructor <;> nlinarith

/-- A stationary approximate equilibrium whose error is below one positive
singleton payoff must absorb with positive probability. -/
theorem quittingRootAbsorptionMass_pos_of_stationaryNash_of_singleton
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool) {error : ℝ} (herror : 0 ≤ error) (who : ι)
    (hsingleton : error < reward (quittingSingletonTerminal who) who)
    (hnash : (quittingGame reward).IsεAsymptoticNash
      (quittingTerminalPayoff reward) error (quittingStationaryProfile reward root)) :
    0 < quittingRootAbsorptionMass root := by
  have habsorption0 : 0 ≤ quittingRootAbsorptionMass root :=
    quittingRootAbsorptionMass_nonneg root
  apply lt_of_le_of_ne habsorption0
  intro habsorptionEq
  have habsorptionZero : quittingRootAbsorptionMass root = 0 :=
    habsorptionEq.symm
  have hmass : quittingStationaryContinueMass root = 1 := by
    unfold quittingRootAbsorptionMass at habsorptionZero
    linarith
  have hroot : root = quittingAllContinueRoot := by
    funext player
    simpa [quittingAllContinueRoot] using
      (eq_pure_false_of_quittingStationaryContinueMass_eq_one hmass player)
  have hprofile : quittingStationaryProfile reward root =
      quittingAlwaysContinueProfile reward := by
    rw [hroot]
    rfl
  rw [hprofile] at hnash
  have hcriterion :=
    (isεAsymptoticNash_quittingAlwaysContinue_iff reward herror).mp hnash who
  linarith

end GameTheory
