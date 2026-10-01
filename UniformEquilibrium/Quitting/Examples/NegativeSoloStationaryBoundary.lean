import MathUE.LinearProgramming.R0Degree
import UniformEquilibrium.Quitting.Examples.SignedTwoPlayerExactNashNonattainment
import UniformEquilibrium.Quitting.Stationary.CompleteBehavioralCap
import UniformEquilibrium.Quitting.Stationary.MinMax
import UniformEquilibrium.Quitting.Stationary.ResponseInvariantQuotient
import UniformEquilibrium.Quitting.Terminal.TerminalExploitability
import UniformEquilibrium.Quitting.Punishment.SoloQuitterEquilibrium
import UniformEquilibrium.Quitting.Classification.LCP.QuittingRewardAdapter

/-! # A negative solo-owner stationary boundary

The reward is the existing signed two-player table at parameter one half.
All caps below are suprema over complete behavioral deviations, including Never.
The Bellman root is not asserted to be a terminal equilibrium.
-/

noncomputable section

namespace GameTheory.NegativeSoloStationaryBoundary

open _root_.Math.ProbabilityMassFunction
open _root_.Math.Probability.DiscreteHazard
open _root_.Math.LinearProgramming QuittingLCPClassification

abbrev reward := SignedTwoPlayerExactNashNonattainment.reward (1 / 2)

/-- The discrete partition retains each original player's response test. -/
theorem responseInvariant_discrete :
    QuittingResponseInvariantOnUnitCube reward (fun who : Fin 2 => who) := by
  intro point _ first second hsame
  cases hsame
  rfl

def quarterCoin : PMF Bool := bernoulliBool (1 / 4) (by norm_num) (by norm_num)

def root (rate : ℝ) (hnonneg : 0 ≤ rate) (hunit : rate ≤ 1) : Fin 2 → PMF Bool :=
  ![bernoulliBool rate hnonneg hunit, quarterCoin]

def profile (rate : ℝ) (hnonneg : 0 ≤ rate) (hunit : rate ≤ 1) :
    (quittingGame reward).BehaviorProfile :=
  quittingStationaryProfile reward (root rate hnonneg hunit)

def value : Payoff (Fin 2) := ![1 / 2, -1 / 2]

private theorem solo_values :
    quittingSoloReward reward 0 0 = 1 ∧ quittingSoloReward reward 0 1 = -1 ∧
      quittingSoloReward reward 1 0 = 1 / 2 ∧
      quittingSoloReward reward 1 1 = -1 / 2 := by
  norm_num [quittingSoloReward, reward, SignedTwoPlayerExactNashNonattainment.reward,
    quittingSingletonTerminal]

private theorem collision_values :
    quittingSingletonCollisionReward reward 1 0 = -1 ∧
      quittingSingletonCollisionReward reward 0 1 = 1 := by
  have hzero : ({0, 1} : Finset (Fin 2)) ≠ {0} := by decide
  have hone : ({0, 1} : Finset (Fin 2)) ≠ {1} := by decide
  have hzero' : ({1, 0} : Finset (Fin 2)) ≠ {0} := by decide
  have hone' : ({1, 0} : Finset (Fin 2)) ≠ {1} := by decide
  norm_num [quittingSingletonCollisionReward, reward,
    SignedTwoPlayerExactNashNonattainment.reward, hzero, hone, hzero', hone']

private theorem update_zero (rate : ℝ) (hnonneg : 0 ≤ rate) (hunit : rate ≤ 1)
    (marginal : PMF Bool) :
    Function.update (root rate hnonneg hunit) 0 marginal =
      Function.update (quittingSoloStationaryRoot 1 quarterCoin) 0 marginal := by
  funext who
  fin_cases who <;> rfl

private theorem update_one (rate : ℝ) (hnonneg : 0 ≤ rate) (hunit : rate ≤ 1)
    (marginal : PMF Bool) :
    Function.update (root rate hnonneg hunit) 1 marginal =
      Function.update
        (quittingSoloStationaryRoot 0 (bernoulliBool rate hnonneg hunit)) 1 marginal := by
  funext who
  fin_cases who <;> rfl

theorem continueMass_zero (rate : ℝ) (hnonneg : 0 ≤ rate) (hunit : rate ≤ 1) :
    quittingStationaryFixedOpponentsContinueMass (root rate hnonneg hunit) 0 = 3 / 4 := by
  change quittingStationaryContinueMass
    (Function.update (root rate hnonneg hunit) 0 (PMF.pure false)) = 3 / 4
  rw [update_zero]
  change quittingStationaryFixedOpponentsContinueMass
    (quittingSoloStationaryRoot 1 quarterCoin) 0 = 3 / 4
  rw [quittingStationaryFixedOpponentsContinueMass_solo_other (by decide)]
  norm_num [quarterCoin]

theorem continueMass_one (rate : ℝ) (hnonneg : 0 ≤ rate) (hunit : rate ≤ 1) :
    quittingStationaryFixedOpponentsContinueMass (root rate hnonneg hunit) 1 = 1 - rate := by
  change quittingStationaryContinueMass
    (Function.update (root rate hnonneg hunit) 1 (PMF.pure false)) = 1 - rate
  rw [update_one]
  change quittingStationaryFixedOpponentsContinueMass
    (quittingSoloStationaryRoot 0 (bernoulliBool rate hnonneg hunit)) 1 = 1 - rate
  rw [quittingStationaryFixedOpponentsContinueMass_solo_other (by decide)]
  exact bernoulliBool_false_toReal rate hnonneg hunit

theorem quitValue_zero (rate : ℝ) (hnonneg : 0 ≤ rate) (hunit : rate ≤ 1) :
    quittingStationaryFixedOpponentsQuitValue reward (root rate hnonneg hunit) 0 = 1 / 2 := by
  change quittingRootAbsorbingContribution reward
    (Function.update (root rate hnonneg hunit) 0 (PMF.pure true)) 0 = 1 / 2
  rw [update_zero]
  change quittingStationaryFixedOpponentsQuitValue reward
    (quittingSoloStationaryRoot 1 quarterCoin) 0 = 1 / 2
  rw [quittingStationaryFixedOpponentsQuitValue_solo_other_eq_mix reward (by decide),
    solo_values.1, collision_values.1]
  norm_num [quarterCoin]

theorem quitValue_one (rate : ℝ) (hnonneg : 0 ≤ rate) (hunit : rate ≤ 1) :
    quittingStationaryFixedOpponentsQuitValue reward (root rate hnonneg hunit) 1 =
      -1 / 2 + 3 * rate / 2 := by
  change quittingRootAbsorbingContribution reward
    (Function.update (root rate hnonneg hunit) 1 (PMF.pure true)) 1 =
      -1 / 2 + 3 * rate / 2
  rw [update_one]
  change quittingStationaryFixedOpponentsQuitValue reward
    (quittingSoloStationaryRoot 0 (bernoulliBool rate hnonneg hunit)) 1 =
      -1 / 2 + 3 * rate / 2
  rw [quittingStationaryFixedOpponentsQuitValue_solo_other_eq_mix reward (by decide),
    solo_values.2.2.2, collision_values.2]
  simp only [bernoulliBool_false_toReal, bernoulliBool_true_toReal]
  ring

theorem continueReward_zero (rate : ℝ) (hnonneg : 0 ≤ rate) (hunit : rate ≤ 1) :
    quittingStationaryFixedOpponentsContinueReward reward (root rate hnonneg hunit) 0 =
      1 / 8 := by
  change quittingRootAbsorbingContribution reward
    (Function.update (root rate hnonneg hunit) 0 (PMF.pure false)) 0 = 1 / 8
  rw [update_zero]
  change quittingStationaryFixedOpponentsContinueReward reward
    (quittingSoloStationaryRoot 1 quarterCoin) 0 = 1 / 8
  rw [quittingStationaryFixedOpponentsContinueReward_solo_other reward (by decide),
    solo_values.2.2.1]
  norm_num [quarterCoin]

theorem continueReward_one (rate : ℝ) (hnonneg : 0 ≤ rate) (hunit : rate ≤ 1) :
    quittingStationaryFixedOpponentsContinueReward reward (root rate hnonneg hunit) 1 =
      -rate := by
  change quittingRootAbsorbingContribution reward
    (Function.update (root rate hnonneg hunit) 1 (PMF.pure false)) 1 = -rate
  rw [update_one]
  change quittingStationaryFixedOpponentsContinueReward reward
    (quittingSoloStationaryRoot 0 (bernoulliBool rate hnonneg hunit)) 1 = -rate
  rw [quittingStationaryFixedOpponentsContinueReward_solo_other reward (by decide),
    solo_values.2.1]
  simp

theorem jointContinueMass (rate : ℝ) (hnonneg : 0 ≤ rate) (hunit : rate ≤ 1) :
    quittingStationaryContinueMass (root rate hnonneg hunit) = (1 - rate) * (3 / 4) := by
  rw [quittingStationaryContinueMass_eq_prod_continueProbability, Fin.prod_univ_two]
  norm_num [root, quarterCoin]

theorem absorbs (rate : ℝ) (hnonneg : 0 ≤ rate) (hunit : rate ≤ 1) :
    quittingStationaryContinueMass (root rate hnonneg hunit) < 1 := by
  rw [jointContinueMass]
  linarith

private theorem quitEndpoint (rate : ℝ) (hnonneg : 0 ≤ rate) (hunit : rate ≤ 1)
    (tail : Payoff (Fin 2)) (who : Fin 2) :
    quittingRootQuitPayoff reward tail (root rate hnonneg hunit) who =
      quittingStationaryFixedOpponentsQuitValue reward (root rate hnonneg hunit) who := by
  exact quittingRootQuitPayoff_eq_fixedOpponentsQuitValue reward
    (fun _ => root rate hnonneg hunit) who tail 0

private theorem continueEndpoint (rate : ℝ) (hnonneg : 0 ≤ rate) (hunit : rate ≤ 1)
    (tail : Payoff (Fin 2)) (who : Fin 2) :
    quittingRootContinuePayoff reward tail (root rate hnonneg hunit) who =
      quittingStationaryFixedOpponentsContinueReward reward (root rate hnonneg hunit) who +
        quittingStationaryFixedOpponentsContinueMass (root rate hnonneg hunit) who *
          tail who := by
  exact quittingRootContinuePayoff_eq_fixedOpponents reward
    (fun _ => root rate hnonneg hunit) who tail 0

/-- The same actual payoff persists on the whole closed rate interval. -/
theorem terminalPayoff (rate : ℝ) (hnonneg : 0 ≤ rate) (hunit : rate ≤ 1) :
    quittingTerminalPayoff reward (profile rate hnonneg hunit) = value := by
  let actual := quittingTerminalPayoff reward (profile rate hnonneg hunit)
  have hbalance := quittingTerminalPayoff_stationary_eq_rootExpectedPayoff
    reward (root rate hnonneg hunit) 0
  have hmix := quittingRootSuccessorPayoff_eq_endpointMix
    reward actual (root rate hnonneg hunit) 0
  rw [quitEndpoint, continueEndpoint, quitValue_zero, continueReward_zero,
    continueMass_zero] at hmix
  have hscalar : actual 0 =
      rate * (1 / 2) + (1 - rate) * (1 / 8 + (3 / 4) * actual 0) := by
    simpa [actual, profile, quittingRootSuccessorPayoff, root] using hbalance.trans hmix
  have hpositive : 0 < 1 + 3 * rate := by positivity
  have hfactor : (1 + 3 * rate) * (actual 0 - 1 / 2) = 0 := by
    nlinarith [hscalar]
  have hzero : actual 0 = 1 / 2 := by
    have := (mul_eq_zero.mp hfactor).resolve_left hpositive.ne'
    linarith
  have hone := SignedTwoPlayerExactNashNonattainment.terminal_payoff_neg
    (1 / 2) (profile rate hnonneg hunit)
  funext who
  fin_cases who
  · exact hzero
  · change actual 1 = -1 / 2
    change actual 1 = -actual 0 at hone
    linarith

theorem bellmanValue (rate : ℝ) (hnonneg : 0 ≤ rate) (hunit : rate ≤ 1) :
    quittingRootSuccessorPayoff reward value (root rate hnonneg hunit) = value := by
  funext who
  have hbalance := quittingTerminalPayoff_stationary_eq_rootExpectedPayoff
    reward (root rate hnonneg hunit) who
  change quittingTerminalPayoff reward (profile rate hnonneg hunit) who =
    quittingRootSuccessorPayoff reward
      (quittingTerminalPayoff reward (profile rate hnonneg hunit))
      (root rate hnonneg hunit) who at hbalance
  rw [terminalPayoff] at hbalance
  exact hbalance.symm

/-- Both players' finite root endpoints agree at the negative solo boundary. -/
theorem boundary_endpointNash :
    IsεQuittingRootEndpointNash reward value 0 (root 0 (by norm_num) (by norm_num)) := by
  have hroot : root 0 (by norm_num) (by norm_num) =
      quittingSoloStationaryRoot 1 quarterCoin := by
    funext who
    fin_cases who
    · change bernoulliBool 0 (by norm_num) (by norm_num) = PMF.pure false
      apply eq_of_forall_toReal_eq
      intro action
      cases action <;> simp
    · rfl
  have hvalue : value = quittingSoloReward reward 1 := by
    funext who
    fin_cases who
    · exact solo_values.2.2.1.symm
    · exact solo_values.2.2.2.symm
  rw [hroot, hvalue, isεQuittingRootEndpointNash_soloStationaryRoot_iff]
  intro who hwho
  fin_cases who
  · change (quarterCoin false).toReal * quittingSoloReward reward 0 0 +
        (quarterCoin true).toReal * quittingSingletonCollisionReward reward 1 0 ≤
      quittingSoloReward reward 1 0
    rw [solo_values.1, collision_values.1, solo_values.2.2.1]
    norm_num [quarterCoin]
  · exact (hwho rfl).elim

theorem stationaryCap_zero (rate : ℝ) (hnonneg : 0 ≤ rate) (hunit : rate ≤ 1) :
    quittingStationaryUnilateralCap reward (root rate hnonneg hunit) 0 = 1 / 2 := by
  rw [quittingStationaryUnilateralCap_eq_max_div, quitValue_zero,
    continueReward_zero, continueMass_zero]
  norm_num

theorem stationaryCap_one (rate : ℝ) (hpositive : 0 < rate) (hunit : rate ≤ 1) :
    quittingStationaryUnilateralCap reward (root rate hpositive.le hunit) 1 =
      -1 / 2 + 3 * rate / 2 := by
  rw [quittingStationaryUnilateralCap_eq_max_div, quitValue_one,
    continueReward_one, continueMass_one]
  have hnever : -rate / (1 - (1 - rate)) = -1 := by
    rw [show 1 - (1 - rate) = rate by ring, neg_div_self hpositive.ne']
  rw [hnever, max_eq_left]
  linarith

/-- Complete caps, not merely root-game or stationary-deviation caps. -/
theorem fullCap_zero (rate : ℝ) (hnonneg : 0 ≤ rate) (hunit : rate ≤ 1) :
    quittingContinuationBestResponseValue reward (profile rate hnonneg hunit) 0 = 1 / 2 := by
  dsimp only [profile]
  rw [quittingContinuationBestResponseValue_stationary_eq_fullRateUnilateralCap]
  rw [quittingStationaryFullRateUnilateralCap_of_lt reward _ 0
    (by rw [continueMass_zero]; norm_num), stationaryCap_zero]

theorem fullCap_one_positive (rate : ℝ) (hpositive : 0 < rate) (hunit : rate ≤ 1) :
    quittingContinuationBestResponseValue reward (profile rate hpositive.le hunit) 1 =
      -1 / 2 + 3 * rate / 2 := by
  dsimp only [profile]
  rw [quittingContinuationBestResponseValue_stationary_eq_fullRateUnilateralCap]
  rw [quittingStationaryFullRateUnilateralCap_of_lt reward _ 1
    (by rw [continueMass_one]; linarith), stationaryCap_one rate hpositive hunit]

theorem fullCap_one_boundary :
    quittingContinuationBestResponseValue reward (profile 0 (by norm_num) (by norm_num)) 1 =
      0 := by
  dsimp only [profile]
  rw [quittingContinuationBestResponseValue_stationary_eq_fullRateUnilateralCap]
  rw [quittingStationaryFullRateUnilateralCap_of_eq_one reward _ 1
    (by rw [continueMass_one]; norm_num)]
  norm_num [reward, SignedTwoPlayerExactNashNonattainment.reward, quittingSingletonTerminal]

/-- The literal Never response at the boundary reaches zero and gains one half. -/
theorem boundary_never_gain :
    quittingTerminalPayoff reward
        (Function.update (profile 0 (by norm_num) (by norm_num)) 1
          (quittingAlwaysContinueStrategy reward 1)) 1 -
      quittingTerminalPayoff reward (profile 0 (by norm_num) (by norm_num)) 1 = 1 / 2 := by
  have hmass : quittingStationaryFixedOpponentsContinueMass
      (root 0 (by norm_num) (by norm_num)) 1 = 1 := by
    rw [continueMass_one]
    norm_num
  change quittingTerminalPayoff reward
      (Function.update
        (quittingStationaryProfile reward (root 0 (by norm_num) (by norm_num))) 1
        (quittingAlwaysContinueStrategy reward 1)) 1 -
      quittingTerminalPayoff reward (profile 0 (by norm_num) (by norm_num)) 1 = 1 / 2
  rw [update_stationaryProfile_eq_update_alwaysContinue_of_fixedMass_eq_one
    reward _ 1 _ hmass]
  have hstrategy : quittingAlwaysContinueStrategy reward 1 =
      quittingAlwaysContinueProfile reward 1 := rfl
  rw [hstrategy, Function.update_eq_self, quittingTerminalPayoff_quittingAlwaysContinue,
    terminalPayoff]
  norm_num [value]

theorem neverPayoff_one_positive (rate : ℝ) (hpositive : 0 < rate) (hunit : rate ≤ 1) :
    quittingTerminalPayoff reward
      (Function.update (profile rate hpositive.le hunit) 1
        (quittingPureTimeBehaviorStrategy reward 1 none)) 1 = -1 := by
  dsimp only [profile]
  rw [quittingTerminalPayoff_update_pureTimeBehaviorStrategy,
    quittingProfileLiveRoot_stationary,
    quittingRootSequencePureTimeTerminalValue_const reward _ 1
      (by rw [continueMass_one]; linarith) none]
  change quittingStationaryNeverValue
    (quittingStationaryFixedOpponentsContinueReward reward (root rate hpositive.le hunit) 1)
    (quittingStationaryFixedOpponentsContinueMass (root rate hpositive.le hunit) 1) = -1
  rw [quittingStationaryNeverValue, continueReward_one, continueMass_one,
    show 1 - (1 - rate) = rate by ring]
  exact neg_div_self hpositive.ne'

/-- Coordinate regret is discontinuous at the zero opponent clock. -/
theorem regret_one_positive (rate : ℝ) (hpositive : 0 < rate) (hunit : rate ≤ 1) :
    quittingContinuationBestResponseValue reward (profile rate hpositive.le hunit) 1 -
      quittingTerminalPayoff reward (profile rate hpositive.le hunit) 1 = 3 * rate / 2 := by
  rw [fullCap_one_positive rate hpositive hunit, terminalPayoff]
  simp only [value, Matrix.cons_val_one, Matrix.cons_val_zero]
  ring

theorem regret_one_boundary :
    quittingContinuationBestResponseValue reward (profile 0 (by norm_num) (by norm_num)) 1 -
      quittingTerminalPayoff reward (profile 0 (by norm_num) (by norm_num)) 1 = 1 / 2 := by
  rw [fullCap_one_boundary, terminalPayoff]
  norm_num [value]

def exploitability (rate : ℝ) (hnonneg : 0 ≤ rate) (hunit : rate ≤ 1) : ℝ :=
  quittingTerminalExploitability reward (profile rate hnonneg hunit)

private theorem exploitability_eq_max
    (rate : ℝ) (hnonneg : 0 ≤ rate) (hunit : rate ≤ 1) :
    exploitability rate hnonneg hunit =
      max
        (quittingContinuationBestResponseValue reward (profile rate hnonneg hunit) 0 -
          quittingTerminalPayoff reward (profile rate hnonneg hunit) 0)
        (quittingContinuationBestResponseValue reward (profile rate hnonneg hunit) 1 -
          quittingTerminalPayoff reward (profile rate hnonneg hunit) 1) := by
  unfold exploitability
  rw [quittingTerminalExploitability_eq_max_debt]
  refine le_antisymm (QuittingBoundaryHolonomy.finitePlayerMax_le ?_) ?_
  · intro who
    fin_cases who
    · exact le_max_left _ _
    · exact le_max_right _ _
  · exact max_le
      (QuittingBoundaryHolonomy.le_finitePlayerMax
        (fun who : Fin 2 => quittingTerminalDeviationDebt reward
          (profile rate hnonneg hunit) who) (0 : Fin 2))
      (QuittingBoundaryHolonomy.le_finitePlayerMax
        (fun who : Fin 2 => quittingTerminalDeviationDebt reward
          (profile rate hnonneg hunit) who) (1 : Fin 2))

theorem exploitability_positive (rate : ℝ) (hpositive : 0 < rate) (hunit : rate ≤ 1) :
    exploitability rate hpositive.le hunit = 3 * rate / 2 := by
  rw [exploitability_eq_max]
  rw [regret_one_positive rate hpositive hunit, fullCap_zero, terminalPayoff]
  change max ((1 / 2 : ℝ) - 1 / 2) (3 * rate / 2) = 3 * rate / 2
  rw [sub_self]
  exact max_eq_right (by positivity)

theorem exploitability_boundary :
    exploitability 0 (by norm_num) (by norm_num) = 1 / 2 := by
  rw [exploitability_eq_max]
  rw [fullCap_zero, fullCap_one_boundary, terminalPayoff]
  norm_num [value]

/-- The actual family's exploitability tends to zero through positive rates.
The boundary itself has error one half, so no closedness inference is made. -/
theorem exploitability_small_rates (accuracy : ℝ) (haccuracy : 0 < accuracy) :
    ∃ clearance : ℝ, 0 < clearance ∧
      ∀ rate (hpositive : 0 < rate) (hunit : rate ≤ 1), rate < clearance →
        exploitability rate hpositive.le hunit < accuracy := by
  refine ⟨2 * accuracy / 3, by positivity, ?_⟩
  intro rate hpositive hunit hsmall
  rw [exploitability_positive rate hpositive hunit]
  linarith

theorem boundary_not_exact_terminalNash :
    ¬(quittingGame reward).IsεAsymptoticNash (quittingTerminalPayoff reward) 0
      (profile 0 (by norm_num) (by norm_num)) :=
  SignedTwoPlayerExactNashNonattainment.not_exact_terminal_nash
    (1 / 2) (by norm_num) (by norm_num) _

/-- Immediate Quit provides the lower bound against every original opponent plan. -/
theorem immediateQuit_floor
    (opponents : (quittingGame reward).BehaviorProfile) :
    -1 / 2 ≤ quittingTerminalPayoff reward
      (Function.update opponents 1 (quittingPureTimeBehaviorStrategy reward 1 (some 0))) 1 := by
  rw [SignedTwoPlayerExactNashNonattainment.quit_at_time_payoff]
  rw [StoppingLaw.survival_zero]
  have hnonneg := StoppingLaw.finiteMass_nonneg
    (quittingBehaviorStoppingLaw reward (opponents 0)) 0
  linarith

theorem punishmentValue_one :
    quittingPunishmentValue reward 1 = -1 / 2 := by
  refine le_antisymm ?_ ?_
  · refine le_of_forall_pos_le_add fun error herror => ?_
    let rate := min 1 (error / 3)
    have hpositive : 0 < rate := lt_min (by norm_num) (by positivity)
    have hunit : rate ≤ 1 := min_le_left _ _
    have hsmall : rate ≤ error / 3 := min_le_right _ _
    have hcap := quittingPunishmentValue_le_stationaryUnilateralCap
      reward 1 (root rate hpositive.le hunit)
    rw [stationaryCap_one rate hpositive hunit] at hcap
    linarith
  · let : Nonempty (quittingGame reward).BehaviorProfile :=
      ⟨quittingAlwaysContinueProfile reward⟩
    exact le_ciInf fun opponents =>
      (immediateQuit_floor opponents).trans
        (le_quittingBestReplyValue reward opponents 1
          (quittingPureTimeBehaviorStrategy reward 1 (some 0)))

/-- The opponents-only solo joining system is feasible precisely from rate one quarter. -/
theorem soloCriterion_iff (rate : ℝ) :
    QuittingSoloQuitterCriterion reward 1 rate ↔ 1 / 4 ≤ rate := by
  constructor
  · intro hcriterion
    have hzero := hcriterion 0 (by decide)
    rw [solo_values.1, collision_values.1, solo_values.2.2.1] at hzero
    linarith
  · intro hrate who hwho
    fin_cases who
    · change (1 - rate) * quittingSoloReward reward 0 0 +
          rate * quittingSingletonCollisionReward reward 1 0 ≤
        quittingSoloReward reward 1 0
      rw [solo_values.1, collision_values.1, solo_values.2.2.1]
      linarith
    · exact (hwho rfl).elim

theorem singletonMatrix :
    quittingSingletonMatrix reward = !![0, -1 / 2; -1 / 2, 0] := by
  ext who owner
  fin_cases who <;> fin_cases owner <;>
    norm_num [quittingSingletonMatrix, reward, SignedTwoPlayerExactNashNonattainment.reward]

theorem singletonMatrix_isR0 : IsR0Matrix (quittingSingletonMatrix reward) := by
  intro weight hsolution who
  have hzero := hsolution.residual_nonneg 0
  have hone := hsolution.residual_nonneg 1
  rw [singletonMatrix] at hzero hone
  norm_num [lcpResidual, Fin.sum_univ_two, Matrix.of_apply] at hzero hone
  have hweightZero := hsolution.weight_nonneg 0
  have hweightOne := hsolution.weight_nonneg 1
  fin_cases who
  · change weight 0 = 0
    linarith
  · change weight 1 = 0
    linarith

theorem singletonMatrix_no_negativeOne_solution :
    ¬StandardLCPSolvable (quittingSingletonMatrix reward) (fun _ => -1) := by
  rintro ⟨weight, hsolution⟩
  have hzero := hsolution.residual_nonneg 0
  rw [singletonMatrix] at hzero
  norm_num [lcpResidual, Fin.sum_univ_two, Matrix.of_apply] at hzero
  have hnonneg := hsolution.weight_nonneg 1
  linarith

theorem singletonMatrix_degree :
    r0Degree (quittingSingletonMatrix reward) singletonMatrix_isR0 = 0 := by
  by_contra hnonzero
  exact singletonMatrix_no_negativeOne_solution
    (isStandardQ_of_r0Degree_ne_zero _ singletonMatrix_isR0 hnonzero (fun _ => -1))

end GameTheory.NegativeSoloStationaryBoundary
