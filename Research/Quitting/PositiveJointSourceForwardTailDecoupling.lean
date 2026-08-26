/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Classification.Existence.PositiveJointPrefixReachEndpoint
import UniformEquilibrium.Quitting.Circulation.SingletonFlowMesh
import UniformEquilibrium.Quitting.Cycles.AnchoredSoloPeriodic
import UniformEquilibrium.Quitting.Cycles.SoloRootSequenceValues
import UniformEquilibrium.Quitting.Paths.LiveChainDominationCap

/-!
# Actual-source forward/tail decoupling regression

This file tests whether positive whole-prefix reach and exact global Nash
align the forward value of a divergent stationary prefix with the prescribed
payoff of its reached punishment tail.

The regression separates those limits from the source and Nash fields alone.
It has a sure-exit exact Nash row at the zero tail, so it is an S.2 case and
does not instantiate the maintained no-sure-exit residual.
-/

noncomputable section

namespace GameTheory

open Filter StochasticGame
open scoped Topology

namespace PositiveJointSourceForwardTailDecoupling

/-- Player `false` is a harmless solo quitter.  Player `true` receives one
exactly when `false` quits alone. -/
def reward : {S : Finset Bool // S.Nonempty} → Payoff Bool :=
  fun terminal who ↦ if who then if terminal.1 = {false} then 1 else 0 else 0

@[simp] theorem reward_false
    (terminal : {S : Finset Bool // S.Nonempty}) :
    reward terminal false = 0 := by
  simp [reward]

@[simp] theorem reward_singleton_false_true :
    reward (quittingSingletonTerminal false) true = 1 := by
  simp [reward, quittingSingletonTerminal]

@[simp] theorem reward_singleton_true_true :
    reward (quittingSingletonTerminal true) true = 0 := by
  simp [reward, quittingSingletonTerminal]

@[simp] theorem reward_pair_true :
    reward ⟨{false, true}, Finset.insert_nonempty false {true}⟩ true = 0 := by
  norm_num [reward, Finset.ext_iff]

/-- The number of repeated microstages in row `n`. -/
def meshSize (n : ℕ) : ℕ := n + 3

theorem meshSize_pos (n : ℕ) : 0 < meshSize n := by
  unfold meshSize
  omega

/-- A mesh whose full-prefix Continue probability is exactly one half. -/
def rate (n : ℕ) : ℝ := quittingMeshHazard (1 / 2) (meshSize n)

theorem rate_nonneg (n : ℕ) : 0 ≤ rate n :=
  quittingMeshHazard_nonneg (meshSize n) (by norm_num) (by norm_num)

theorem rate_le_one (n : ℕ) : rate n ≤ 1 :=
  quittingMeshHazard_le_one (p := 1 / 2) (meshSize n) (by norm_num)

theorem one_sub_rate_pow (n : ℕ) :
    (1 - rate n) ^ meshSize n = 1 / 2 := by
  unfold rate
  rw [one_sub_quittingMeshHazard_pow (p := (1 / 2 : ℝ))
    (by norm_num) (meshSize_pos n)]
  norm_num

/-- Only player `false` may Quit in the repeated prefix. -/
def root (n : ℕ) : Bool → PMF Bool :=
  quittingSoloMixedRoot false
    (quittingHazardCoin (rate n) (rate_nonneg n) (rate_le_one n))

theorem root_continueMass (n : ℕ) :
    quittingStationaryContinueMass (root n) = 1 - rate n := by
  rw [root, quittingStationaryContinueMass_soloMixedRoot,
    quittingHazardCoin_false_toReal]

/-- The reached punishment tail is literal all-Continue. -/
def punishment : ℕ → Bool → PMF Bool :=
  fun _ ↦ quittingAllContinueRoot

/-- Row `n` repeats its mesh root for exactly `meshSize n` stages. -/
def roots (n : ℕ) : ℕ → Bool → PMF Bool :=
  quittingStationaryPrefixThenRoots (root n) (n + 2) punishment

theorem roots_eq_truncated (n : ℕ) :
    roots n = quittingTruncatedRoots (fun _ ↦ root n) (meshSize n) := by
  funext time
  by_cases htime : time ≤ n + 2
  · rw [quittingTruncatedRoots_of_lt]
    · simp [roots, htime]
    · unfold meshSize
      omega
  · rw [quittingTruncatedRoots_of_le]
    · unfold roots quittingStationaryPrefixThenRoots
      rw [if_neg htime]
      rfl
    · unfold meshSize
      omega

theorem roots_solo (n time : ℕ) (who : Bool) (hwho : who ≠ false) :
    roots n time who = PMF.pure false := by
  rw [roots_eq_truncated]
  by_cases htime : time < meshSize n
  · rw [quittingTruncatedRoots_of_lt _ htime]
    exact quittingSoloMixedRoot_of_ne hwho _
  · rw [quittingTruncatedRoots_of_le _ (Nat.not_lt.mp htime)]
    simp [quittingAllContinueRoot]

theorem terminalValue_false_eq_zero
    (plan : ℕ → Bool → PMF Bool) (start : ℕ) :
    quittingRootSequenceTerminalValue reward plan false start = 0 := by
  rw [quittingRootSequenceTerminalValue, quittingTerminalPayoff]
  simp [reward]

theorem hazardTerminalValue_false_eq_zero
    (plan : ℕ → Bool → PMF Bool) (hazard : ℕ → PMF Bool)
    (start : ℕ) :
    quittingRootSequenceHazardTerminalValue reward plan false hazard start = 0 := by
  unfold quittingRootSequenceHazardTerminalValue
  exact terminalValue_false_eq_zero _ _

theorem terminalValue_true_nonneg (n start : ℕ) :
    0 ≤ quittingRootSequenceTerminalValue reward (roots n) true start := by
  apply quittingRootSequenceTerminalValue_nonneg_of_soloRoots
    reward (roots n) false start
  · exact roots_solo n
  · change 0 ≤ reward (quittingSingletonTerminal false) true
    rw [reward_singleton_false_true]
    norm_num

theorem endpointNash (n stage : ℕ) :
    IsεQuittingRootEndpointNash reward
      (quittingRootSequenceTailVector reward (roots n) (stage + 1)) 0
      (roots n stage) := by
  rw [roots_eq_truncated]
  by_cases hstage : stage < meshSize n
  · rw [quittingTruncatedRoots_of_lt _ hstage]
    apply isZeroQuittingRootEndpointNash_soloMixedRoot
    · exact terminalValue_false_eq_zero _ _ |>.symm
    · intro who hwho
      cases who with
      | false => exact False.elim (hwho rfl)
      | true =>
          have htail := terminalValue_true_nonneg n (stage + 1)
          rw [roots_eq_truncated] at htail
          simp only [reward_pair_true, reward_singleton_true_true,
            reward_singleton_false_true, mul_zero, add_zero]
          exact add_nonneg (mul_nonneg ENNReal.toReal_nonneg (by norm_num))
            (mul_nonneg ENNReal.toReal_nonneg htail)
  · rw [quittingTruncatedRoots_of_le _ (Nat.not_lt.mp hstage)]
    have hroot : (quittingAllContinueRoot : Bool → PMF Bool) =
        quittingSoloMixedRoot false (PMF.pure false) := by
      funext who
      cases who <;> simp [quittingAllContinueRoot, quittingSoloMixedRoot]
    rw [hroot]
    apply isZeroQuittingRootEndpointNash_soloMixedRoot
    · exact terminalValue_false_eq_zero _ _ |>.symm
    · intro who hwho
      cases who with
      | false => exact False.elim (hwho rfl)
      | true =>
          have htail := terminalValue_true_nonneg n (stage + 1)
          rw [roots_eq_truncated] at htail
          simpa [quittingRootSequenceTailVector] using htail

/-- Every displayed stationary-prefix row is exact Nash against arbitrary
time-dependent unilateral hazards. -/
theorem roots_nash (n : ℕ) :
    IsεQuittingRootSequenceNash reward 0 (roots n) := by
  intro who hazard
  cases who with
  | false =>
      rw [hazardTerminalValue_false_eq_zero,
        terminalValue_false_eq_zero]
      norm_num
  | true =>
      rw [roots_eq_truncated]
      have hcap :=
        quittingRootSequenceHazardTerminalValue_quittingTruncatedRoots_le_of_quitRegret_le
          reward (fun _ ↦ root n) true (meshSize n) (by norm_num : (0 : ℝ) ≤ 0)
          (fun index _ ↦ by
            have hledger := quittingLedger_le_of_isεQuittingRootEndpointNash
              reward (roots n) true index (endpointNash n)
            rw [roots_eq_truncated] at hledger
            simpa using hledger)
          (fun stage ↦ by
            have hregret :=
              quittingLedgerQuitRegret_le_of_isεQuittingRootEndpointNash
                reward (roots n) true stage (endpointNash n stage)
            rw [roots_eq_truncated] at hregret
            simpa using hregret)
          hazard
      simpa using hcap

/-- A standard positive error scale. -/
def error (n : ℕ) : ℝ := 1 / (n + 1)

theorem error_pos (n : ℕ) : 0 < error n := by
  unfold error
  positivity

theorem error_tendsto_zero : Tendsto error atTop (nhds 0) := by
  exact tendsto_one_div_add_atTop_nhds_zero_nat

theorem punishmentValue_false_eq_zero :
    quittingPunishmentValue reward false = 0 := by
  rw [quittingPunishmentValue_eq_stationaryPunishmentValue]
  unfold quittingStationaryPunishmentValue
  have hcap : ∀ root : Bool → PMF Bool,
      quittingStationaryUnilateralCap reward root false = 0 := by
    intro root
    rw [quittingStationaryUnilateralCap_eq_max_div]
    simp [quittingStationaryFixedOpponentsQuitValue,
      quittingStationaryFixedOpponentsContinueReward,
      quittingFixedOpponentsQuitValue,
      quittingFixedOpponentsContinueReward,
      quittingRootAbsorbingContribution, quittingRootExpectedPayoff,
      quittingRootPayoff, reward]
  simp only [hcap, ciInf_const]

/-- The exact diffuse family behind the regression. -/
def family : QuittingDiffuseStationaryPrefixFamily reward where
  error := error
  root := root
  horizon := fun n ↦ n + 2
  punished := fun _ ↦ false
  punishment := fun _ ↦ punishment
  error_pos := error_pos
  error_tendsto_zero := error_tendsto_zero
  horizon_gt_one := by omega
  punishmentWithin := by
    intro n hazard
    have hcap := quittingRootSequenceHazardTerminalValue_quittingAllContinueRoots_le_max
      reward false hazard
    have hzero : reward (quittingSingletonTerminal false) false = 0 := by simp
    rw [hzero, max_self] at hcap
    change quittingRootSequenceHazardTerminalValue reward
      (fun _ ↦ quittingAllContinueRoot) false hazard 0 ≤ _
    simpa [punishmentValue_false_eq_zero] using
      hcap.trans (error_pos n).le
  nash := by
    intro n who hazard
    have hnash := roots_nash n who hazard
    change quittingRootSequenceHazardTerminalValue reward (roots n) who
      hazard 0 ≤ quittingRootSequenceTerminalValue reward (roots n) who 0 +
        2 * error n
    exact hnash.trans (by nlinarith [error_pos n])
  live_pos := by
    intro n
    rw [root_continueMass]
    unfold rate
    rw [one_sub_quittingMeshHazard]
    exact Real.rpow_pos_of_pos (by norm_num) _

theorem family_prefixJointSurvival (n : ℕ) :
    family.prefixJointSurvival n = 1 / 2 := by
  unfold QuittingDiffuseStationaryPrefixFamily.prefixJointSurvival family
  rw [quittingJointSurvivalWeight_const, root_continueMass]
  simpa [meshSize] using one_sub_rate_pow n

/-- The regression is a literal positive-joint source with divergent
stationary-prefix horizons and constant reach one half. -/
def source : QuittingPositiveJointPrefixReachSource reward where
  family := family
  selected := id
  jointLimit := 1 / 2
  selected_strictMono := strictMono_id
  jointLimit_pos := by norm_num
  joint_tendsto := by
    have heq : (fun n ↦ family.prefixJointSurvival (id n)) =
        fun _ ↦ (1 / 2 : ℝ) := by
      funext n
      exact family_prefixJointSurvival n
    rw [heq]
    exact tendsto_const_nhds

theorem source_horizon_tendsto_atTop :
    Tendsto (fun n ↦ source.family.horizon (source.selected n))
      atTop atTop := by
  simpa [source, family] using tendsto_add_atTop_nat 2

theorem root_eq_soloStationaryRoot (n : ℕ) :
    root n = quittingSoloStationaryRoot false
      (quittingHazardCoin (rate n) (rate_nonneg n) (rate_le_one n)) := by
  funext who
  cases who <;>
    simp [root, quittingSoloMixedRoot, quittingSoloStationaryRoot,
      quittingAllContinueRoot]

theorem root_absorbingContribution_true (n : ℕ) :
    quittingRootAbsorbingContribution reward (root n) true = rate n := by
  rw [root_eq_soloStationaryRoot,
    quittingRootAbsorbingContribution_solo,
    quittingHazardCoin_true_toReal]
  change rate n * reward (quittingSingletonTerminal false) true = rate n
  rw [reward_singleton_false_true, mul_one]

/-- The beginning of every full source row pays the spectator exactly one
half. -/
theorem forwardValue_true_eq_half (n : ℕ) :
    quittingStationaryPrefixFamilyValue family n 0 true = 1 / 2 := by
  change quittingRootSequenceTerminalValue reward (roots n) true 0 = 1 / 2
  rw [roots_eq_truncated,
    quittingRootSequenceTerminalValue_quittingTruncatedRoots_eq_sum]
  simp_rw [quittingJointSurvivalWeight_const, root_continueMass,
    root_absorbingContribution_true]
  have hgeom := geom_sum_mul (1 - rate n) (meshSize n)
  have hpow := one_sub_rate_pow n
  calc
    ∑ offset ∈ Finset.range (meshSize n),
          (1 - rate n) ^ offset * rate n =
        rate n * ∑ offset ∈ Finset.range (meshSize n),
          (1 - rate n) ^ offset := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro offset _
            ring
    _ = 1 / 2 := by nlinarith

/-- Every reached punishment suffix is all-Continue and hence has prescribed
spectator payoff zero. -/
theorem punishmentPayoff_true_eq_zero (n : ℕ) :
    quittingTerminalPayoff reward (source.punishmentProfile n) true = 0 := by
  change quittingRootSequenceTerminalValue reward punishment true 0 = 0
  have hroot : punishment =
      (fun _ ↦ (quittingAllContinueRoot : Bool → PMF Bool)) := rfl
  rw [hroot]
  exact quittingRootSequenceTerminalValue_eq_zero_of_allContinue_from
    reward _ true 0 (fun _ _ ↦ rfl)

/-- Exact actual-source decoupling: the forward fixed-depth value and the
prescribed payoff of the reached punishment tail stay one half apart. -/
theorem abs_forwardValue_sub_punishmentPayoff_true_eq_half (n : ℕ) :
    |quittingStationaryPrefixFamilyValue family n 0 true -
        quittingTerminalPayoff reward (source.punishmentProfile n) true| =
      1 / 2 := by
  rw [forwardValue_true_eq_half, punishmentPayoff_true_eq_zero]
  norm_num

theorem forwardValue_true_tendsto_half :
    Tendsto (fun n ↦ quittingStationaryPrefixFamilyValue family n 0 true)
      atTop (nhds (1 / 2)) := by
  simpa only [forwardValue_true_eq_half] using
    (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ (1 / 2 : ℝ))
      atTop (nhds (1 / 2)))

theorem punishmentPayoff_true_tendsto_zero :
    Tendsto (fun n ↦
      quittingTerminalPayoff reward (source.punishmentProfile n) true)
      atTop (nhds 0) := by
  simpa only [punishmentPayoff_true_eq_zero] using
    (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ (0 : ℝ))
      atTop (nhds 0))

/-- The separating game is already on the sure-exit side of the AGKRS
classification.  Thus the regression does not test the additional
no-sure-exit residual hypothesis. -/
theorem exists_sureExit_exactNash_at_zero :
    ∃ root : Bool → PMF Bool,
      root false = PMF.pure true ∧
      IsεQuittingRootNash reward (0 : Payoff Bool) 0 root := by
  let root : Bool → PMF Bool :=
    quittingSoloMixedRoot false (PMF.pure true)
  refine ⟨root, ?_, ?_⟩
  · simp [root, quittingSoloMixedRoot]
  · rw [← isZeroQuittingRootEndpointNash_iff_isZeroQuittingRootNash]
    apply isZeroQuittingRootEndpointNash_soloMixedRoot
    · simp [reward]
    · intro who hwho
      cases who with
      | false => exact False.elim (hwho rfl)
      | true => norm_num [reward, quittingSingletonTerminal, Finset.ext_iff]

/-- The reached all-Continue punishment suffix is itself exact Nash against
arbitrary behavioral deviations. -/
theorem punishment_nash :
    IsεQuittingRootSequenceNash reward 0 punishment := by
  intro who hazard
  cases who with
  | false =>
      rw [hazardTerminalValue_false_eq_zero,
        terminalValue_false_eq_zero]
      norm_num
  | true =>
      have hcap :=
        quittingRootSequenceHazardTerminalValue_quittingAllContinueRoots_le_max
          reward true hazard
      have hvalue : quittingRootSequenceTerminalValue reward punishment
          true 0 = 0 := by
        exact quittingRootSequenceTerminalValue_eq_zero_of_allContinue_from
          reward punishment true 0 (fun _ _ ↦ rfl)
      rw [hvalue, add_zero]
      change quittingRootSequenceHazardTerminalValue reward
        (fun _ ↦ quittingAllContinueRoot) true hazard 0 ≤ 0
      simpa [reward_singleton_true_true] using hcap

/-- The literal reached punishment profile at every selected source row is
the all-Continue root sequence used above. -/
theorem source_punishmentProfile_eq (n : ℕ) :
    source.punishmentProfile n =
      quittingRootSequenceProfile reward punishment 0 := by
  rfl

/-- An actual zero-debt endpoint furnished by the reached punishment suffix,
with the source's punished player retained. -/
def punishmentEndpoint :
    QuittingPositiveJointPrefixReachPunishmentEndpoint reward where
  punished := false
  endpoint := quittingTerminalSemanticPair reward
    (source.punishmentProfile 0)
  endpoint_mem := by
    exact subset_closure ⟨source.punishmentProfile 0, rfl⟩
  debt_nonpos := by
    intro who
    have hnash : (quittingGame reward).IsεAsymptoticNash
        (quittingTerminalPayoff reward) 0
        (source.punishmentProfile 0) := by
      rw [source_punishmentProfile_eq]
      exact (isεQuittingRootSequenceNash_iff_isεAsymptoticNash
        reward 0 punishment).mp punishment_nash
    exact quittingTerminalSemanticDebt_pair_le_of_isεAsymptoticNash
      reward (source.punishmentProfile 0) 0 hnash who
  punishmentCap := by
    change quittingContinuationBestResponseValue reward
      (source.punishmentProfile 0) false ≤
        quittingPunishmentValue reward false
    have hnash : (quittingGame reward).IsεAsymptoticNash
        (quittingTerminalPayoff reward) 0
        (source.punishmentProfile 0) := by
      rw [source_punishmentProfile_eq]
      exact (isεQuittingRootSequenceNash_iff_isεAsymptoticNash
        reward 0 punishment).mp punishment_nash
    have hdebt :=
      quittingTerminalSemanticDebt_pair_le_of_isεAsymptoticNash
        reward (source.punishmentProfile 0) 0 hnash false
    change quittingContinuationBestResponseValue reward
        (source.punishmentProfile 0) false -
          quittingTerminalPayoff reward
            (source.punishmentProfile 0) false ≤ 0 at hdebt
    have hpayoff : quittingTerminalPayoff reward
        (source.punishmentProfile 0) false = 0 := by
      rw [source_punishmentProfile_eq]
      exact terminalValue_false_eq_zero punishment 0
    rw [hpayoff, sub_zero] at hdebt
    simpa [punishmentValue_false_eq_zero] using hdebt

theorem punishmentEndpoint_payoff_eq_zero :
    punishmentEndpoint.endpoint.1 = (0 : Payoff Bool) := by
  funext who
  cases who with
  | false =>
      change quittingTerminalPayoff reward
        (source.punishmentProfile 0) false = 0
      rw [source_punishmentProfile_eq]
      exact terminalValue_false_eq_zero punishment 0
  | true =>
      change quittingTerminalPayoff reward
        (source.punishmentProfile 0) true = 0
      simpa using punishmentPayoff_true_eq_zero 0

/-- The actual reached endpoint lies on the sure-exit side of the endpoint
dichotomy. -/
theorem punishmentEndpoint_hasSureExitNashPrefix :
    punishmentEndpoint.HasSureExitNashPrefix := by
  obtain ⟨root, hquit, hnash⟩ := exists_sureExit_exactNash_at_zero
  refine ⟨false, root, hquit, ?_⟩
  rw [punishmentEndpoint_payoff_eq_zero]
  exact hnash

/-- Hence the regression belongs to paper branch S.2. -/
theorem instantPunishmentExistence :
    QuittingInstantPunishmentεEquilibriumExistence reward :=
  punishmentEndpoint.instantPunishment
    punishmentEndpoint_hasSureExitNashPrefix

/-- In particular, this game cannot instantiate the maintained
positive-joint no-sure-exit residual. -/
theorem not_nonempty_noSureExitResidual :
    ¬Nonempty (QuittingPositiveJointPrefixReachNoSureExitResidual reward) := by
  rintro ⟨residual⟩
  exact residual.noSureExitNashPrefix punishmentEndpoint
    punishmentEndpoint_hasSureExitNashPrefix

/-- The actual forward values and reached-tail prescribed payoffs admit no
common limit, even though the source has exact global Nash rows, divergent
horizons, and fixed positive whole-prefix reach. -/
theorem not_exists_common_forward_punishmentPayoff_limit :
    ¬∃ limit : ℝ,
      Tendsto (fun n ↦ quittingStationaryPrefixFamilyValue family n 0 true)
        atTop (nhds limit) ∧
      Tendsto (fun n ↦
        quittingTerminalPayoff reward (source.punishmentProfile n) true)
        atTop (nhds limit) := by
  rintro ⟨limit, hforward, hpunishment⟩
  have hhalf : limit = 1 / 2 :=
    tendsto_nhds_unique hforward forwardValue_true_tendsto_half
  have hzero : limit = 0 :=
    tendsto_nhds_unique hpunishment punishmentPayoff_true_tendsto_zero
  norm_num [hzero] at hhalf

end PositiveJointSourceForwardTailDecoupling

end GameTheory
