/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Cycles.FourPlayerPeriodOneVanishingHazardSource
import UniformEquilibrium.Quitting.Stationary.ApproximabilityCompactification
import UniformEquilibrium.Quitting.Classification.LCP.CounterexampleNecessary
import UniformEquilibrium.Quitting.Classification.LCP.FullNormalCoreHomogeneousTransfer
import UniformEquilibrium.Quitting.Classification.LCP.ThreeCore.AmbientCarrierElimination

/-!
# Limiting singleton margins of one-period vanishing-hazard sources

This module identifies the payoff limit of one actual one-period source with
the singleton-reward barycenter of its normalized hazard direction. It then
uses the exact exponential response law to identify the support of that
direction with the players having the least limiting Continue advantage.
-/

noncomputable section

namespace GameTheory

open Filter Math.LinearProgramming QuittingLCPClassification
open ThreeCoreAmbientCarrierElimination

variable {ι : Type} [Fintype ι] [DecidableEq ι] [Nontrivial ι]

/-- Payoff of the singleton lottery selected by a player-simplex direction. -/
def quittingSingletonDirectionPayoff
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (direction : stdSimplex ℝ ι) : Payoff ι :=
  fun who ↦ ∑ owner, direction.val owner * quittingSoloReward reward owner who

omit [Nontrivial ι] in
/-- The singleton-matrix residual is the direction payoff minus the player's
own singleton payoff. -/
theorem singletonLCPResidual_normalizedSoloMatrix_eq_directionPayoff_sub_solo
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (direction : stdSimplex ℝ ι) (who : ι) :
    singletonLCPResidual (normalizedSoloMatrix reward) direction who =
      quittingSingletonDirectionPayoff reward direction who -
        quittingSoloReward reward who who := by
  rw [normalizedSoloMatrix_eq_projectiveLCPMatrix]
  unfold singletonLCPResidual wsum dotProduct quittingProjectiveLCPMatrix
    quittingSingletonDirectionPayoff
  simp_rw [mul_sub]
  rw [Finset.sum_sub_distrib, ← Finset.sum_mul]
  have hmass : ∑ owner, direction owner = 1 := direction.property.2
  rw [hmass, one_mul]
  rfl

/-- Logistic responses at two separated Continue advantages have an
exponentially small ratio when the lower advantage is bounded below by a
fixed multiple of the temperature. -/
theorem interiorBinaryApproximateResponse_ratio_le_exp_of_boundedLowAdvantage
    {error constant separation : ℝ} (herror : 0 < error)
    (quitHigh continueHigh quitLow continueLow : ℝ)
    (hlow : -constant * error ≤ continueLow - quitLow)
    (hseparated : continueLow - quitLow + separation ≤
      continueHigh - quitHigh) :
    interiorBinaryApproximateResponse error quitHigh continueHigh /
        interiorBinaryApproximateResponse error quitLow continueLow ≤
      (1 + Real.exp constant) * Real.exp (-separation / error) := by
  let highExponent := (quitHigh - continueHigh) / error
  let lowExponent := (quitLow - continueLow) / error
  have hhighExpPos : 0 < Real.exp highExponent := Real.exp_pos _
  have hlowExpPos : 0 < Real.exp lowExponent := Real.exp_pos _
  have hconstantExpPos : 0 < Real.exp constant := Real.exp_pos _
  have hhighDenPos : 0 < 1 + Real.exp highExponent := by positivity
  have hlowDenPos : 0 < 1 + Real.exp lowExponent := by positivity
  have hlowExponent : lowExponent ≤ constant := by
    dsimp only [lowExponent]
    apply (div_le_iff₀ herror).2
    linarith
  have hlowExpLe : Real.exp lowExponent ≤ Real.exp constant := by
    rwa [Real.exp_le_exp]
  have hfactorNonnegative :
      0 ≤ (1 + Real.exp lowExponent) / (1 + Real.exp highExponent) := by
    positivity
  have hfactorLe :
      (1 + Real.exp lowExponent) / (1 + Real.exp highExponent) ≤
        1 + Real.exp constant := by
    apply (div_le_iff₀ hhighDenPos).2
    nlinarith
  have hexponent : highExponent - lowExponent ≤ -separation / error := by
    dsimp only [highExponent, lowExponent]
    rw [← sub_div]
    apply (div_le_div_iff_of_pos_right herror).2
    linarith
  have hexpComparison :
      Real.exp highExponent / Real.exp lowExponent ≤
        Real.exp (-separation / error) := by
    rw [← Real.exp_sub, Real.exp_le_exp]
    exact hexponent
  have hratio :
      interiorBinaryApproximateResponse error quitHigh continueHigh /
          interiorBinaryApproximateResponse error quitLow continueLow =
        (Real.exp highExponent / Real.exp lowExponent) *
          ((1 + Real.exp lowExponent) / (1 + Real.exp highExponent)) := by
    dsimp only [highExponent, lowExponent]
    unfold interiorBinaryApproximateResponse
    field_simp [ne_of_gt hhighExpPos, ne_of_gt hlowExpPos,
      ne_of_gt hhighDenPos, ne_of_gt hlowDenPos]
  rw [hratio]
  nlinarith [mul_le_mul hexpComparison hfactorLe hfactorNonnegative
    (Real.exp_nonneg (-separation / error))]

/-- Along vanishing positive temperatures, the response ratio at two
uniformly separated Continue advantages vanishes if the lower advantage is
bounded below by a fixed temperature multiple. -/
theorem tendsto_interiorBinaryApproximateResponse_ratio_zero_of_boundedLowAdvantage
    (error quitHigh continueHigh quitLow continueLow : ℕ → ℝ)
    (constant : ℝ) {separation : ℝ} (hseparation : 0 < separation)
    (herrorPos : ∀ index, 0 < error index)
    (herrorZero : Tendsto error atTop (nhds 0))
    (hlow : ∀ᶠ index in atTop,
      -constant * error index ≤ continueLow index - quitLow index)
    (hseparated : ∀ᶠ index in atTop,
      continueLow index - quitLow index + separation ≤
        continueHigh index - quitHigh index) :
    Tendsto (fun index ↦
      interiorBinaryApproximateResponse (error index)
          (quitHigh index) (continueHigh index) /
        interiorBinaryApproximateResponse (error index)
          (quitLow index) (continueLow index)) atTop (nhds 0) := by
  have herrorWithin : Tendsto error atTop (nhdsWithin 0 (Set.Ioi 0)) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within error herrorZero
      (Eventually.of_forall herrorPos)
  have hinverse : Tendsto (fun index ↦ (error index)⁻¹) atTop atTop := by
    simpa [Pi.inv_def] using herrorWithin.inv_tendsto_nhdsGT_zero
  have hscaled : Tendsto (fun index ↦ separation * (error index)⁻¹)
      atTop atTop := hinverse.const_mul_atTop hseparation
  have hexponential : Tendsto
      (fun index ↦ Real.exp (-(separation * (error index)⁻¹)))
      atTop (nhds 0) := Real.tendsto_exp_neg_atTop_nhds_zero.comp hscaled
  have hupper : Tendsto (fun index ↦
      (1 + Real.exp constant) * Real.exp (-separation / error index))
      atTop (nhds 0) := by
    simpa only [div_eq_mul_inv, neg_mul, mul_zero] using
      tendsto_const_nhds.mul hexponential
  apply squeeze_zero'
  · exact Eventually.of_forall fun index ↦ div_nonneg
      (interiorBinaryApproximateResponse_pos _ _ _).le
      (interiorBinaryApproximateResponse_pos _ _ _).le
  · filter_upwards [hlow, hseparated] with index hlowIndex hseparatedIndex
    exact interiorBinaryApproximateResponse_ratio_le_exp_of_boundedLowAdvantage
      (herrorPos index) _ _ _ _ hlowIndex hseparatedIndex
  · exact hupper

omit [DecidableEq ι] [Nontrivial ι] in
/-- A one-row cyclic behavior profile is the stationary profile of its sole
root. -/
theorem quittingCyclicBehaviorProfile_finOne_eq_stationary
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (cycle : Fin 1 → ι → PMF Bool) (phase : Fin 1) :
    quittingCyclicBehaviorProfile reward cycle phase =
      quittingStationaryProfile reward (cycle phase) := by
  funext who time history
  unfold quittingCyclicBehaviorProfile quittingRootSequenceProfile
    quittingCyclicRootSequence quittingStationaryProfile
    StochasticGame.stationaryBehaviorProfile
  simp only [Nat.zero_add]
  rw [Subsingleton.elim (quittingCyclicOrbit phase time) phase]

namespace PeriodOneNormalizedSourceLimit

variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
  {error : ℕ → ℝ}
  {source : PeriodOneVanishingHazardSource reward error}

/-- Continue payoff minus Quit payoff at one selected actual source. -/
def selectedEndpointContinueAdvantage
    (limit : PeriodOneNormalizedSourceLimit source)
    (index : ℕ) (who : ι) : ℝ :=
  quittingCyclicEndpointContinueAdvantage reward
    (source.block (limit.originalIndex index)).cycle
    (source.block (limit.originalIndex index)).value 0 who

/-- Limiting Continue payoff minus own singleton Quit payoff. -/
def limitingSingletonMargin
    (limit : PeriodOneNormalizedSourceLimit source) (who : ι) : ℝ :=
  singletonLCPResidual (normalizedSoloMatrix reward) limit.direction who

/-- Aggregate endpoint Nash regret of one selected returned row. -/
def selectedTotalEndpointRegret
    (limit : PeriodOneNormalizedSourceLimit source) (index : ℕ) : ℝ :=
  quittingRootTotalNashDefect reward
    ((source.block (limit.originalIndex index)).value (finRotate 1 0))
    ((source.block (limit.originalIndex index)).cycle 0)

/-- Every selected one-period source profile is literally the stationary
profile of its displayed root. -/
theorem selectedProfile_eq_stationary
    (limit : PeriodOneNormalizedSourceLimit source) (index : ℕ) :
    source.profile (limit.select index) =
      quittingStationaryProfile reward (source.root (limit.select index)) := by
  exact quittingCyclicBehaviorProfile_finOne_eq_stationary
    reward (source.block (limit.originalIndex index)).cycle 0

/-- The exact-return tail of a selected block is its stationary terminal
payoff vector. -/
theorem selectedBlockTail_eq_stationaryTerminalPayoff
    (limit : PeriodOneNormalizedSourceLimit source) (index : ℕ) :
    (source.block (limit.originalIndex index)).value (finRotate 1 0) =
      fun player ↦ quittingTerminalPayoff reward
        (quittingStationaryProfile reward
          (source.root (limit.select index))) player := by
  funext player
  rw [Subsingleton.elim (finRotate 1 0) 0]
  change source.value (limit.select index) player = _
  rw [← source.terminalPayoff_eq_value (limit.select index),
    limit.selectedProfile_eq_stationary index]

/-- The displayed root is endpoint approximate Nash against its literal
stationary terminal continuation. -/
theorem selectedRoot_endpointNash
    (limit : PeriodOneNormalizedSourceLimit source) (index : ℕ) :
    IsεQuittingRootEndpointNash reward
      (fun player ↦ quittingTerminalPayoff reward
        (quittingStationaryProfile reward
          (source.root (limit.select index))) player)
      (error (limit.originalIndex index))
      (source.root (limit.select index)) := by
  rw [← limit.selectedBlockTail_eq_stationaryTerminalPayoff index,
    isεQuittingRootEndpointNash_iff_isεQuittingRootNash]
  exact (source.block (limit.originalIndex index)).rootNash 0

/-- The payoff limit of an actual vanishing-hazard source is the singleton
lottery selected by the limit of its normalized hazard directions. -/
theorem limitValue_eq_singletonDirectionPayoff
    (limit : PeriodOneNormalizedSourceLimit source) :
    limit.limitValue = quittingSingletonDirectionPayoff reward limit.direction := by
  funext who
  let selectedDirection : ℕ → stdSimplex ℝ ι := fun index ↦
    quittingStationaryHazardDirection
      (source.root (limit.select index))
      (source.totalHazard_pos (limit.select index))
  let selectedValue : ℕ → Payoff ι :=
    fun index ↦ source.value (limit.select index)
  have hvalue : Tendsto (fun index ↦ selectedValue index who) atTop
      (nhds (limit.limitValue who)) :=
    ((continuous_apply who).tendsto limit.limitValue).comp limit.value_tendsto
  have hdirectionCoordinate : ∀ owner, Tendsto
      (fun index ↦ (selectedDirection index).val owner) atTop
      (nhds (limit.direction.val owner)) := by
    intro owner
    exact (((continuous_apply owner).comp continuous_subtype_val).tendsto
      limit.direction).comp limit.direction_tendsto
  have hbarycenter : Tendsto
      (fun index ↦ ∑ owner, (selectedDirection index).val owner *
        quittingSoloReward reward owner who) atTop
      (nhds (quittingSingletonDirectionPayoff reward limit.direction who)) := by
    unfold quittingSingletonDirectionPayoff
    exact tendsto_finsetSum Finset.univ fun owner _ ↦
      (hdirectionCoordinate owner).mul tendsto_const_nhds
  have hhalf : ∀ᶠ index in atTop,
      quittingStationaryTotalHazard (source.root (limit.select index)) ≤
        1 / 2 := by
    exact (limit.totalHazard_tendsto_zero.eventually
      (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))).mono
        fun _ hlt ↦ hlt.le
  have hdifferenceBound : ∀ᶠ index in atTop,
      |selectedValue index who -
          ∑ owner, (selectedDirection index).val owner *
            quittingSoloReward reward owner who| ≤
        6 * quittingRewardBound reward *
          quittingStationaryTotalHazard
            (source.root (limit.select index)) := by
    filter_upwards [hhalf] with index hhalfIndex
    change |source.value (limit.select index) who -
        ∑ owner, (quittingStationaryHazardDirection
          (source.root (limit.select index))
          (source.totalHazard_pos (limit.select index))).val owner *
            quittingSoloReward reward owner who| ≤ _
    rw [← source.terminalPayoff_eq_value (limit.select index),
      limit.selectedProfile_eq_stationary index]
    simpa [quittingStationarySingletonDirectionBarycenter] using
      abs_stationaryPayoff_sub_singletonDirectionBarycenter_le
        reward (abs_reward_le_quittingRewardBound reward)
        (source.root (limit.select index)) who
        (source.totalHazard_pos (limit.select index)) hhalfIndex
  have hbound : Tendsto (fun index ↦
      6 * quittingRewardBound reward *
        quittingStationaryTotalHazard (source.root (limit.select index)))
      atTop (nhds 0) := by
    simpa only [mul_zero] using
      limit.totalHazard_tendsto_zero.const_mul
        (6 * quittingRewardBound reward)
  have hdifference : Tendsto (fun index ↦ selectedValue index who -
      ∑ owner, (selectedDirection index).val owner *
        quittingSoloReward reward owner who) atTop (nhds 0) :=
    Math.tendsto_zero_of_abs_le_of_tendsto_zero _ _ hbound hdifferenceBound
  have hlimitDifference := hvalue.sub hbarycenter
  have hzero : limit.limitValue who -
      quittingSingletonDirectionPayoff reward limit.direction who = 0 :=
    tendsto_nhds_unique hlimitDifference hdifference
  linarith

/-- The limiting singleton residual is exactly the limiting payoff minus the
player's own singleton payoff. -/
theorem limitingSingletonMargin_eq_limitValue_sub_solo
    (limit : PeriodOneNormalizedSourceLimit source) (who : ι) :
    limit.limitingSingletonMargin who =
      limit.limitValue who - quittingSoloReward reward who who := by
  rw [limitingSingletonMargin,
    singletonLCPResidual_normalizedSoloMatrix_eq_directionPayoff_sub_solo,
    ← limit.limitValue_eq_singletonDirectionPayoff]

/-- The endpoint Continue advantages of the actual selected sources converge
to the singleton residual at the limiting hazard direction. -/
theorem selectedEndpointContinueAdvantage_tendsto_limitingSingletonMargin
    (limit : PeriodOneNormalizedSourceLimit source) :
    Tendsto (fun index who ↦
      limit.selectedEndpointContinueAdvantage index who) atTop
      (nhds limit.limitingSingletonMargin) := by
  apply tendsto_pi_nhds.2
  intro who
  let selectedDirection : ℕ → stdSimplex ℝ ι := fun index ↦
    quittingStationaryHazardDirection
      (source.root (limit.select index))
      (source.totalHazard_pos (limit.select index))
  let selectedResidual : ℕ → ℝ := fun index ↦
    singletonLCPResidual (normalizedSoloMatrix reward)
      (selectedDirection index) who
  have hresidual : Tendsto selectedResidual atTop
      (nhds (limit.limitingSingletonMargin who)) := by
    have hcontinuous : Continuous fun direction : stdSimplex ℝ ι ↦
        singletonLCPResidual (normalizedSoloMatrix reward) direction who := by
      rw [show (fun direction : stdSimplex ℝ ι ↦
          singletonLCPResidual (normalizedSoloMatrix reward) direction who) =
          fun direction ↦ quittingSingletonDirectionPayoff reward direction who -
            quittingSoloReward reward who who by
        funext direction
        exact singletonLCPResidual_normalizedSoloMatrix_eq_directionPayoff_sub_solo
          reward direction who]
      apply (continuous_finsetSum Finset.univ fun owner _ ↦
        (((continuous_apply owner).comp continuous_subtype_val).mul
          continuous_const)).sub continuous_const
    exact (hcontinuous.tendsto limit.direction).comp limit.direction_tendsto
  have hhalf : ∀ᶠ index in atTop,
      quittingStationaryTotalHazard (source.root (limit.select index)) ≤
        1 / 2 := by
    exact (limit.totalHazard_tendsto_zero.eventually
      (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))).mono
        fun _ hlt ↦ hlt.le
  have hclose : ∀ᶠ index in atTop,
      |limit.selectedEndpointContinueAdvantage index who -
          selectedResidual index| ≤
        10 * quittingRewardBound reward *
          quittingStationaryTotalHazard
            (source.root (limit.select index)) := by
    filter_upwards [hhalf] with index hhalfIndex
    let block := source.block (limit.originalIndex index)
    have htail := limit.selectedBlockTail_eq_stationaryTerminalPayoff index
    have hbound :=
      abs_quittingRootEndpointDifference_add_singletonLCPResidual_le
        reward (abs_reward_le_quittingRewardBound reward)
        (source.root (limit.select index)) who
        (source.totalHazard_pos (limit.select index)) hhalfIndex
    rw [← htail] at hbound
    change |limit.selectedEndpointContinueAdvantage index who -
        selectedResidual index| ≤ _
    rw [abs_sub_comm]
    have heq : selectedResidual index -
        limit.selectedEndpointContinueAdvantage index who =
      quittingRootEndpointDifference reward (block.value 0)
          (source.root (limit.select index)) who + selectedResidual index := by
      simp only [selectedEndpointContinueAdvantage,
        quittingCyclicEndpointContinueAdvantage,
        quittingRootEndpointDifference]
      dsimp only [block, PeriodOneVanishingHazardSource.root,
        PeriodOneNormalizedSourceLimit.originalIndex]
      rw [Subsingleton.elim (finRotate 1 0) 0]
      ring
    rw [heq]
    exact hbound
  have hbound : Tendsto (fun index ↦
      10 * quittingRewardBound reward *
        quittingStationaryTotalHazard (source.root (limit.select index)))
      atTop (nhds 0) := by
    simpa only [mul_zero] using
      limit.totalHazard_tendsto_zero.const_mul
        (10 * quittingRewardBound reward)
  have hdifference : Tendsto (fun index ↦
      limit.selectedEndpointContinueAdvantage index who -
        selectedResidual index) atTop (nhds 0) :=
    Math.tendsto_zero_of_abs_le_of_tendsto_zero _ _ hbound hclose
  have := hdifference.add hresidual
  simpa only [sub_add_cancel, zero_add] using this

/-- Every limiting Continue advantage is nonnegative. This conclusion uses
only endpoint approximate Nash and the common vanishing-error/hazard
chronology; support selection is not yet used. -/
theorem limitingSingletonMargin_nonneg
    (limit : PeriodOneNormalizedSourceLimit source)
    (herrorPos : ∀ index, 0 < error index)
    (herror : Tendsto error atTop (nhds 0)) (who : ι) :
    0 ≤ limit.limitingSingletonMargin who := by
  let selectedDirection : ℕ → stdSimplex ℝ ι := fun index ↦
    quittingStationaryHazardDirection
      (source.root (limit.select index))
      (source.totalHazard_pos (limit.select index))
  let selectedResidual : ℕ → ℝ := fun index ↦
    singletonLCPResidual (normalizedSoloMatrix reward)
      (selectedDirection index) who
  have hresidual : Tendsto selectedResidual atTop
      (nhds (limit.limitingSingletonMargin who)) := by
    have hcontinuous : Continuous fun direction : stdSimplex ℝ ι ↦
        singletonLCPResidual (normalizedSoloMatrix reward) direction who := by
      rw [show (fun direction : stdSimplex ℝ ι ↦
          singletonLCPResidual (normalizedSoloMatrix reward) direction who) =
          fun direction ↦ quittingSingletonDirectionPayoff reward direction who -
            quittingSoloReward reward who who by
        funext direction
        exact singletonLCPResidual_normalizedSoloMatrix_eq_directionPayoff_sub_solo
          reward direction who]
      apply (continuous_finsetSum Finset.univ fun owner _ ↦
        (((continuous_apply owner).comp continuous_subtype_val).mul
          continuous_const)).sub continuous_const
    exact (hcontinuous.tendsto limit.direction).comp limit.direction_tendsto
  let bound : ℕ → ℝ := fun index ↦
    10 * quittingRewardBound reward *
        quittingStationaryTotalHazard (source.root (limit.select index)) +
      2 * error (limit.originalIndex index)
  have hbound : Tendsto bound atTop (nhds 0) := by
    have hfirst : Tendsto (fun index ↦
        10 * quittingRewardBound reward *
          quittingStationaryTotalHazard (source.root (limit.select index)))
        atTop (nhds 0) := by
      simpa only [mul_zero] using
        limit.totalHazard_tendsto_zero.const_mul
          (10 * quittingRewardBound reward)
    have hsecond : Tendsto (fun index ↦
        2 * error (limit.originalIndex index)) atTop (nhds 0) := by
      simpa only [mul_zero] using
        (limit.error_tendsto_zero herror).const_mul 2
    simpa [bound] using hfirst.add hsecond
  have hhalf : ∀ᶠ index in atTop,
      quittingStationaryTotalHazard (source.root (limit.select index)) ≤
        1 / 2 := by
    exact (limit.totalHazard_tendsto_zero.eventually
      (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))).mono
        fun _ hlt ↦ hlt.le
  have hlower : ∀ᶠ index in atTop,
      -selectedResidual index ≤ bound index := by
    filter_upwards [hhalf] with index hhalfIndex
    exact neg_singletonLCPResidual_hazardDirection_le
      reward (abs_reward_le_quittingRewardBound reward)
      (herrorPos (limit.originalIndex index)).le
      (source.root (limit.select index))
      (source.totalHazard_pos (limit.select index)) hhalfIndex
      (limit.selectedRoot_endpointNash index) who
  have hlimit : Tendsto (fun index ↦ -selectedResidual index - bound index)
      atTop (nhds (-limit.limitingSingletonMargin who)) := by
    simpa only [sub_zero] using hresidual.neg.sub hbound
  have hnonpositive : ∀ᶠ index in atTop,
      -selectedResidual index - bound index ≤ 0 :=
    hlower.mono fun _ hle ↦ sub_nonpos.mpr hle
  have : -limit.limitingSingletonMargin who ≤ 0 :=
    le_of_tendsto hlimit hnonpositive
  linarith

/-- Every individual Quit probability vanishes along the selected source. -/
theorem selectedQuitProbability_tendsto_zero
    (limit : PeriodOneNormalizedSourceLimit source) (who : ι) :
    Tendsto (fun index ↦
      (source.root (limit.select index) who true).toReal)
      atTop (nhds 0) := by
  have hnonnegative : ∀ᶠ index in atTop,
      0 ≤ (source.root (limit.select index) who true).toReal :=
    Eventually.of_forall fun _ ↦ ENNReal.toReal_nonneg
  have hupper : ∀ᶠ index in atTop,
      (source.root (limit.select index) who true).toReal ≤
        quittingStationaryTotalHazard
          (source.root (limit.select index)) :=
    Eventually.of_forall fun index ↦ by
      unfold quittingStationaryTotalHazard
      exact Finset.single_le_sum
        (fun player _ ↦ ENNReal.toReal_nonneg
          (a := source.root (limit.select index) player true))
        (Finset.mem_univ who)
  exact squeeze_zero' hnonnegative hupper limit.totalHazard_tendsto_zero

/-- Endpoint Nash and vanishing individual hazard give the eventual lower
bound `-2·error` for every selected Continue advantage. -/
theorem eventually_neg_two_mul_error_le_selectedEndpointContinueAdvantage
    (limit : PeriodOneNormalizedSourceLimit source)
    (herrorPos : ∀ index, 0 < error index) (who : ι) :
    ∀ᶠ index in atTop,
      -2 * error (limit.originalIndex index) ≤
        limit.selectedEndpointContinueAdvantage index who := by
  have hhalf : ∀ᶠ index in atTop,
      (1 / 2 : ℝ) ≤
        (source.root (limit.select index) who false).toReal := by
    have hquit := limit.selectedQuitProbability_tendsto_zero who
    have hsmall := hquit.eventually
      (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))
    filter_upwards [hsmall] with index hquitHalf
    linarith [quittingRoot_continueProbability_add_quitProbability
      (source.root (limit.select index)) who]
  filter_upwards [hhalf] with index hcontinueHalf
  let difference := quittingRootEndpointDifference reward
    (fun player ↦ quittingTerminalPayoff reward
      (quittingStationaryProfile reward
        (source.root (limit.select index))) player)
    (source.root (limit.select index)) who
  have hnash := (limit.selectedRoot_endpointNash index who).1
  change (source.root (limit.select index) who false).toReal *
    difference ≤ error (limit.originalIndex index) at hnash
  have hadvantage : limit.selectedEndpointContinueAdvantage index who =
      -difference := by
    let block := source.block (limit.originalIndex index)
    have htail := limit.selectedBlockTail_eq_stationaryTerminalPayoff index
    dsimp only [difference]
    rw [← htail]
    simp only [selectedEndpointContinueAdvantage,
      quittingCyclicEndpointContinueAdvantage,
      quittingRootEndpointDifference]
    dsimp only [block, PeriodOneVanishingHazardSource.root,
      PeriodOneNormalizedSourceLimit.originalIndex]
    rw [Subsingleton.elim (finRotate 1 0) 0]
    ring
  rw [hadvantage]
  by_cases hdifference : 0 ≤ difference
  · have hweighted : (1 / 2 : ℝ) * difference ≤
        (source.root (limit.select index) who false).toReal * difference :=
      mul_le_mul_of_nonneg_right hcontinueHalf hdifference
    nlinarith [herrorPos (limit.originalIndex index)]
  · have : difference ≤ 0 := le_of_not_ge hdifference
    nlinarith [herrorPos (limit.originalIndex index)]

/-- If one limiting Continue advantage is strictly larger than another, its
selected Quit probability is asymptotically negligible relative to the
other player's Quit probability. -/
theorem selectedQuitProbability_ratio_tendsto_zero_of_limitingMargin_lt
    (limit : PeriodOneNormalizedSourceLimit source)
    (herrorPos : ∀ index, 0 < error index)
    (herror : Tendsto error atTop (nhds 0)) {low high : ι}
    (hmargin : limit.limitingSingletonMargin low <
      limit.limitingSingletonMargin high) :
    Tendsto (fun index ↦
      (source.root (limit.select index) high true).toReal /
        (source.root (limit.select index) low true).toReal)
      atTop (nhds 0) := by
  let selectedBlock : ∀ index, InteriorApproximateNashCyclicBlock reward 0
      (error (limit.originalIndex index)) :=
    fun index ↦ source.block (limit.originalIndex index)
  let quitPayoff : ℕ → ι → ℝ := fun index who ↦
    quittingRootQuitPayoff reward
      ((selectedBlock index).value (finRotate 1 0))
      ((selectedBlock index).cycle 0) who
  let continuePayoff : ℕ → ι → ℝ := fun index who ↦
    quittingRootContinuePayoff reward
      ((selectedBlock index).value (finRotate 1 0))
      ((selectedBlock index).cycle 0) who
  let separation :=
    (limit.limitingSingletonMargin high -
      limit.limitingSingletonMargin low) / 2
  have hseparation : 0 < separation := by
    dsimp only [separation]
    linarith
  have hlow : ∀ᶠ index in atTop,
      -2 * error (limit.originalIndex index) ≤
        continuePayoff index low - quitPayoff index low := by
    have hsource :=
      limit.eventually_neg_two_mul_error_le_selectedEndpointContinueAdvantage
        herrorPos low
    filter_upwards [hsource] with index hindex
    change -2 * error (limit.originalIndex index) ≤
      limit.selectedEndpointContinueAdvantage index low
    exact hindex
  have hhighTendsto : Tendsto (fun index ↦
      continuePayoff index high - quitPayoff index high) atTop
      (nhds (limit.limitingSingletonMargin high)) := by
    change Tendsto (fun index ↦
      limit.selectedEndpointContinueAdvantage index high) atTop _
    exact ((continuous_apply high).tendsto limit.limitingSingletonMargin).comp
      limit.selectedEndpointContinueAdvantage_tendsto_limitingSingletonMargin
  have hlowTendsto : Tendsto (fun index ↦
      continuePayoff index low - quitPayoff index low) atTop
      (nhds (limit.limitingSingletonMargin low)) := by
    change Tendsto (fun index ↦
      limit.selectedEndpointContinueAdvantage index low) atTop _
    exact ((continuous_apply low).tendsto limit.limitingSingletonMargin).comp
      limit.selectedEndpointContinueAdvantage_tendsto_limitingSingletonMargin
  have hdifference := hhighTendsto.sub hlowTendsto
  have hseparated : ∀ᶠ index in atTop,
      continuePayoff index low - quitPayoff index low + separation ≤
        continuePayoff index high - quitPayoff index high := by
    have heventual := hdifference.eventually
      (Ioi_mem_nhds (by
        dsimp only [separation]
        linarith : separation <
          limit.limitingSingletonMargin high -
            limit.limitingSingletonMargin low))
    exact heventual.mono fun _ hlt ↦ by linarith
  have hresponse :=
    tendsto_interiorBinaryApproximateResponse_ratio_zero_of_boundedLowAdvantage
      (fun index ↦ error (limit.originalIndex index))
      (fun index ↦ quitPayoff index high)
      (fun index ↦ continuePayoff index high)
      (fun index ↦ quitPayoff index low)
      (fun index ↦ continuePayoff index low)
      2 hseparation (fun index ↦ herrorPos (limit.originalIndex index))
      (limit.error_tendsto_zero herror) hlow hseparated
  apply hresponse.congr'
  exact Eventually.of_forall fun index ↦ by
    change interiorBinaryApproximateResponse
        (error (limit.originalIndex index))
          (quittingRootQuitPayoff reward
            ((source.block (limit.originalIndex index)).value (finRotate 1 0))
            ((source.block (limit.originalIndex index)).cycle 0) high)
          (quittingRootContinuePayoff reward
            ((source.block (limit.originalIndex index)).value (finRotate 1 0))
            ((source.block (limit.originalIndex index)).cycle 0) high) /
        interiorBinaryApproximateResponse
          (error (limit.originalIndex index))
          (quittingRootQuitPayoff reward
            ((source.block (limit.originalIndex index)).value (finRotate 1 0))
            ((source.block (limit.originalIndex index)).cycle 0) low)
          (quittingRootContinuePayoff reward
            ((source.block (limit.originalIndex index)).value (finRotate 1 0))
            ((source.block (limit.originalIndex index)).cycle 0) low) = _
    rw [← (source.block
      (limit.originalIndex index)).quitProbability_eq_response 0 high,
      ← (source.block
      (limit.originalIndex index)).quitProbability_eq_response 0 low]
    rfl

/-- Every player with positive limiting hazard share has a least limiting
Continue advantage among all players. -/
theorem limitingSingletonMargin_le_of_direction_pos
    (limit : PeriodOneNormalizedSourceLimit source)
    (herrorPos : ∀ index, 0 < error index)
    (herror : Tendsto error atTop (nhds 0)) {who : ι}
    (hwho : 0 < limit.direction.val who) (other : ι) :
    limit.limitingSingletonMargin who ≤
      limit.limitingSingletonMargin other := by
  by_contra hnot
  have hmargin : limit.limitingSingletonMargin other <
      limit.limitingSingletonMargin who := lt_of_not_ge hnot
  have hratio :=
    limit.selectedQuitProbability_ratio_tendsto_zero_of_limitingMargin_lt
      herrorPos herror hmargin
  let selectedDirection : ℕ → stdSimplex ℝ ι := fun index ↦
    quittingStationaryHazardDirection
      (source.root (limit.select index))
      (source.totalHazard_pos (limit.select index))
  have hdirectionZero : Tendsto
      (fun index ↦ (selectedDirection index).val who) atTop (nhds 0) := by
    apply squeeze_zero'
    · exact Eventually.of_forall fun index ↦
        (selectedDirection index).property.1 who
    · exact Eventually.of_forall fun index ↦ by
        have hotherLe :
            (source.root (limit.select index) other true).toReal ≤
              quittingStationaryTotalHazard
                (source.root (limit.select index)) := by
          unfold quittingStationaryTotalHazard
          exact Finset.single_le_sum
            (fun player _ ↦ ENNReal.toReal_nonneg
              (a := source.root (limit.select index) player true))
            (Finset.mem_univ other)
        exact div_le_div_of_nonneg_left
          (ENNReal.toReal_nonneg
            (a := source.root (limit.select index) who true))
          (source.quitProbability_pos (limit.select index) other) hotherLe
    · exact hratio
  have hdirectionLimit : Tendsto
      (fun index ↦ (selectedDirection index).val who) atTop
      (nhds (limit.direction.val who)) :=
    (((continuous_apply who).comp continuous_subtype_val).tendsto
      limit.direction).comp limit.direction_tendsto
  have hzero : limit.direction.val who = 0 :=
    tendsto_nhds_unique hdirectionLimit hdirectionZero
  linarith

/-- In a four-player counterexample every limiting singleton Continue
advantage is strictly positive. If one vanished, minimum-margin support would
make the limiting direction a homogeneous singleton-LCP solution, contrary
to the full-core standard-Q side. -/
theorem limitingSingletonMargin_pos_of_fourPlayer_noUniformPayoff
    (limit : PeriodOneNormalizedSourceLimit source)
    (hplayers : Fintype.card ι = 4)
    (hno : ¬ ∃ payoff : Payoff ι,
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff)
    (herrorPos : ∀ index, 0 < error index)
    (herror : Tendsto error atTop (nhds 0)) (who : ι) :
    0 < limit.limitingSingletonMargin who := by
  have hnonnegative := limit.limitingSingletonMargin_nonneg
    herrorPos herror who
  apply lt_of_le_of_ne hnonnegative
  intro hzero
  have hzero' : limit.limitingSingletonMargin who = 0 := hzero.symm
  have hfeasible : SingletonLCPFeasible (normalizedSoloMatrix reward) := by
    refine ⟨limit.direction,
      fun player ↦ limit.limitingSingletonMargin_nonneg
        herrorPos herror player, fun player ↦ ?_⟩
    by_cases hplayer : limit.direction.val player = 0
    · rw [hplayer, zero_mul]
    · have hplayerPos : 0 < limit.direction.val player :=
        lt_of_le_of_ne (limit.direction.property.1 player) (Ne.symm hplayer)
      have hle := limit.limitingSingletonMargin_le_of_direction_pos
        herrorPos herror hplayerPos who
      have hmarginZero : limit.limitingSingletonMargin player = 0 := by
        apply le_antisymm
        · simpa only [hzero'] using hle
        · exact limit.limitingSingletonMargin_nonneg herrorPos herror player
      change limit.direction.val player *
        limit.limitingSingletonMargin player = 0
      rw [hmarginZero, mul_zero]
  have hcore :=
    normalCore_eq_univ_of_fourPlayer_not_exists_uniformEquilibriumPayoff
      reward hplayers hno
  have hstandard :=
    standardQMatrixSide_of_not_exists_uniformEquilibriumPayoff reward hno
  apply hstandard.no_homogeneous
  have hprincipal :=
    (singletonLCPFeasible_normalPlayerMatrix_iff_of_normalCore_eq_univ
      (normalizedSoloMatrix reward) hcore).2 hfeasible
  simpa only [normalizedNormalPlayerMatrix] using hprincipal

/-- The limiting Continue advantages have one common positive minimum, and
every player with positive limiting hazard share attains it. -/
theorem exists_positive_commonMinimum_limitingSingletonMargin
    (limit : PeriodOneNormalizedSourceLimit source)
    (hplayers : Fintype.card ι = 4)
    (hno : ¬ ∃ payoff : Payoff ι,
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff)
    (herrorPos : ∀ index, 0 < error index)
    (herror : Tendsto error atTop (nhds 0)) :
    ∃ minimum : ℝ, 0 < minimum ∧
      (∀ who, minimum ≤ limit.limitingSingletonMargin who) ∧
      ∀ who, 0 < limit.direction.val who →
        limit.limitingSingletonMargin who = minimum := by
  have hsumPos : 0 < ∑ who, limit.direction.val who := by
    rw [limit.direction.property.2]
    norm_num
  obtain ⟨owner, _, howner⟩ :=
    (Finset.sum_pos_iff_of_nonneg
      (fun player _ ↦ limit.direction.property.1 player)).mp hsumPos
  refine ⟨limit.limitingSingletonMargin owner,
    limit.limitingSingletonMargin_pos_of_fourPlayer_noUniformPayoff
      hplayers hno herrorPos herror owner,
    fun who ↦ limit.limitingSingletonMargin_le_of_direction_pos
      herrorPos herror howner who, ?_⟩
  intro who hwho
  apply le_antisymm
  · exact limit.limitingSingletonMargin_le_of_direction_pos
      herrorPos herror hwho owner
  · exact limit.limitingSingletonMargin_le_of_direction_pos
      herrorPos herror howner who

/-- The limiting hazard direction has at least two distinct positive
coordinates. A unique positive coordinate would make the direction pure and
its normalized singleton residual equal the zero diagonal entry. -/
theorem exists_two_distinct_direction_positive
    (limit : PeriodOneNormalizedSourceLimit source)
    (hplayers : Fintype.card ι = 4)
    (hno : ¬ ∃ payoff : Payoff ι,
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff)
    (herrorPos : ∀ index, 0 < error index)
    (herror : Tendsto error atTop (nhds 0)) :
    ∃ first second : ι, first ≠ second ∧
      0 < limit.direction.val first ∧ 0 < limit.direction.val second := by
  have hsumPos : 0 < ∑ who, limit.direction.val who := by
    rw [limit.direction.property.2]
    norm_num
  obtain ⟨first, _, hfirst⟩ :=
    (Finset.sum_pos_iff_of_nonneg
      (fun player _ ↦ limit.direction.property.1 player)).mp hsumPos
  have hsecond : ∃ second, second ≠ first ∧
      0 < limit.direction.val second := by
    by_contra hnone
    push Not at hnone
    have hzero : ∀ second, second ≠ first →
        limit.direction.val second = 0 := by
      intro second hne
      exact le_antisymm (hnone second hne)
        (limit.direction.property.1 second)
    have hsumSingle : ∑ player, limit.direction.val player =
        limit.direction.val first := by
      exact Finset.sum_eq_single first
        (fun second _ hne ↦ hzero second hne)
        (fun hnotmem ↦ False.elim (hnotmem (Finset.mem_univ first)))
    have hfirstOne : limit.direction.val first = 1 := by
      rw [← hsumSingle, limit.direction.property.2]
    have hdirection : limit.direction = stdSimplex.pure (𝕜 := ℝ) first := by
      apply Subtype.ext
      funext player
      by_cases hplayer : player = first
      · subst player
        simp [hfirstOne]
      · rw [hzero player hplayer]
        simp [stdSimplex.pure_apply, hplayer]
    have hmarginZero : limit.limitingSingletonMargin first = 0 := by
      rw [limitingSingletonMargin, hdirection, singletonLCPResidual_def,
        wsum_pure_apply, normalizedSoloMatrix_diagonal]
    have hmarginPos :=
      limit.limitingSingletonMargin_pos_of_fourPlayer_noUniformPayoff
        hplayers hno herrorPos herror first
    linarith
  obtain ⟨second, hne, hsecondPos⟩ := hsecond
  exact ⟨first, second, hne.symm, hfirst, hsecondPos⟩

/-- Once a selected Continue advantage is nonnegative, that coordinate's
endpoint regret is exactly its Quit probability times the Continue
advantage. -/
theorem selectedCoordinateNashDefect_eq_quitProbability_mul_continueAdvantage
    (limit : PeriodOneNormalizedSourceLimit source)
    (index : ℕ) (who : ι)
    (hadvantage : 0 ≤ limit.selectedEndpointContinueAdvantage index who) :
    quittingRootCoordinateNashDefect reward
        ((source.block (limit.originalIndex index)).value (finRotate 1 0))
        ((source.block (limit.originalIndex index)).cycle 0) who =
      (source.root (limit.select index) who true).toReal *
        limit.selectedEndpointContinueAdvantage index who := by
  rw [quittingRootCoordinateNashDefect_eq_actionProbability_mul_posPart]
  have hdifference : quittingRootEndpointDifference reward
      ((source.block (limit.originalIndex index)).value (finRotate 1 0))
      ((source.block (limit.originalIndex index)).cycle 0) who =
    -limit.selectedEndpointContinueAdvantage index who := by
    simp only [selectedEndpointContinueAdvantage,
      quittingCyclicEndpointContinueAdvantage,
      quittingRootEndpointDifference]
    ring
  rw [hdifference]
  have hnegative : -limit.selectedEndpointContinueAdvantage index who ≤ 0 :=
    neg_nonpos.mpr hadvantage
  rw [max_eq_right hnegative, neg_neg, max_eq_left hadvantage, mul_zero,
    zero_add]
  rfl

/-- Eventually every selected limiting-row Continue advantage is positive,
and the normalized aggregate endpoint regret is the hazard-direction
weighted Continue advantage exactly. -/
theorem eventually_totalEndpointRegret_div_totalHazard_eq_directionWeightedAdvantage
    (limit : PeriodOneNormalizedSourceLimit source)
    (hplayers : Fintype.card ι = 4)
    (hno : ¬ ∃ payoff : Payoff ι,
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff)
    (herrorPos : ∀ index, 0 < error index)
    (herror : Tendsto error atTop (nhds 0)) :
    ∀ᶠ index in atTop,
      limit.selectedTotalEndpointRegret index /
          quittingStationaryTotalHazard (source.root (limit.select index)) =
        ∑ who, (quittingStationaryHazardDirection
            (source.root (limit.select index))
            (source.totalHazard_pos (limit.select index))).val who *
          limit.selectedEndpointContinueAdvantage index who := by
  have hallPositive : ∀ᶠ index in atTop, ∀ who,
      0 < limit.selectedEndpointContinueAdvantage index who := by
    apply Filter.eventually_all.mpr
    intro who
    have htendsto :=
      ((continuous_apply who).tendsto limit.limitingSingletonMargin).comp
        limit.selectedEndpointContinueAdvantage_tendsto_limitingSingletonMargin
    exact htendsto.eventually (Ioi_mem_nhds
      (limit.limitingSingletonMargin_pos_of_fourPlayer_noUniformPayoff
        hplayers hno herrorPos herror who))
  filter_upwards [hallPositive] with index hpositive
  unfold selectedTotalEndpointRegret quittingRootTotalNashDefect
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro who _
  rw [limit.selectedCoordinateNashDefect_eq_quitProbability_mul_continueAdvantage
    index who (hpositive who).le]
  change _ / _ = (_ / _) * _
  ring

/-- The aggregate endpoint-regret density converges to the same positive
minimum attained by every positive-share limiting player. -/
theorem exists_positive_commonMinimum_and_totalEndpointRegretDensity_tendsto
    (limit : PeriodOneNormalizedSourceLimit source)
    (hplayers : Fintype.card ι = 4)
    (hno : ¬ ∃ payoff : Payoff ι,
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff)
    (herrorPos : ∀ index, 0 < error index)
    (herror : Tendsto error atTop (nhds 0)) :
    ∃ minimum : ℝ, 0 < minimum ∧
      (∀ who, minimum ≤ limit.limitingSingletonMargin who) ∧
      (∀ who, 0 < limit.direction.val who →
        limit.limitingSingletonMargin who = minimum) ∧
      Tendsto (fun index ↦ limit.selectedTotalEndpointRegret index /
        quittingStationaryTotalHazard (source.root (limit.select index)))
        atTop (nhds minimum) := by
  obtain ⟨minimum, hminimumPos, hminimum, hequal⟩ :=
    limit.exists_positive_commonMinimum_limitingSingletonMargin
      hplayers hno herrorPos herror
  refine ⟨minimum, hminimumPos, hminimum, hequal, ?_⟩
  let selectedDirection : ℕ → stdSimplex ℝ ι := fun index ↦
    quittingStationaryHazardDirection
      (source.root (limit.select index))
      (source.totalHazard_pos (limit.select index))
  have hweighted : Tendsto (fun index ↦
      ∑ who, (selectedDirection index).val who *
        limit.selectedEndpointContinueAdvantage index who) atTop
      (nhds (∑ who, limit.direction.val who *
        limit.limitingSingletonMargin who)) := by
    exact tendsto_finsetSum Finset.univ fun who _ ↦
      ((((continuous_apply who).comp continuous_subtype_val).tendsto
        limit.direction).comp limit.direction_tendsto).mul
        (((continuous_apply who).tendsto limit.limitingSingletonMargin).comp
          limit.selectedEndpointContinueAdvantage_tendsto_limitingSingletonMargin)
  have hsum : ∑ who, limit.direction.val who *
      limit.limitingSingletonMargin who = minimum := by
    calc
      (∑ who, limit.direction.val who *
          limit.limitingSingletonMargin who) =
          ∑ who, limit.direction.val who * minimum := by
        apply Finset.sum_congr rfl
        intro who _
        by_cases hzero : limit.direction.val who = 0
        · rw [hzero, zero_mul, zero_mul]
        · have hpos : 0 < limit.direction.val who :=
            lt_of_le_of_ne (limit.direction.property.1 who) (Ne.symm hzero)
          rw [hequal who hpos]
      _ = minimum := by
        rw [← Finset.sum_mul, limit.direction.property.2, one_mul]
  rw [← hsum]
  apply hweighted.congr'
  exact Filter.EventuallyEq.symm
    (limit.eventually_totalEndpointRegret_div_totalHazard_eq_directionWeightedAdvantage
      hplayers hno herrorPos herror)

end PeriodOneNormalizedSourceLimit

end GameTheory
