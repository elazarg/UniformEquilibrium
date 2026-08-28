/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Research.Quitting.ForwardExactCapTailFlow
import MathUE.Analysis.SummableTailAverage
import UniformEquilibrium.Quitting.Root.FirstOrderProductFlow

/-!
# First-order estimates for a forward exact-cap tail

This module supplies the analytic bridge deliberately left out of
`ForwardExactCapTailFlow`.  The product estimates come from the exact
finite-product laws, and the weighted-tail arguments compile them into an
unconditional normalized cap-flow certificate.
-/

noncomputable section

namespace GameTheory

open Filter Math.Probability Set

variable {ι : Type} [Fintype ι] [DecidableEq ι]

namespace QuittingForwardExactCapTail

variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}

/-- Exact nonlinear remainder after subtracting the singleton first-order
expansion of one cap update. -/
def capProductRemainder
    (ray : QuittingForwardExactCapTail reward) (time : ℕ) (who : ι) : ℝ :=
    (ray.pair (time + 1)).2 who - (ray.pair time).2 who -
    ∑ owner, quittingRootQuitRates (ray.root time) owner *
      QuittingLCPClassification.normalizedSoloMatrix reward who owner -
    ray.totalHazard time *
      (quittingSoloReward reward who who - (ray.pair time).2 who)

/-- Normalized cap-flow error.  The second term changes the moving cap
baseline in the singleton expansion to the fixed diagonal singleton reward. -/
def canonicalCapFlowError
    (ray : QuittingForwardExactCapTail reward) (time : ℕ) (who : ι) : ℝ :=
  ray.capProductRemainder time who / ray.totalHazard time +
    (quittingSoloReward reward who who - (ray.pair time).2 who)

theorem abs_capProductRemainder_le
    (ray : QuittingForwardExactCapTail reward) (time : ℕ) (who : ι) :
    |ray.capProductRemainder time who| ≤
      2 * quittingRewardBound reward * ray.totalHazard time ^ 2 := by
  have hnext : (ray.pair (time + 1)).2 =
      quittingRootSuccessorPayoff reward (ray.pair time).2
        (ray.root time) := by
    rw [ray.forward]
    exact
      quittingTerminalSemanticPrefix_envelope_eq_rootSuccessorPayoff_of_capNash
        (ray.pair time) (ray.root time) (ray.exactNash time)
  have hbox := quittingTerminalSemanticCarrier_mem_box reward
    (ray.pair time) (abs_reward_le_quittingRewardBound reward)
    (ray.pair_mem time)
  unfold capProductRemainder
  rw [hnext]
  simpa only [totalHazard] using
    abs_quittingRootSuccessorPayoff_sub_tail_sub_normalizedSoloFlow_sub_baseline_le
      reward (ray.pair time).2 (ray.root time) who
      (abs_reward_le_quittingRewardBound reward)
      (abs_le.mpr ⟨hbox.2.1 who, hbox.2.2 who⟩)

theorem cap_increment_eq_normalizedSolo_add_error
    (ray : QuittingForwardExactCapTail reward) (time : ℕ) (who : ι) :
    (ray.pair (time + 1)).2 who - (ray.pair time).2 who =
      ray.totalHazard time *
        ((∑ owner, QuittingLCPClassification.normalizedSoloMatrix reward who owner *
          ray.currentHazard time owner) + ray.canonicalCapFlowError time who) := by
  let epsilon := ray.totalHazard time
  let singleton := quittingSoloReward reward who who
  have hepsilon : epsilon ≠ 0 := (ray.totalHazard_pos time).ne'
  have hrate : ∀ owner,
      quittingRootQuitRates (ray.root time) owner =
        epsilon * ray.currentHazard time owner := by
    intro owner
    exact ray.quitRate_eq_totalHazard_mul_currentHazard time owner
  have hlinear :
      epsilon *
          (∑ owner,
            QuittingLCPClassification.normalizedSoloMatrix reward who owner *
              ray.currentHazard time owner) =
      ∑ owner, quittingRootQuitRates (ray.root time) owner *
        QuittingLCPClassification.normalizedSoloMatrix reward who owner := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro owner _
    rw [hrate owner]
    ring
  unfold canonicalCapFlowError
  rw [mul_add, mul_add, mul_div_cancel₀ _ hepsilon]
  unfold capProductRemainder
  dsimp only [epsilon, singleton] at hlinear
  nlinarith [hlinear]

theorem canonicalCapFlowError_tendsto_zero
    (ray : QuittingForwardExactCapTail reward) (who : ι)
    (hbinding : who ∈ ray.bindingFinset) :
    Tendsto (fun time ↦ ray.canonicalCapFlowError time who)
      atTop (nhds 0) := by
  have hepsilon := ray.totalHazard_summable.tendsto_atTop_zero
  have hquotient : Tendsto (fun time ↦
      ray.capProductRemainder time who / ray.totalHazard time)
      atTop (nhds 0) := by
    apply (tendsto_zero_iff_abs_tendsto_zero _).2
    refine squeeze_zero (g := fun time ↦
      2 * quittingRewardBound reward * ray.totalHazard time)
      (fun time ↦ abs_nonneg _) (fun time ↦ ?_) ?_
    · change |ray.capProductRemainder time who / ray.totalHazard time| ≤ _
      rw [abs_div]
      have habsEpsilon : |ray.totalHazard time| = ray.totalHazard time :=
        abs_of_pos (ray.totalHazard_pos time)
      rw [habsEpsilon]
      apply (div_le_iff₀ (ray.totalHazard_pos time)).2
      change |ray.capProductRemainder time who| ≤
        (2 * quittingRewardBound reward * ray.totalHazard time) *
          ray.totalHazard time
      have hbound := ray.abs_capProductRemainder_le time who
      nlinarith [ray.totalHazard_nonneg time,
        quittingRewardBound_nonneg reward]
    · simpa using hepsilon.const_mul (2 * quittingRewardBound reward)
  have hbindingEq : ray.capLimit who =
      quittingSoloReward reward who who := by
    change ray.capLimit who = reward (quittingSingletonTerminal who) who
    exact (Finset.mem_filter.mp hbinding).2
  have hbaseline : Tendsto (fun time ↦
      quittingSoloReward reward who who - (ray.pair time).2 who)
      atTop (nhds 0) := by
    have hconst : Tendsto
        (fun _ : ℕ ↦ quittingSoloReward reward who who) atTop
        (nhds (quittingSoloReward reward who who)) := tendsto_const_nhds
    have hsub := hconst.sub (ray.cap_tendsto who)
    simpa only [hbindingEq, sub_self] using hsub
  simpa [canonicalCapFlowError] using hquotient.add hbaseline

/-- Remainder after subtracting the singleton gap and the canonical
off-diagonal collision linearization from the exact endpoint difference. -/
def endpointProductRemainder
    (ray : QuittingForwardExactCapTail reward) (time : ℕ) (who : ι) : ℝ :=
  quittingRootEndpointDifference reward (ray.pair time).2
      (ray.root time) who -
    (quittingSoloReward reward who who - (ray.pair time).2 who) -
    ∑ owner, quittingRootQuitRates (ray.root time) owner *
      quittingCollisionMatrix reward who owner

/-- Pointwise quantitative endpoint estimate needed by the normalized-flow
compiler. -/
def HasCanonicalEndpointProductRemainderBound
    (ray : QuittingForwardExactCapTail reward) : Prop :=
  ∀ time who,
    |ray.endpointProductRemainder time who| ≤
      ray.totalHazard time *
          |(ray.pair time).2 who - quittingSoloReward reward who who| +
        4 * quittingRewardBound reward * ray.totalHazard time ^ 2

/-- The exact finite-product endpoint law supplies the required local
quadratic estimate for every forward exact-cap tail. -/
theorem hasCanonicalEndpointProductRemainderBound
    (ray : QuittingForwardExactCapTail reward) :
    HasCanonicalEndpointProductRemainderBound ray := by
  intro time who
  have hbox := quittingTerminalSemanticCarrier_mem_box reward
    (ray.pair time) (abs_reward_le_quittingRewardBound reward)
    (ray.pair_mem time)
  simpa only [endpointProductRemainder, totalHazard] using
    abs_quittingRootEndpointDifference_sub_solo_sub_tail_sub_collisionFlow_le
      reward (ray.pair time).2 (ray.root time) who
      (abs_reward_le_quittingRewardBound reward)
      (abs_le.mpr ⟨hbox.2.1 who, hbox.2.2 who⟩)

/-- Exact endpoint slack.  The `max` handles the finitely many possible
sure-Quit rows without asserting that their endpoint difference is
nonpositive. -/
def canonicalEndpointSlack
    (ray : QuittingForwardExactCapTail reward) (time : ℕ) (who : ι) : ℝ :=
  max 0 (-quittingRootEndpointDifference reward (ray.pair time).2
    (ray.root time) who / ray.totalHazard time)

/-- Local normalized endpoint remainder. -/
def canonicalLocalCollisionError
    (ray : QuittingForwardExactCapTail reward) (time : ℕ) (who : ι) : ℝ :=
  -ray.endpointProductRemainder time who / ray.totalHazard time

theorem canonicalEndpointSlack_nonneg
    (ray : QuittingForwardExactCapTail reward) (time : ℕ) (who : ι) :
    0 ≤ ray.canonicalEndpointSlack time who :=
  le_max_left _ _

theorem currentHazard_mul_canonicalEndpointSlack
    (ray : QuittingForwardExactCapTail reward) (time : ℕ) (who : ι) :
    ray.currentHazard time who * ray.canonicalEndpointSlack time who = 0 := by
  have hnash := (isZeroQuittingRootEndpointNash_iff_isZeroQuittingRootNash
    reward (ray.pair time).2 (ray.root time)).2 (ray.exactNash time)
  by_cases hquit : quittingRootQuitRates (ray.root time) who = 0
  · have hcurrent : ray.currentHazard time who = 0 := by
      have hrate := ray.quitRate_eq_totalHazard_mul_currentHazard time who
      rw [hquit] at hrate
      exact (mul_eq_zero.mp hrate.symm).resolve_left
        (ray.totalHazard_pos time).ne'
    rw [hcurrent, zero_mul]
  · have hquitPos : 0 < (ray.root time who true).toReal := by
      change 0 < quittingRootQuitRates (ray.root time) who
      exact lt_of_le_of_ne ENNReal.toReal_nonneg (Ne.symm hquit)
    by_cases hcontinue : (ray.root time who false).toReal = 0
    · have hdiff :=
        quittingRootEndpointDifference_nonneg_of_continueProbability_eq_zero
          reward (ray.pair time).2 (ray.root time) who hnash hcontinue
      have hratio :
          -quittingRootEndpointDifference reward (ray.pair time).2
              (ray.root time) who / ray.totalHazard time ≤ 0 :=
        div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hdiff)
          (ray.totalHazard_nonneg time)
      simp [canonicalEndpointSlack, max_eq_left hratio]
    · have hcontinuePos : 0 < (ray.root time who false).toReal :=
        lt_of_le_of_ne ENNReal.toReal_nonneg (Ne.symm hcontinue)
      have hdiff :=
        quittingRootEndpointDifference_eq_zero_of_both_probabilities_pos
          reward (ray.pair time).2 (ray.root time) who hnash
          hcontinuePos hquitPos
      simp [canonicalEndpointSlack, hdiff]

theorem eventually_canonicalEndpointSlack_eq_neg_div
    (ray : QuittingForwardExactCapTail reward) (who : ι) :
    ∀ᶠ time in atTop,
      ray.canonicalEndpointSlack time who =
        -quittingRootEndpointDifference reward (ray.pair time).2
          (ray.root time) who / ray.totalHazard time := by
  have hepsilon := ray.totalHazard_summable.tendsto_atTop_zero
  have hsmall : ∀ᶠ time in atTop, ray.totalHazard time < 1 :=
    (tendsto_order.1 hepsilon).2 1 zero_lt_one
  filter_upwards [hsmall] with time htime
  have hquitLe : quittingRootQuitRates (ray.root time) who ≤
      ray.totalHazard time := by
    unfold totalHazard
    apply Finset.single_le_sum
    · intro owner _
      exact ENNReal.toReal_nonneg
    · exact Finset.mem_univ who
  have hcontinuePos : 0 < (ray.root time who false).toReal := by
    have hsum := quittingRoot_continueProbability_add_quitProbability
      (ray.root time) who
    change (ray.root time who true).toReal ≤ ray.totalHazard time at hquitLe
    linarith
  have hnash := (isZeroQuittingRootEndpointNash_iff_isZeroQuittingRootNash
    reward (ray.pair time).2 (ray.root time)).2 (ray.exactNash time)
  have hdiff : quittingRootEndpointDifference reward (ray.pair time).2
      (ray.root time) who ≤ 0 := by
    have hweighted := (hnash who).1
    exact nonpos_of_mul_nonpos_left (by simpa [mul_comm] using hweighted)
      hcontinuePos
  unfold canonicalEndpointSlack
  rw [max_eq_right]
  exact div_nonneg (neg_nonneg.mpr hdiff) (ray.totalHazard_nonneg time)

theorem canonicalLocalCollisionError_tendsto_zero
    (ray : QuittingForwardExactCapTail reward)
    (who : ι) (hbinding : who ∈ ray.bindingFinset) :
    Tendsto (fun time ↦ ray.canonicalLocalCollisionError time who)
      atTop (nhds 0) := by
  have hepsilon := ray.totalHazard_summable.tendsto_atTop_zero
  have hbindingEq : ray.capLimit who =
      quittingSoloReward reward who who := by
    change ray.capLimit who = reward (quittingSingletonTerminal who) who
    exact (Finset.mem_filter.mp hbinding).2
  have hgap : Tendsto (fun time ↦
      |(ray.pair time).2 who - quittingSoloReward reward who who|)
      atTop (nhds 0) := by
    have hsub := (ray.cap_tendsto who).sub_const
      (quittingSoloReward reward who who)
    simpa only [hbindingEq, sub_self, abs_zero] using hsub.abs
  apply (tendsto_zero_iff_abs_tendsto_zero _).2
  refine squeeze_zero (g := fun time ↦
    |(ray.pair time).2 who - quittingSoloReward reward who who| +
      4 * quittingRewardBound reward * ray.totalHazard time)
    (fun time ↦ abs_nonneg _) (fun time ↦ ?_) ?_
  · change |-ray.endpointProductRemainder time who /
      ray.totalHazard time| ≤ _
    rw [abs_div, abs_neg]
    have habsEpsilon : |ray.totalHazard time| = ray.totalHazard time :=
      abs_of_pos (ray.totalHazard_pos time)
    rw [habsEpsilon]
    apply (div_le_iff₀ (ray.totalHazard_pos time)).2
    change |ray.endpointProductRemainder time who| ≤
      (|(ray.pair time).2 who - quittingSoloReward reward who who| +
        4 * quittingRewardBound reward * ray.totalHazard time) *
          ray.totalHazard time
    have hbound := ray.hasCanonicalEndpointProductRemainderBound time who
    nlinarith [ray.totalHazard_nonneg time,
      quittingRewardBound_nonneg reward]
  · simpa only [zero_add] using hgap.add (by
      simpa using hepsilon.const_mul (4 * quittingRewardBound reward))

theorem renewalRatio_nonneg
    (ray : QuittingForwardExactCapTail reward) (time : ℕ) :
    0 ≤ ray.renewalRatio time :=
  div_nonneg (ray.totalHazard_nonneg time) (ray.tailMass_pos time).le

theorem renewalRatio_le_one
    (ray : QuittingForwardExactCapTail reward) (time : ℕ) :
    ray.renewalRatio time ≤ 1 := by
  apply (div_le_iff₀ (ray.tailMass_pos time)).2
  nlinarith [ray.tailMass_eq_add_succ time, ray.tailMass_pos (time + 1)]

/-- Exact residual which makes the endpoint decomposition literal at every
date, including finitely many possible sure-Quit rows. -/
def canonicalCollisionError
    (ray : QuittingForwardExactCapTail reward) (time : ℕ) (who : ι) : ℝ :=
  ray.renewalRatio time * ray.canonicalEndpointSlack time who +
    (ray.capLimit who - (ray.pair time).2 who) / ray.tailMass time +
    ray.renewalRatio time *
      ∑ owner, quittingCollisionMatrix reward who owner *
        ray.currentHazard time owner

theorem canonicalEndpoint_decomposition
    (ray : QuittingForwardExactCapTail reward) (time : ℕ) (who : ι) :
    ray.renewalRatio time * ray.canonicalEndpointSlack time who =
      -((ray.capLimit who - (ray.pair time).2 who) / ray.tailMass time) -
        ray.renewalRatio time *
          (∑ owner, quittingCollisionMatrix reward who owner *
            ray.currentHazard time owner) +
        ray.canonicalCollisionError time who := by
  unfold canonicalCollisionError
  ring

theorem eventually_canonicalCollisionError_eq_renewalRatio_mul_local
    (ray : QuittingForwardExactCapTail reward) (who : ι)
    (hbinding : who ∈ ray.bindingFinset) :
    ∀ᶠ time in atTop,
      ray.canonicalCollisionError time who =
        ray.renewalRatio time * ray.canonicalLocalCollisionError time who := by
  filter_upwards [ray.eventually_canonicalEndpointSlack_eq_neg_div who]
    with time hslack
  have hbindingEq : ray.capLimit who =
      quittingSoloReward reward who who := by
    change ray.capLimit who = reward (quittingSingletonTerminal who) who
    exact (Finset.mem_filter.mp hbinding).2
  have hmatrix :
      ∑ owner, quittingRootQuitRates (ray.root time) owner *
          quittingCollisionMatrix reward who owner =
        ray.totalHazard time *
          ∑ owner, quittingCollisionMatrix reward who owner *
            ray.currentHazard time owner := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro owner _
    rw [ray.quitRate_eq_totalHazard_mul_currentHazard]
    ring
  have hepsilon : ray.totalHazard time ≠ 0 :=
    (ray.totalHazard_pos time).ne'
  have htail : ray.tailMass time ≠ 0 := (ray.tailMass_pos time).ne'
  unfold canonicalCollisionError canonicalLocalCollisionError renewalRatio
  rw [hslack, hbindingEq]
  unfold endpointProductRemainder
  field_simp [hepsilon, htail]
  nlinarith [hmatrix]

theorem canonicalCollisionError_tendsto_zero
    (ray : QuittingForwardExactCapTail reward)
    (who : ι) (hbinding : who ∈ ray.bindingFinset) :
    Tendsto (fun time ↦ ray.canonicalCollisionError time who)
      atTop (nhds 0) := by
  have hlocal := ray.canonicalLocalCollisionError_tendsto_zero
    who hbinding
  have habsLocal : Tendsto (fun time ↦
      |ray.canonicalLocalCollisionError time who|) atTop (nhds 0) := by
    simpa only [abs_zero] using hlocal.abs
  have hproduct : Tendsto (fun time ↦
      ray.renewalRatio time * ray.canonicalLocalCollisionError time who)
      atTop (nhds 0) := by
    apply (tendsto_zero_iff_abs_tendsto_zero _).2
    refine squeeze_zero (fun time ↦ abs_nonneg _) (fun time ↦ ?_) habsLocal
    change |ray.renewalRatio time *
      ray.canonicalLocalCollisionError time who| ≤ _
    rw [abs_mul]
    have hratioAbs : |ray.renewalRatio time| = ray.renewalRatio time :=
      abs_of_nonneg (ray.renewalRatio_nonneg time)
    rw [hratioAbs]
    exact mul_le_of_le_one_left (abs_nonneg _)
      (ray.renewalRatio_le_one time)
  exact hproduct.congr' (Filter.EventuallyEq.symm
    (ray.eventually_canonicalCollisionError_eq_renewalRatio_mul_local
      who hbinding))

theorem weightedCanonicalCapFlowError_summable
    (ray : QuittingForwardExactCapTail reward) (who : ι)
    (hbinding : who ∈ ray.bindingFinset) :
    Summable (fun time ↦
      ray.totalHazard time * ray.canonicalCapFlowError time who) :=
  Math.summable_weight_mul_of_nonneg_of_tendsto_zero ray.totalHazard
    (fun time ↦ ray.canonicalCapFlowError time who)
    ray.totalHazard_nonneg ray.totalHazard_summable
    (ray.canonicalCapFlowError_tendsto_zero who hbinding)

private theorem weightedSoloMatrixCurrent_summable
    (ray : QuittingForwardExactCapTail reward) (who : ι) (start : ℕ) :
    Summable (fun offset ↦
      ray.totalHazard (start + offset) *
        ∑ owner,
          QuittingLCPClassification.normalizedSoloMatrix reward who owner *
            ray.currentHazard (start + offset) owner) := by
  have hsum : Summable (fun offset ↦
      ∑ owner,
        QuittingLCPClassification.normalizedSoloMatrix reward who owner *
          (ray.totalHazard (start + offset) *
            ray.currentHazard (start + offset) owner)) := by
    apply summable_sum
    intro owner _
    exact (ray.weightedCurrentHazard_summable start owner).mul_left
      (QuittingLCPClassification.normalizedSoloMatrix reward who owner)
  have heq : (fun offset ↦
      ray.totalHazard (start + offset) *
        ∑ owner,
          QuittingLCPClassification.normalizedSoloMatrix reward who owner *
            ray.currentHazard (start + offset) owner) =
      (fun offset ↦
        ∑ owner,
          QuittingLCPClassification.normalizedSoloMatrix reward who owner *
            (ray.totalHazard (start + offset) *
              ray.currentHazard (start + offset) owner)) := by
    funext offset
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro owner _
    ring
  rw [heq]
  exact hsum

theorem capIncrement_summable
    (ray : QuittingForwardExactCapTail reward) (who : ι)
    (hbinding : who ∈ ray.bindingFinset) :
    Summable (fun time ↦
      (ray.pair (time + 1)).2 who - (ray.pair time).2 who) := by
  have hmatrix : Summable (fun time ↦
      ray.totalHazard time *
        ∑ owner,
          QuittingLCPClassification.normalizedSoloMatrix reward who owner *
            ray.currentHazard time owner) := by
    simpa only [Nat.zero_add] using
      ray.weightedSoloMatrixCurrent_summable who 0
  have herror := ray.weightedCanonicalCapFlowError_summable who hbinding
  have htotal := hmatrix.add herror
  apply htotal.congr
  intro time
  rw [ray.cap_increment_eq_normalizedSolo_add_error]
  ring

theorem capGap_eq_soloTailFlow_add_errorTail
    (ray : QuittingForwardExactCapTail reward) (who : ι)
    (hbinding : who ∈ ray.bindingFinset) (start : ℕ) :
    ray.capLimit who - (ray.pair start).2 who =
      (∑ owner,
        QuittingLCPClassification.normalizedSoloMatrix reward who owner *
          ray.tailFlow start owner) +
        ∑' offset, ray.totalHazard (start + offset) *
          ray.canonicalCapFlowError (start + offset) who := by
  have hincrements : Summable (fun offset ↦
      (ray.pair (start + offset + 1)).2 who -
        (ray.pair (start + offset)).2 who) := by
    simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
      (summable_nat_add_iff start).2
        (ray.capIncrement_summable who hbinding)
  have htelescope := Math.hasSum_forwardDifference
    (fun time ↦ (ray.pair time).2 who) (ray.capLimit who)
    (ray.cap_tendsto who) start hincrements
  have hmatrix := ray.weightedSoloMatrixCurrent_summable who start
  have herror : Summable (fun offset ↦
      ray.totalHazard (start + offset) *
        ray.canonicalCapFlowError (start + offset) who) := by
    simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
      (summable_nat_add_iff start).2
        (ray.weightedCanonicalCapFlowError_summable who hbinding)
  have hsum :
      (∑' offset,
        ((ray.pair (start + offset + 1)).2 who -
          (ray.pair (start + offset)).2 who)) =
      (∑' offset,
        ray.totalHazard (start + offset) *
          ∑ owner,
            QuittingLCPClassification.normalizedSoloMatrix reward who owner *
              ray.currentHazard (start + offset) owner) +
        ∑' offset, ray.totalHazard (start + offset) *
          ray.canonicalCapFlowError (start + offset) who := by
    rw [← hmatrix.tsum_add herror]
    apply tsum_congr
    intro offset
    rw [ray.cap_increment_eq_normalizedSolo_add_error]
    ring
  have hmatrixTsum :
      (∑' offset,
        ray.totalHazard (start + offset) *
          ∑ owner,
            QuittingLCPClassification.normalizedSoloMatrix reward who owner *
              ray.currentHazard (start + offset) owner) =
      ∑ owner,
        QuittingLCPClassification.normalizedSoloMatrix reward who owner *
          ray.tailFlow start owner := by
    calc
      (∑' offset,
          ray.totalHazard (start + offset) *
            ∑ owner,
              QuittingLCPClassification.normalizedSoloMatrix reward who owner *
                ray.currentHazard (start + offset) owner) =
          ∑' offset,
            ∑ owner,
              QuittingLCPClassification.normalizedSoloMatrix reward who owner *
                (ray.totalHazard (start + offset) *
                  ray.currentHazard (start + offset) owner) := by
            apply tsum_congr
            intro offset
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro owner _
            ring
      _ = ∑ owner,
          ∑' offset,
            QuittingLCPClassification.normalizedSoloMatrix reward who owner *
              (ray.totalHazard (start + offset) *
                ray.currentHazard (start + offset) owner) := by
            rw [Summable.tsum_finsetSum]
            intro owner _
            exact (ray.weightedCurrentHazard_summable start owner).mul_left _
      _ = ∑ owner,
          QuittingLCPClassification.normalizedSoloMatrix reward who owner *
            ray.tailFlow start owner := by
            apply Finset.sum_congr rfl
            intro owner _
            rw [tsum_mul_left]
            rfl
  rw [← htelescope.tsum_eq, hsum, hmatrixTsum]

theorem capGap_div_tailMass_sub_soloTailAverage_eq_errorTailAverage
    (ray : QuittingForwardExactCapTail reward) (who : ι)
    (hbinding : who ∈ ray.bindingFinset) (start : ℕ) :
    (ray.capLimit who - (ray.pair start).2 who) / ray.tailMass start -
        ∑ owner,
          QuittingLCPClassification.normalizedSoloMatrix reward who owner *
            ray.tailAverage start owner =
      (∑' offset, ray.totalHazard (start + offset) *
        ray.canonicalCapFlowError (start + offset) who) /
          ray.tailMass start := by
  have hgap := ray.capGap_eq_soloTailFlow_add_errorTail
    who hbinding start
  unfold tailAverage
  have hmatrixDiv :
      (∑ owner,
        QuittingLCPClassification.normalizedSoloMatrix reward who owner *
          (ray.tailFlow start owner / ray.tailMass start)) =
      (∑ owner,
        QuittingLCPClassification.normalizedSoloMatrix reward who owner *
          ray.tailFlow start owner) / ray.tailMass start := by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro owner _
    ring
  rw [hmatrixDiv]
  field_simp [(ray.tailMass_pos start).ne']
  linear_combination hgap

theorem tailNormalized_capFlow_tendsto
    (ray : QuittingForwardExactCapTail reward) (who : ι)
    (hbinding : who ∈ ray.bindingFinset) :
    Tendsto (fun start ↦
      (ray.capLimit who - (ray.pair start).2 who) / ray.tailMass start -
        ∑ owner,
          QuittingLCPClassification.normalizedSoloMatrix reward who owner *
            ray.tailAverage start owner) atTop (nhds 0) := by
  have hweighted := Math.weightedTailAverage_tendsto_zero
    ray.totalHazard (fun time ↦ ray.canonicalCapFlowError time who)
    ray.totalHazard_nonneg ray.totalHazard_summable ray.tailMass_pos
    (ray.canonicalCapFlowError_tendsto_zero who hbinding)
  exact hweighted.congr' (Eventually.of_forall fun start ↦
    (ray.capGap_div_tailMass_sub_soloTailAverage_eq_errorTailAverage
      who hbinding start).symm)

/-- The exact normalized-flow certificate compiled from the product estimates.
The cap product error, telescope, slack, and complementarity are all
constructed from `ray`. -/
def tailNormalizedCapFlow
    (ray : QuittingForwardExactCapTail reward) :
    QuittingTailNormalizedCapFlow reward ray where
  soloMatrix := QuittingLCPClassification.normalizedSoloMatrix reward
  collisionMatrix := quittingCollisionMatrix reward
  endpointSlack := ray.canonicalEndpointSlack
  capFlowError := ray.canonicalCapFlowError
  collisionError := ray.canonicalCollisionError
  cap_increment := ray.cap_increment_eq_normalizedSolo_add_error
  endpoint_decomposition := ray.canonicalEndpoint_decomposition
  endpointSlack_nonneg := ray.canonicalEndpointSlack_nonneg
  current_complementarity := ray.currentHazard_mul_canonicalEndpointSlack
  capFlowError_tendsto_zero := ray.canonicalCapFlowError_tendsto_zero
  collisionError_tendsto_zero := ray.canonicalCollisionError_tendsto_zero
  tailNormalized_capFlow := ray.tailNormalized_capFlow_tendsto

/-- Existential form of the unconditional product-expansion compiler. -/
theorem exists_productExpansionErrors
    (ray : QuittingForwardExactCapTail reward) :
    ∃ flow : QuittingTailNormalizedCapFlow reward ray,
      flow.soloMatrix =
          QuittingLCPClassification.normalizedSoloMatrix reward ∧
        flow.collisionMatrix = quittingCollisionMatrix reward := by
  exact ⟨ray.tailNormalizedCapFlow, rfl, rfl⟩

end QuittingForwardExactCapTail

end GameTheory
