/-
Copyright (c) 2026 UniformEquilibrium contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: UniformEquilibrium contributors
-/

import UniformEquilibrium.Quitting.Cycles.PeriodOneVanishingHazardEndpointLimits
import UniformEquilibrium.Quitting.Stationary.CompleteEndpointChoices
import UniformEquilibrium.Quitting.Stationary.TerminalCoalitionLaw

/-! # Literal stationary subsets of a period-one source

Only removed positive-share owners are replaced by Never. Every zero-share
outsider retains its exact original source hazard, not merely its limit.
-/

noncomputable section

namespace GameTheory.PeriodOneNormalizedSourceLimit

open Filter Math.Probability
open scoped Topology

variable {ι : Type} [Fintype ι] [DecidableEq ι] [Nontrivial ι]
  {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
  {error : ℕ → ℝ} {source : PeriodOneVanishingHazardSource reward error}

def positiveSupport (limit : PeriodOneNormalizedSourceLimit source) : Finset ι :=
  Finset.univ.filter fun who ↦ 0 < limit.direction.val who

def subsetMass (limit : PeriodOneNormalizedSourceLimit source) (retained : Finset ι) : ℝ :=
  ∑ who ∈ retained, limit.direction.val who

def subsetValue (limit : PeriodOneNormalizedSourceLimit source) (retained : Finset ι) : Payoff ι :=
  fun who ↦ (∑ owner ∈ retained, limit.direction.val owner * quittingSoloReward reward owner who) /
    limit.subsetMass retained

/-- Exact retained source root. A zero-share outsider remains active. -/
def subsetRoot (limit : PeriodOneNormalizedSourceLimit source) (retained : Finset ι)
    (index : ℕ) (who : ι) : PMF Bool :=
  if who ∈ retained ∨ limit.direction.val who = 0 then source.root (limit.select index) who
  else PMF.pure false

def subsetProfile (limit : PeriodOneNormalizedSourceLimit source) (retained : Finset ι)
    (index : ℕ) : (quittingGame reward).BehaviorProfile :=
  quittingStationaryProfile reward (limit.subsetRoot retained index)

theorem subsetRoot_zeroShare (limit : PeriodOneNormalizedSourceLimit source)
    (retained : Finset ι) (index : ℕ) {who : ι} (hzero : limit.direction.val who = 0) :
    limit.subsetRoot retained index who = source.root (limit.select index) who := by
  simp [subsetRoot, hzero]

theorem subsetRoot_positiveSupport (limit : PeriodOneNormalizedSourceLimit source) (index : ℕ) :
    limit.subsetRoot limit.positiveSupport index = source.root (limit.select index) := by
  funext who
  by_cases hpos : 0 < limit.direction.val who
  · simp [subsetRoot, positiveSupport, hpos]
  · have hzero := le_antisymm (not_lt.mp hpos) (limit.direction.property.1 who)
    simp [subsetRoot, hzero]

theorem subsetProfile_positiveSupport (limit : PeriodOneNormalizedSourceLimit source) (index : ℕ) :
    limit.subsetProfile limit.positiveSupport index = source.profile (limit.select index) := by
  rw [subsetProfile, subsetRoot_positiveSupport, limit.selectedProfile_eq_stationary]

/-- A Never update produces the displayed child, rather than a response
sibling at the original source. -/
theorem subsetProfile_erase_eq_update_never (limit : PeriodOneNormalizedSourceLimit source)
    (retained : Finset ι) (index : ℕ) {who : ι} (hwho : 0 < limit.direction.val who) :
    limit.subsetProfile (retained.erase who) index =
      Function.update (limit.subsetProfile retained index) who
        (quittingPureTimeBehaviorStrategy reward who none) := by
  rw [quittingPureTimeBehaviorStrategy_none_eq_alwaysContinue,
    subsetProfile, subsetProfile, update_quittingStationaryProfile_alwaysContinue]
  congr 1
  funext player
  by_cases heq : player = who
  · subst player
    simp [subsetRoot, ne_of_gt hwho]
  · simp [subsetRoot, heq]

theorem subsetRoot_totalHazard_le (limit : PeriodOneNormalizedSourceLimit source)
    (retained : Finset ι) (index : ℕ) :
    quittingStationaryTotalHazard (limit.subsetRoot retained index) ≤
      quittingStationaryTotalHazard (source.root (limit.select index)) := by
  unfold quittingStationaryTotalHazard
  apply Finset.sum_le_sum
  intro who _
  unfold subsetRoot
  split_ifs <;> simp [ENNReal.toReal_nonneg]

theorem subsetRoot_totalHazard_tendsto_zero (limit : PeriodOneNormalizedSourceLimit source)
    (retained : Finset ι) :
    Tendsto (fun index ↦ quittingStationaryTotalHazard (limit.subsetRoot retained index))
      atTop (nhds 0) :=
  squeeze_zero (fun _ ↦ Finset.sum_nonneg fun _ _ ↦ ENNReal.toReal_nonneg)
    (limit.subsetRoot_totalHazard_le retained) limit.totalHazard_tendsto_zero

theorem subsetRoot_totalHazard_pos (limit : PeriodOneNormalizedSourceLimit source)
    (retained : Finset ι) (hmass : 0 < limit.subsetMass retained) (index : ℕ) :
    0 < quittingStationaryTotalHazard (limit.subsetRoot retained index) := by
  obtain ⟨who, hwho, _⟩ := (Finset.sum_pos_iff_of_nonneg
    (fun player (_ : player ∈ retained) ↦ limit.direction.property.1 player)).mp hmass
  have hterm : 0 < (limit.subsetRoot retained index who true).toReal := by
    simpa [subsetRoot, hwho] using source.quitProbability_pos (limit.select index) who
  unfold quittingStationaryTotalHazard
  exact hterm.trans_le (Finset.single_le_sum
    (f := fun player ↦ (limit.subsetRoot retained index player true).toReal)
    (fun _ _ ↦ ENNReal.toReal_nonneg)
    (Finset.mem_univ who))

private theorem selectedShare_tendsto (limit : PeriodOneNormalizedSourceLimit source) (who : ι) :
    Tendsto (fun index ↦ (source.root (limit.select index) who true).toReal /
      quittingStationaryTotalHazard (source.root (limit.select index))) atTop
      (nhds (limit.direction.val who)) :=
  (((continuous_apply who).comp continuous_subtype_val).tendsto limit.direction).comp
    limit.direction_tendsto

theorem subsetRoot_originalScale_tendsto (limit : PeriodOneNormalizedSourceLimit source)
    (retained : Finset ι) (who : ι) :
    Tendsto (fun index ↦ (limit.subsetRoot retained index who true).toReal /
      quittingStationaryTotalHazard (source.root (limit.select index))) atTop
      (nhds (if who ∈ retained then limit.direction.val who else 0)) := by
  by_cases hmem : who ∈ retained
  · simpa [subsetRoot, hmem] using limit.selectedShare_tendsto who
  · by_cases hzero : limit.direction.val who = 0
    · simpa [subsetRoot, hmem, hzero] using limit.selectedShare_tendsto who
    · simp [subsetRoot, hmem, hzero]

theorem subsetRoot_totalHazard_ratio_tendsto (limit : PeriodOneNormalizedSourceLimit source)
    (retained : Finset ι) :
    Tendsto (fun index ↦ quittingStationaryTotalHazard (limit.subsetRoot retained index) /
      quittingStationaryTotalHazard (source.root (limit.select index))) atTop
      (nhds (limit.subsetMass retained)) := by
  have h := tendsto_finsetSum Finset.univ fun who _ ↦
    limit.subsetRoot_originalScale_tendsto retained who
  simpa [quittingStationaryTotalHazard, Finset.sum_div, subsetMass] using h

theorem subsetRoot_direction_tendsto (limit : PeriodOneNormalizedSourceLimit source)
    (retained : Finset ι) (hmass : 0 < limit.subsetMass retained) (who : ι) :
    Tendsto (fun index ↦ (limit.subsetRoot retained index who true).toReal /
      quittingStationaryTotalHazard (limit.subsetRoot retained index)) atTop
      (nhds ((if who ∈ retained then limit.direction.val who else 0) /
        limit.subsetMass retained)) := by
  have h := (limit.subsetRoot_originalScale_tendsto retained who).div
    (limit.subsetRoot_totalHazard_ratio_tendsto retained) hmass.ne'
  apply h.congr'
  filter_upwards [] with index
  exact div_div_div_cancel_right₀ (source.totalHazard_pos (limit.select index)).ne' _ _

theorem subsetRoot_testPayoff_tendsto (limit : PeriodOneNormalizedSourceLimit source)
    (retained : Finset ι) (hmass : 0 < limit.subsetMass retained)
    (testReward : {S : Finset ι // S.Nonempty} → Payoff ι) (who : ι) :
    Tendsto (fun index ↦ quittingTerminalPayoff testReward
      (quittingStationaryProfile testReward (limit.subsetRoot retained index)) who)
      atTop (nhds ((∑ owner ∈ retained, limit.direction.val owner *
        quittingSoloReward testReward owner who) / limit.subsetMass retained)) := by
  have hbary := tendsto_finsetSum Finset.univ fun owner _ ↦
    (limit.subsetRoot_direction_tendsto retained hmass owner).mul_const
      (quittingSoloReward testReward owner who)
  have hbary' : Tendsto (fun index ↦ quittingStationarySingletonDirectionBarycenter testReward
      (limit.subsetRoot retained index) who) atTop
      (nhds ((∑ owner ∈ retained, limit.direction.val owner *
        quittingSoloReward testReward owner who) / limit.subsetMass retained)) := by
    simpa [quittingStationarySingletonDirectionBarycenter,
      div_mul_eq_mul_div, ← Finset.sum_div, ite_mul] using hbary
  have htotal := limit.subsetRoot_totalHazard_tendsto_zero retained
  have hhalf : ∀ᶠ index in atTop,
      quittingStationaryTotalHazard (limit.subsetRoot retained index) ≤ 1 / 2 :=
    (htotal.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))).mono fun _ h ↦ h.le
  have hdiff := Math.tendsto_zero_of_abs_le_of_tendsto_zero _ _
    (by simpa using htotal.const_mul (6 * quittingRewardBound testReward))
    (hhalf.mono fun index h ↦ abs_stationaryPayoff_sub_singletonDirectionBarycenter_le testReward
      (abs_reward_le_quittingRewardBound testReward) (limit.subsetRoot retained index) who
      (limit.subsetRoot_totalHazard_pos retained hmass index) h)
  simpa using hdiff.add hbary'

theorem subsetProfile_payoff_tendsto (limit : PeriodOneNormalizedSourceLimit source)
    (retained : Finset ι) (hmass : 0 < limit.subsetMass retained) (who : ι) :
    Tendsto (fun index ↦ quittingTerminalPayoff reward (limit.subsetProfile retained index) who)
      atTop (nhds (limit.subsetValue retained who)) :=
  limit.subsetRoot_testPayoff_tendsto retained hmass reward who

/-- The first absorbing coalition law converges pointwise to the retained
singleton lottery. The numerator is the exact product-root coalition mass. -/
theorem subsetRoot_absorbingCoalitionLaw_tendsto
    (limit : PeriodOneNormalizedSourceLimit source) (retained : Finset ι)
    (hmass : 0 < limit.subsetMass retained)
    (coalition : {S : Finset ι // S.Nonempty}) :
    Tendsto (fun index ↦ quittingRootCoalitionMass (limit.subsetRoot retained index) coalition.1 /
      quittingRootAbsorptionMass (limit.subsetRoot retained index)) atTop
      (nhds ((∑ owner ∈ retained, limit.direction.val owner *
        if ({owner} : Finset ι) = coalition.1 then 1 else 0) /
          limit.subsetMass retained)) := by
  let testReward : {S : Finset ι // S.Nonempty} → Payoff ι :=
    fun terminal _ ↦ if terminal = coalition then 1 else 0
  obtain ⟨who⟩ := (inferInstance : Nonempty ι)
  have h := limit.subsetRoot_testPayoff_tendsto retained hmass testReward who
  have hlimit : (∑ owner ∈ retained, limit.direction.val owner *
      quittingSoloReward testReward owner who) =
      ∑ owner ∈ retained, limit.direction.val owner *
        if ({owner} : Finset ι) = coalition.1 then 1 else 0 := by
    apply Finset.sum_congr rfl
    intro owner _
    simp [quittingSoloReward, testReward, Subtype.ext_iff]
  rw [hlimit] at h
  apply h.congr'
  filter_upwards [] with index
  rw [quittingTerminalPayoff_stationary_eq_absorbingContribution_div testReward
    (limit.subsetRoot retained index) who
    (quittingStationaryContinueMass_lt_one_of_totalHazard_pos _
      (limit.subsetRoot_totalHazard_pos retained hmass index)),
    quittingRootAbsorbingContribution_eq_sum_nonemptyCoalitionMass]
  simp [testReward, mul_ite, quittingRootCoalitionMass, quittingRootAbsorptionMass]
  rfl

/-- The probability in this statement is generated by the original reward
game and literal retained-source profile, not by an auxiliary test game. -/
theorem subsetProfile_actualTerminalLaw_tendsto
    (limit : PeriodOneNormalizedSourceLimit source) (retained : Finset ι)
    (hmass : 0 < limit.subsetMass retained)
    (coalition : {S : Finset ι // S.Nonempty}) :
    Tendsto (fun index ↦ quittingTerminalOutcomeMass reward
      (limit.subsetProfile retained index) (some coalition)) atTop
      (nhds ((∑ owner ∈ retained, limit.direction.val owner *
        if ({owner} : Finset ι) = coalition.1 then 1 else 0) /
          limit.subsetMass retained)) := by
  apply (limit.subsetRoot_absorbingCoalitionLaw_tendsto retained hmass coalition).congr'
  filter_upwards [] with index
  exact (quittingTerminalOutcomeMass_stationary_some_eq_conditionalCoalitionMass reward
    (limit.subsetRoot retained index)
    (quittingStationaryContinueMass_lt_one_of_totalHazard_pos _
      (limit.subsetRoot_totalHazard_pos retained hmass index)) coalition).symm

theorem subsetRoot_absorbingSingletonLaw_tendsto
    (limit : PeriodOneNormalizedSourceLimit source) (retained : Finset ι)
    (hmass : 0 < limit.subsetMass retained) (who : ι) :
    Tendsto (fun index ↦ quittingRootCoalitionMass (limit.subsetRoot retained index) {who} /
      quittingRootAbsorptionMass (limit.subsetRoot retained index)) atTop
      (nhds ((if who ∈ retained then limit.direction.val who else 0) /
        limit.subsetMass retained)) := by
  simpa only [Finset.singleton_inj, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq'] using
    limit.subsetRoot_absorbingCoalitionLaw_tendsto retained hmass
      ⟨{who}, Finset.singleton_nonempty who⟩

theorem subsetRoot_absorbingNonsingletonLaw_tendsto
    (limit : PeriodOneNormalizedSourceLimit source) (retained : Finset ι)
    (hmass : 0 < limit.subsetMass retained)
    (coalition : {S : Finset ι // S.Nonempty}) (hnon : coalition.1.card ≠ 1) :
    Tendsto (fun index ↦ quittingRootCoalitionMass (limit.subsetRoot retained index) coalition.1 /
      quittingRootAbsorptionMass (limit.subsetRoot retained index)) atTop (nhds 0) := by
  have hne (owner : ι) : ({owner} : Finset ι) ≠ coalition.1 := by
    intro heq
    exact hnon (by rw [← heq]; simp)
  simpa [hne] using limit.subsetRoot_absorbingCoalitionLaw_tendsto retained hmass coalition

/-- On the finite nonempty-coalition space the pointwise law convergence is
also convergence in total variation, with the conventional factor one half. -/
theorem subsetRoot_absorbingLaw_totalVariation_tendsto_zero
    (limit : PeriodOneNormalizedSourceLimit source) (retained : Finset ι)
    (hmass : 0 < limit.subsetMass retained) :
    Tendsto (fun index ↦ (1 / 2 : ℝ) * ∑ coalition : {S : Finset ι // S.Nonempty},
      |quittingRootCoalitionMass (limit.subsetRoot retained index) coalition.1 /
          quittingRootAbsorptionMass (limit.subsetRoot retained index) -
        (∑ owner ∈ retained, limit.direction.val owner *
          if ({owner} : Finset ι) = coalition.1 then 1 else 0) /
            limit.subsetMass retained|) atTop (nhds 0) := by
  have h := tendsto_finsetSum Finset.univ fun coalition _ ↦
    ((limit.subsetRoot_absorbingCoalitionLaw_tendsto retained hmass coalition).sub_const
      ((∑ owner ∈ retained, limit.direction.val owner *
        if ({owner} : Finset ι) = coalition.1 then 1 else 0) /
          limit.subsetMass retained)).abs
  simpa using h.const_mul (1 / 2 : ℝ)

/-- The Quit-now endpoint converges to the singleton reward, including
simultaneous quits in every finite source row. -/
theorem subsetProfile_quitNow_tendsto (limit : PeriodOneNormalizedSourceLimit source)
    (retained : Finset ι) (who : ι) :
    Tendsto (fun index ↦ quittingTerminalPayoff reward
      (Function.update (limit.subsetProfile retained index) who
        (quittingPureTimeBehaviorStrategy reward who (some 0))) who)
      atTop (nhds (quittingSoloReward reward who who)) := by
  have hbound : ∀ index,
      |quittingTerminalPayoff reward
        (Function.update (limit.subsetProfile retained index) who
          (quittingPureTimeBehaviorStrategy reward who (some 0))) who -
        quittingSoloReward reward who who| ≤ 2 * quittingRewardBound reward *
          quittingStationaryTotalHazard (limit.subsetRoot retained index) := by
    intro index
    rw [quittingTerminalPayoff_update_quitNow_eq_fixedOpponentsQuitValue]
    simp only [subsetProfile, quittingProfileLiveRoot_stationary]
    exact (abs_quittingStationaryFixedOpponentsQuitValue_sub_singleton_le
      (reward := reward) (limit.subsetRoot retained index) who
      (abs_reward_le_quittingRewardBound reward)).trans
      (mul_le_mul_of_nonneg_left
        (quittingRootOpponentAbsorptionMass_le_stationaryTotalHazard
          (limit.subsetRoot retained index) who)
        (mul_nonneg (by norm_num) (quittingRewardBound_nonneg reward)))
  have hdiff := Math.tendsto_zero_of_abs_le_of_tendsto_zero _ _
    (by
      simpa using (limit.subsetRoot_totalHazard_tendsto_zero retained).const_mul
        (2 * quittingRewardBound reward))
    (Eventually.of_forall hbound)
  simpa using hdiff.add_const (quittingSoloReward reward who who)

/-- The Never endpoint is the payoff of the actual further-deleted child. -/
theorem subsetProfile_never_tendsto (limit : PeriodOneNormalizedSourceLimit source)
    (retained : Finset ι) {who : ι} (hwho : 0 < limit.direction.val who)
    (hmass : 0 < limit.subsetMass (retained.erase who)) :
    Tendsto (fun index ↦ quittingTerminalPayoff reward
      (Function.update (limit.subsetProfile retained index) who
        (quittingPureTimeBehaviorStrategy reward who none)) who)
      atTop (nhds (limit.subsetValue (retained.erase who) who)) := by
  simpa only [← limit.subsetProfile_erase_eq_update_never retained _ hwho] using
    limit.subsetProfile_payoff_tendsto (retained.erase who) hmass who

theorem subsetMass_erase (limit : PeriodOneNormalizedSourceLimit source)
    (retained : Finset ι) {who : ι} (hwho : who ∈ retained) :
    limit.subsetMass (retained.erase who) =
      limit.subsetMass retained - limit.direction.val who := by
  unfold subsetMass
  rw [← Finset.sum_erase_add _ _ hwho]
  ring

/-- Exact barycentric Never-gain identity on the retained leading owners. -/
theorem subsetValue_neverGain_eq (limit : PeriodOneNormalizedSourceLimit source)
    (retained : Finset ι) {who : ι} (hwho : who ∈ retained)
    (hmass : 0 < limit.subsetMass retained)
    (hrest : 0 < limit.subsetMass (retained.erase who)) :
    limit.subsetValue (retained.erase who) who - limit.subsetValue retained who =
      limit.direction.val who * (∑ owner ∈ retained.erase who, limit.direction.val owner *
        (quittingSoloReward reward owner who - quittingSoloReward reward who who)) /
        (limit.subsetMass retained * limit.subsetMass (retained.erase who)) := by
  have hmassSplit := limit.subsetMass_erase retained hwho
  unfold subsetValue
  rw [← Finset.sum_erase_add _ _ hwho]
  simp_rw [mul_sub]
  rw [Finset.sum_sub_distrib, ← Finset.sum_mul]
  change _ = limit.direction.val who * (_ - limit.subsetMass (retained.erase who) * _) / _
  field_simp [hmass.ne', hrest.ne']
  rw [show limit.subsetMass retained = limit.subsetMass (retained.erase who) +
    limit.direction.val who by linarith]
  ring

theorem subsetProfile_neverGain_tendsto (limit : PeriodOneNormalizedSourceLimit source)
    (retained : Finset ι) {who : ι} (hwho : who ∈ retained)
    (hpositive : 0 < limit.direction.val who)
    (hmass : 0 < limit.subsetMass retained)
    (hrest : 0 < limit.subsetMass (retained.erase who)) :
    Tendsto (fun index ↦ quittingTerminalPayoff reward
      (Function.update (limit.subsetProfile retained index) who
        (quittingPureTimeBehaviorStrategy reward who none)) who -
      quittingTerminalPayoff reward (limit.subsetProfile retained index) who) atTop
      (nhds (limit.direction.val who *
        (∑ owner ∈ retained.erase who, limit.direction.val owner *
          (quittingSoloReward reward owner who - quittingSoloReward reward who who)) /
        (limit.subsetMass retained * limit.subsetMass (retained.erase who)))) := by
  rw [← limit.subsetValue_neverGain_eq retained hwho hmass hrest]
  exact (limit.subsetProfile_never_tendsto retained hpositive hrest).sub
    (limit.subsetProfile_payoff_tendsto retained hmass who)

def subsetNeverGain (limit : PeriodOneNormalizedSourceLimit source)
    (retained : Finset ι) (who : ι) : ℝ :=
  limit.direction.val who *
    (∑ owner ∈ retained.erase who, limit.direction.val owner *
      (quittingSoloReward reward owner who - quittingSoloReward reward who who)) /
    (limit.subsetMass retained * limit.subsetMass (retained.erase who))

theorem subsetValue_sub_solo (limit : PeriodOneNormalizedSourceLimit source)
    (retained : Finset ι) (hmass : 0 < limit.subsetMass retained) (who : ι) :
    limit.subsetValue retained who - quittingSoloReward reward who who =
      (∑ owner ∈ retained, limit.direction.val owner *
        (quittingSoloReward reward owner who - quittingSoloReward reward who who)) /
        limit.subsetMass retained := by
  unfold subsetValue
  simp_rw [mul_sub]
  rw [Finset.sum_sub_distrib, ← Finset.sum_mul]
  change _ = (_ - limit.subsetMass retained * _) / limit.subsetMass retained
  field_simp [hmass.ne']

/-- Strict residual selects a finite-rank exact complete Never cap at the
actual retained source, with a fixed positive half-limit gain. -/
theorem eventually_subsetNever_exactCap_and_gain
    (limit : PeriodOneNormalizedSourceLimit source) (retained : Finset ι) {who : ι}
    (hwho : who ∈ retained) (hpositive : 0 < limit.direction.val who)
    (hrest : 0 < limit.subsetMass (retained.erase who))
    (hmargin : 0 < ∑ owner ∈ retained.erase who, limit.direction.val owner *
      (quittingSoloReward reward owner who - quittingSoloReward reward who who)) :
    0 < limit.subsetNeverGain retained who ∧ ∀ᶠ index in atTop,
      quittingTerminalPayoff reward
        (Function.update (limit.subsetProfile retained index) who
          (quittingPureTimeBehaviorStrategy reward who none)) who =
        quittingContinuationBestResponseValue reward (limit.subsetProfile retained index) who ∧
      limit.subsetNeverGain retained who / 2 ≤
        quittingTerminalPayoff reward (limit.subsetProfile (retained.erase who) index) who -
          quittingTerminalPayoff reward (limit.subsetProfile retained index) who := by
  have hmass : 0 < limit.subsetMass retained := by
    have hsplit := limit.subsetMass_erase retained hwho
    linarith
  have hgainPos : 0 < limit.subsetNeverGain retained who :=
    div_pos (mul_pos hpositive hmargin) (mul_pos hmass hrest)
  have hsep : 0 < limit.subsetValue (retained.erase who) who -
      quittingSoloReward reward who who := by
    rw [limit.subsetValue_sub_solo (retained.erase who) hrest who]
    exact div_pos hmargin hrest
  have hnever := limit.subsetProfile_never_tendsto retained hpositive hrest
  have hquit := limit.subsetProfile_quitNow_tendsto retained who
  have heventSep := ((hnever.sub hquit).eventually (lt_mem_nhds hsep))
  have heventGain := (limit.subsetProfile_neverGain_tendsto retained hwho hpositive hmass hrest)
    |>.eventually (lt_mem_nhds (show limit.subsetNeverGain retained who / 2 <
      limit.subsetNeverGain retained who by linarith))
  refine ⟨hgainPos, ?_⟩
  filter_upwards [heventSep, heventGain] with index hsepIndex hgainIndex
  refine ⟨?_, ?_⟩
  · obtain ⟨choice, hkind, hcap⟩ := exists_stationary_quitNow_or_never_completeCap
      reward (limit.subsetRoot retained index) who
    rcases hkind with rfl | rfl
    · exact hcap
    · have hneverLe := quittingTerminalPayoff_update_le_continuationBestResponseValue
        reward (limit.subsetProfile retained index) who
        (quittingPureTimeBehaviorStrategy reward who none)
      change quittingTerminalPayoff reward
        (Function.update (limit.subsetProfile retained index) who
          (quittingPureTimeBehaviorStrategy reward who (some 0))) who =
        quittingContinuationBestResponseValue reward
          (limit.subsetProfile retained index) who at hcap
      rw [← hcap] at hneverLe
      linarith
  · rw [← limit.subsetProfile_erase_eq_update_never retained index hpositive] at hgainIndex
    exact hgainIndex.le

theorem subsetMass_positiveSupport (limit : PeriodOneNormalizedSourceLimit source) :
    limit.subsetMass limit.positiveSupport = 1 := by
  unfold subsetMass
  calc
    ∑ who ∈ limit.positiveSupport, limit.direction.val who = ∑ who, limit.direction.val who := by
      apply Finset.sum_subset (Finset.subset_univ _)
      intro who _ hnot
      exact le_antisymm (not_lt.mp (by simpa [positiveSupport] using hnot))
        (limit.direction.property.1 who)
    _ = 1 := limit.direction.property.2

theorem subsetMass_pos_of_nonempty_subset_support (limit : PeriodOneNormalizedSourceLimit source)
    {retained : Finset ι} (hsubset : retained ⊆ limit.positiveSupport)
    (hnonempty : retained.Nonempty) : 0 < limit.subsetMass retained := by
  exact Finset.sum_pos (fun who hwho ↦ by simpa [positiveSupport] using hsubset hwho) hnonempty

theorem subsetValue_positiveSupport (limit : PeriodOneNormalizedSourceLimit source) (who : ι) :
    limit.subsetValue limit.positiveSupport who = limit.limitValue who := by
  rw [subsetValue, subsetMass_positiveSupport, div_one,
    limit.limitValue_eq_singletonDirectionPayoff]
  unfold quittingSingletonDirectionPayoff
  apply Finset.sum_subset (Finset.subset_univ _)
  intro owner _ hnot
  have hzero : limit.direction.val owner = 0 :=
    le_antisymm (not_lt.mp (by simpa [positiveSupport] using hnot))
      (limit.direction.property.1 owner)
  simp [hzero]

theorem support_erased_singletonMargin (limit : PeriodOneNormalizedSourceLimit source)
    {who : ι} (hwho : who ∈ limit.positiveSupport) :
    (∑ owner ∈ limit.positiveSupport.erase who, limit.direction.val owner *
      (quittingSoloReward reward owner who - quittingSoloReward reward who who)) =
      limit.limitingSingletonMargin who := by
  have h := limit.subsetValue_sub_solo limit.positiveSupport
    (by rw [limit.subsetMass_positiveSupport]; norm_num) who
  rw [subsetMass_positiveSupport, div_one, subsetValue_positiveSupport,
    ← limit.limitingSingletonMargin_eq_limitValue_sub_solo] at h
  rw [← Finset.sum_erase_add _ _ hwho] at h
  simpa using h.symm

theorem subsetNeverGain_positiveSupport (limit : PeriodOneNormalizedSourceLimit source)
    {who : ι} (hwho : who ∈ limit.positiveSupport) {minimum : ℝ}
    (hcommon : limit.limitingSingletonMargin who = minimum) :
    limit.subsetNeverGain limit.positiveSupport who =
      limit.direction.val who * minimum / (1 - limit.direction.val who) := by
  unfold subsetNeverGain
  rw [limit.support_erased_singletonMargin hwho, hcommon,
    limit.subsetMass_erase limit.positiveSupport hwho, limit.subsetMass_positiveSupport, one_mul]

/-- The second move uses the residual at the actual first child: the first
owner's column contribution has been subtracted from the common margin. -/
theorem subsetNeverGain_after_first (limit : PeriodOneNormalizedSourceLimit source)
    {first second : ι} (hfirst : first ∈ limit.positiveSupport)
    (hsecond : second ∈ limit.positiveSupport.erase first) {minimum : ℝ}
    (hcommon : limit.limitingSingletonMargin second = minimum) :
    limit.subsetNeverGain (limit.positiveSupport.erase first) second =
      limit.direction.val second * (minimum - limit.direction.val first *
        (quittingSoloReward reward first second - quittingSoloReward reward second second)) /
        ((1 - limit.direction.val first) *
          (1 - limit.direction.val first - limit.direction.val second)) := by
  have hsecondSupport := (Finset.mem_erase.mp hsecond).2
  have hfirstOther : first ∈ limit.positiveSupport.erase second :=
    Finset.mem_erase.mpr ⟨(Finset.mem_erase.mp hsecond).1.symm, hfirst⟩
  have hmargin := limit.support_erased_singletonMargin hsecondSupport
  rw [hcommon, ← Finset.sum_erase_add _ _ hfirstOther] at hmargin
  have hsum : (∑ owner ∈ (limit.positiveSupport.erase first).erase second,
      limit.direction.val owner *
        (quittingSoloReward reward owner second - quittingSoloReward reward second second)) =
      minimum - limit.direction.val first *
        (quittingSoloReward reward first second - quittingSoloReward reward second second) := by
    rw [Finset.erase_right_comm]
    linarith
  unfold subsetNeverGain
  rw [hsum, limit.subsetMass_erase (limit.positiveSupport.erase first) hsecond,
    limit.subsetMass_erase limit.positiveSupport hfirst, limit.subsetMass_positiveSupport]

/-- The ordered second mover's residual remains strictly positive after
deleting a suitably selected first mover. -/
theorem exists_ordered_pair_positive_childMargin
    (limit : PeriodOneNormalizedSourceLimit source) {minimum : ℝ} (hminimum : 0 < minimum)
    (hcommon : ∀ who ∈ limit.positiveSupport, limit.limitingSingletonMargin who = minimum)
    (hcard : 3 ≤ limit.positiveSupport.card) :
    ∃ first ∈ limit.positiveSupport, ∃ second ∈ limit.positiveSupport.erase first,
      0 < ∑ owner ∈ (limit.positiveSupport.erase first).erase second,
        limit.direction.val owner *
          (quittingSoloReward reward owner second - quittingSoloReward reward second second) := by
  obtain ⟨second, hsecond⟩ := Finset.card_pos.mp (by omega : 0 < limit.positiveSupport.card)
  let rest := limit.positiveSupport.erase second
  let term := fun owner ↦ limit.direction.val owner *
    (quittingSoloReward reward owner second - quittingSoloReward reward second second)
  have hsum : ∑ owner ∈ rest, term owner = minimum := by
    exact (limit.support_erased_singletonMargin hsecond).trans (hcommon second hsecond)
  have hrestCard : 2 ≤ rest.card := by
    dsimp [rest]
    rw [Finset.card_erase_of_mem hsecond]
    omega
  have hexists : ∃ first ∈ rest, term first < minimum := by
    by_contra hnot
    push Not at hnot
    have hsumge := Finset.sum_le_sum (fun owner (howner : owner ∈ rest) ↦ hnot owner howner)
    rw [hsum] at hsumge
    simp only [Finset.sum_const, nsmul_eq_mul] at hsumge
    have hcardReal : (2 : ℝ) ≤ rest.card := by exact_mod_cast hrestCard
    nlinarith
  obtain ⟨first, hfirst, hterm⟩ := hexists
  have hfirstSupport := (Finset.mem_erase.mp hfirst).2
  have hne := (Finset.mem_erase.mp hfirst).1
  refine ⟨first, hfirstSupport, second, Finset.mem_erase.mpr ⟨hne.symm, hsecond⟩, ?_⟩
  change 0 < ∑ owner ∈ (limit.positiveSupport.erase first).erase second, term owner
  rw [Finset.erase_right_comm]
  change 0 < ∑ owner ∈ rest.erase first, term owner
  rw [← Finset.sum_erase_add _ _ hfirst] at hsum
  linarith

/-- A literal Never child attains the full cap of its own predecessor. -/
def IsExactNeverCapEdge
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (before after : (quittingGame reward).BehaviorProfile) (who : ι) (gain : ℝ) : Prop :=
  after = Function.update before who (quittingPureTimeBehaviorStrategy reward who none) ∧
  quittingTerminalPayoff reward after who =
    quittingContinuationBestResponseValue reward before who ∧
  gain ≤ quittingTerminalPayoff reward after who - quittingTerminalPayoff reward before who

theorem eventually_subsetNever_edge
    (limit : PeriodOneNormalizedSourceLimit source) (retained : Finset ι) {who : ι}
    (hwho : who ∈ retained) (hpositive : 0 < limit.direction.val who)
    (hrest : 0 < limit.subsetMass (retained.erase who))
    (hmargin : 0 < ∑ owner ∈ retained.erase who, limit.direction.val owner *
      (quittingSoloReward reward owner who - quittingSoloReward reward who who)) :
    ∃ gain : ℝ, 0 < gain ∧ ∀ᶠ index in atTop,
      IsExactNeverCapEdge reward (limit.subsetProfile retained index)
        (limit.subsetProfile (retained.erase who) index) who gain := by
  obtain ⟨hpos, hevent⟩ :=
    limit.eventually_subsetNever_exactCap_and_gain retained hwho hpositive hrest hmargin
  refine ⟨limit.subsetNeverGain retained who / 2, half_pos hpos, ?_⟩
  filter_upwards [hevent] with index hindex
  refine ⟨limit.subsetProfile_erase_eq_update_never retained index hpositive, ?_, hindex.2⟩
  rw [limit.subsetProfile_erase_eq_update_never retained index hpositive]
  exact hindex.1

/-- Two Never moves are installed successively on the same actual source
chronology; the second cap is recomputed at the first child. -/
theorem exists_chronological_twoNever_supportDescent
    (limit : PeriodOneNormalizedSourceLimit source) {minimum : ℝ} (hminimum : 0 < minimum)
    (hcommon : ∀ who ∈ limit.positiveSupport, limit.limitingSingletonMargin who = minimum)
    (hcard : 3 ≤ limit.positiveSupport.card) :
    ∃ first ∈ limit.positiveSupport, ∃ second ∈ limit.positiveSupport.erase first,
      ∃ firstGain secondGain : ℝ, 0 < firstGain ∧ 0 < secondGain ∧
        (limit.positiveSupport.erase first |>.erase second).card =
          limit.positiveSupport.card - 2 ∧
        ∀ᶠ index in atTop,
          IsExactNeverCapEdge reward (source.profile (limit.select index))
            (limit.subsetProfile (limit.positiveSupport.erase first) index) first firstGain ∧
          IsExactNeverCapEdge reward
            (limit.subsetProfile (limit.positiveSupport.erase first) index)
            (limit.subsetProfile ((limit.positiveSupport.erase first).erase second) index)
            second secondGain := by
  obtain ⟨first, hfirst, second, hsecond, hmarginSecond⟩ :=
    limit.exists_ordered_pair_positive_childMargin hminimum hcommon hcard
  have hfirstPositive : 0 < limit.direction.val first := by
    simpa [positiveSupport] using hfirst
  have hsecondPositive : 0 < limit.direction.val second := by
    simpa [positiveSupport] using (Finset.mem_erase.mp hsecond).2
  have hchildCard : (limit.positiveSupport.erase first).card =
      limit.positiveSupport.card - 1 := Finset.card_erase_of_mem hfirst
  have hlastCard : ((limit.positiveSupport.erase first).erase second).card =
      limit.positiveSupport.card - 2 := by
    rw [Finset.card_erase_of_mem hsecond, hchildCard]
    omega
  have hchildMass := limit.subsetMass_pos_of_nonempty_subset_support
    (Finset.erase_subset first limit.positiveSupport)
    (Finset.card_pos.mp (by omega : 0 < (limit.positiveSupport.erase first).card))
  have hlastMass := limit.subsetMass_pos_of_nonempty_subset_support
    ((Finset.erase_subset second (limit.positiveSupport.erase first)).trans
      (Finset.erase_subset first limit.positiveSupport))
    (Finset.card_pos.mp (by omega : 0 < ((limit.positiveSupport.erase first).erase second).card))
  have hmarginFirst : 0 < ∑ owner ∈ limit.positiveSupport.erase first,
      limit.direction.val owner *
        (quittingSoloReward reward owner first - quittingSoloReward reward first first) := by
    rw [limit.support_erased_singletonMargin hfirst, hcommon first hfirst]
    exact hminimum
  obtain ⟨firstGain, hfirstGain, hfirstEdge⟩ := limit.eventually_subsetNever_edge
    limit.positiveSupport hfirst hfirstPositive hchildMass hmarginFirst
  obtain ⟨secondGain, hsecondGain, hsecondEdge⟩ := limit.eventually_subsetNever_edge
    (limit.positiveSupport.erase first) hsecond hsecondPositive hlastMass hmarginSecond
  refine ⟨first, hfirst, second, hsecond, firstGain, secondGain, hfirstGain, hsecondGain,
    hlastCard, ?_⟩
  filter_upwards [hfirstEdge, hsecondEdge] with index hfirstIndex hsecondIndex
  exact ⟨by simpa only [subsetProfile_positiveSupport] using hfirstIndex, hsecondIndex⟩

/-- A zero-share player's literal Never deviation removes its finite hazard,
but leaves the limiting singleton lottery unchanged. -/
theorem subsetProfile_zeroShare_never_tendsto
    (limit : PeriodOneNormalizedSourceLimit source) (retained : Finset ι)
    (hmass : 0 < limit.subsetMass retained) {who : ι}
    (hzero : limit.direction.val who = 0) :
    Tendsto (fun index ↦ quittingTerminalPayoff reward
      (Function.update (limit.subsetProfile retained index) who
        (quittingPureTimeBehaviorStrategy reward who none)) who)
      atTop (nhds (limit.subsetValue retained who)) := by
  let root := fun index ↦ Function.update (limit.subsetRoot retained index) who (PMF.pure false)
  have hscale (owner : ι) : Tendsto (fun index ↦ (root index owner true).toReal /
      quittingStationaryTotalHazard (source.root (limit.select index))) atTop
      (nhds (if owner ∈ retained then limit.direction.val owner else 0)) := by
    by_cases heq : owner = who
    · subst owner
      simp [root, hzero]
    · simpa [root, Function.update_of_ne heq] using
        limit.subsetRoot_originalScale_tendsto retained owner
  have htotalScale : Tendsto (fun index ↦ quittingStationaryTotalHazard (root index) /
      quittingStationaryTotalHazard (source.root (limit.select index))) atTop
      (nhds (limit.subsetMass retained)) := by
    simpa [quittingStationaryTotalHazard, Finset.sum_div, subsetMass] using
      tendsto_finsetSum Finset.univ (fun owner _ ↦ hscale owner)
  have hpositive : ∀ᶠ index in atTop, 0 < quittingStationaryTotalHazard (root index) := by
    filter_upwards [htotalScale.eventually_const_lt hmass] with index hindex
    exact (div_pos_iff.mp hindex).resolve_right
      (fun h ↦ (not_lt_of_ge (le_of_lt (source.totalHazard_pos (limit.select index)))) h.2) |>.1
  have htotalLe (index : ℕ) : quittingStationaryTotalHazard (root index) ≤
      quittingStationaryTotalHazard (limit.subsetRoot retained index) := by
    apply Finset.sum_le_sum
    intro owner _
    by_cases heq : owner = who
    · subst owner
      simp [root, ENNReal.toReal_nonneg]
    · simp [root, Function.update_of_ne heq]
  have htotal := squeeze_zero (fun index ↦ Finset.sum_nonneg
    (fun owner _ ↦ ENNReal.toReal_nonneg)) htotalLe
    (limit.subsetRoot_totalHazard_tendsto_zero retained)
  have hdirection (owner : ι) : Tendsto (fun index ↦ (root index owner true).toReal /
      quittingStationaryTotalHazard (root index)) atTop
      (nhds ((if owner ∈ retained then limit.direction.val owner else 0) /
        limit.subsetMass retained)) := by
    apply ((hscale owner).div htotalScale hmass.ne').congr'
    filter_upwards [] with index
    exact div_div_div_cancel_right₀ (source.totalHazard_pos (limit.select index)).ne' _ _
  have hbary : Tendsto (fun index ↦ quittingStationarySingletonDirectionBarycenter reward
      (root index) who) atTop (nhds (limit.subsetValue retained who)) := by
    simpa [quittingStationarySingletonDirectionBarycenter, subsetValue,
      div_mul_eq_mul_div, ← Finset.sum_div, ite_mul] using
      tendsto_finsetSum Finset.univ (fun owner _ ↦
        (hdirection owner).mul_const (quittingSoloReward reward owner who))
  have hhalf : ∀ᶠ index in atTop, quittingStationaryTotalHazard (root index) ≤ 1 / 2 :=
    (htotal.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))).mono fun _ h ↦ h.le
  have hdiff := Math.tendsto_zero_of_abs_le_of_tendsto_zero _ _
    (by simpa using htotal.const_mul (6 * quittingRewardBound reward))
    (show ∀ᶠ index in atTop, _ from by
      filter_upwards [hpositive, hhalf] with index hpos hle
      exact abs_stationaryPayoff_sub_singletonDirectionBarycenter_le reward
        (abs_reward_le_quittingRewardBound reward) (root index) who hpos hle)
  have hpayoff := hdiff.add hbary
  simp only [zero_add] at hpayoff
  apply hpayoff.congr'
  filter_upwards [] with index
  simp [subsetProfile, root, quittingPureTimeBehaviorStrategy_none_eq_alwaysContinue,
    update_quittingStationaryProfile_alwaysContinue]

/-- Erasing a zero-share label does not change the limiting lottery. -/
theorem subsetValue_erase_zeroShare
    (limit : PeriodOneNormalizedSourceLimit source) (retained : Finset ι) {who : ι}
    (hzero : limit.direction.val who = 0) (receiver : ι) :
    limit.subsetValue (retained.erase who) receiver = limit.subsetValue retained receiver := by
  unfold subsetValue subsetMass
  congr 1
  · apply Finset.sum_subset (Finset.erase_subset who retained)
    intro owner hmem hnot
    have : owner = who := by simpa [Finset.mem_erase, hmem] using hnot
    simp [this, hzero]
  · apply Finset.sum_subset (Finset.erase_subset who retained)
    intro owner hmem hnot
    have : owner = who := by simpa [Finset.mem_erase, hmem] using hnot
    simpa [this] using hzero

/-- The Never endpoint formula holds for every player, including the original
zero-share outsiders whose finite hazards are still present. -/
theorem subsetProfile_anyNever_tendsto
    (limit : PeriodOneNormalizedSourceLimit source) (retained : Finset ι) (who : ι)
    (hmass : 0 < limit.subsetMass (retained.erase who)) :
    Tendsto (fun index ↦ quittingTerminalPayoff reward
      (Function.update (limit.subsetProfile retained index) who
        (quittingPureTimeBehaviorStrategy reward who none)) who)
      atTop (nhds (limit.subsetValue (retained.erase who) who)) := by
  by_cases hzero : limit.direction.val who = 0
  · have hmassEq : limit.subsetMass (retained.erase who) = limit.subsetMass retained := by
      apply Finset.sum_subset (Finset.erase_subset who retained)
      intro owner hmem hnot
      have : owner = who := by simpa [Finset.mem_erase, hmem] using hnot
      simpa [this] using hzero
    rw [limit.subsetValue_erase_zeroShare retained hzero]
    exact limit.subsetProfile_zeroShare_never_tendsto retained (by rwa [hmassEq] at hmass) hzero
  · exact limit.subsetProfile_never_tendsto retained
      (lt_of_le_of_ne (limit.direction.property.1 who) (Ne.symm hzero)) hmass

/-- Every retained subset row becomes jointly live; hence so do each player's
own and opponent Continue probabilities, with a common eventual half floor. -/
theorem subsetRoot_continueLimits (limit : PeriodOneNormalizedSourceLimit source)
    (retained : Finset ι) (who : ι) :
    Tendsto (fun index ↦ quittingStationaryContinueMass (limit.subsetRoot retained index))
      atTop (nhds 1) ∧
    Tendsto (fun index ↦ (limit.subsetRoot retained index who false).toReal)
      atTop (nhds 1) ∧
    Tendsto (fun index ↦ quittingRootOpponentContinueMass (limit.subsetRoot retained index) who)
      atTop (nhds 1) ∧
    ∀ᶠ index in atTop,
      1 / 2 ≤ quittingStationaryContinueMass (limit.subsetRoot retained index) ∧
      1 / 2 ≤ (limit.subsetRoot retained index who false).toReal ∧
      1 / 2 ≤ quittingRootOpponentContinueMass (limit.subsetRoot retained index) who := by
  have habs := squeeze_zero
    (fun index ↦ quittingRootAbsorptionMass_nonneg (limit.subsetRoot retained index))
    (fun index ↦ quittingRootAbsorptionMass_le_stationaryTotalHazard
      (limit.subsetRoot retained index))
    (limit.subsetRoot_totalHazard_tendsto_zero retained)
  have hjoint : Tendsto
      (fun index ↦ quittingStationaryContinueMass (limit.subsetRoot retained index))
      atTop (nhds 1) := by
    have h := habs.const_sub 1
    simpa [quittingRootAbsorptionMass] using h
  have hown : Tendsto (fun index ↦ (limit.subsetRoot retained index who false).toReal)
      atTop (nhds 1) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le hjoint tendsto_const_nhds
    · exact fun index ↦ quittingStationaryContinueMass_le_ownContinueProbability
        (limit.subsetRoot retained index) who
    · intro index
      simpa using ENNReal.toReal_mono ENNReal.one_ne_top
        ((limit.subsetRoot retained index who).coe_le_one false)
  have hopp : Tendsto
      (fun index ↦ quittingRootOpponentContinueMass (limit.subsetRoot retained index) who)
      atTop (nhds 1) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le hjoint tendsto_const_nhds
    · exact fun index ↦ quittingStationaryContinueMass_le_update_pure_false
        (limit.subsetRoot retained index) who
    · exact fun index ↦ quittingRootOpponentContinueMass_le_one
        (limit.subsetRoot retained index) who
  refine ⟨hjoint, hown, hopp, ?_⟩
  filter_upwards [hjoint.eventually_const_lt (by norm_num : (1 / 2 : ℝ) < 1),
    hown.eventually_const_lt (by norm_num : (1 / 2 : ℝ) < 1),
    hopp.eventually_const_lt (by norm_num : (1 / 2 : ℝ) < 1)] with index hj ho hp
  exact ⟨hj.le, ho.le, hp.le⟩

theorem subsetValue_singleton (limit : PeriodOneNormalizedSourceLimit source)
    {owner : ι} (hpositive : 0 < limit.direction.val owner) (who : ι) :
    limit.subsetValue {owner} who = quittingSoloReward reward owner who := by
  simp [subsetValue, subsetMass, hpositive.ne']

/-- The singleton descendant's prescribed and Never endpoints coincide in the
limit for every other player, even an original zero-share outsider. -/
theorem singletonSubset_endpointLimits (limit : PeriodOneNormalizedSourceLimit source)
    {owner who : ι} (hpositive : 0 < limit.direction.val owner) (hne : who ≠ owner) :
    Tendsto (fun index ↦ quittingTerminalPayoff reward
      (limit.subsetProfile {owner} index) who) atTop
      (nhds (quittingSoloReward reward owner who)) ∧
    Tendsto (fun index ↦ quittingTerminalPayoff reward
      (Function.update (limit.subsetProfile {owner} index) who
        (quittingPureTimeBehaviorStrategy reward who none)) who) atTop
      (nhds (quittingSoloReward reward owner who)) ∧
    Tendsto (fun index ↦ quittingTerminalPayoff reward
      (Function.update (limit.subsetProfile {owner} index) who
        (quittingPureTimeBehaviorStrategy reward who (some 0))) who) atTop
      (nhds (quittingSoloReward reward who who)) := by
  have hmass : 0 < limit.subsetMass {owner} := by simpa [subsetMass] using hpositive
  have herase : ({owner} : Finset ι).erase who = {owner} := by simp [hne]
  refine ⟨?_, ?_, limit.subsetProfile_quitNow_tendsto {owner} who⟩
  · simpa only [limit.subsetValue_singleton hpositive] using
      limit.subsetProfile_payoff_tendsto {owner} hmass who
  · have h := limit.subsetProfile_anyNever_tendsto {owner} who (by rwa [herase])
    simpa only [herase, limit.subsetValue_singleton hpositive] using h

/-- With two positive-share owners, the first exact Never move leaves a literal
one-leading-owner descendant, retaining all zero-share outsider hazards. -/
theorem exists_chronological_Never_singletonDescent
    (limit : PeriodOneNormalizedSourceLimit source) {minimum : ℝ} (hminimum : 0 < minimum)
    (hcommon : ∀ who ∈ limit.positiveSupport, limit.limitingSingletonMargin who = minimum)
    (hcard : limit.positiveSupport.card = 2) :
    ∃ first ∈ limit.positiveSupport, ∃ last : ι, ∃ gain : ℝ,
      0 < gain ∧ limit.positiveSupport.erase first = {last} ∧
      ∀ᶠ index in atTop,
        IsExactNeverCapEdge reward (source.profile (limit.select index))
          (limit.subsetProfile {last} index) first gain := by
  obtain ⟨first, hfirst⟩ := Finset.card_pos.mp (by omega : 0 < limit.positiveSupport.card)
  have hchildCard : (limit.positiveSupport.erase first).card = 1 := by
    rw [Finset.card_erase_of_mem hfirst, hcard]
  obtain ⟨last, hlast⟩ := Finset.card_eq_one.mp hchildCard
  have hmass := limit.subsetMass_pos_of_nonempty_subset_support
    (Finset.erase_subset first limit.positiveSupport)
    (Finset.card_pos.mp (by omega : 0 < (limit.positiveSupport.erase first).card))
  have hpositive : 0 < limit.direction.val first := (Finset.mem_filter.mp hfirst).2
  have hmargin : 0 < ∑ owner ∈ limit.positiveSupport.erase first,
      limit.direction.val owner *
        (quittingSoloReward reward owner first - quittingSoloReward reward first first) := by
    rw [limit.support_erased_singletonMargin hfirst, hcommon first hfirst]
    exact hminimum
  obtain ⟨gain, hgain, hedge⟩ := limit.eventually_subsetNever_edge
    limit.positiveSupport hfirst hpositive hmass hmargin
  refine ⟨first, hfirst, last, gain, hgain, hlast, ?_⟩
  simpa only [subsetProfile_positiveSupport, hlast] using hedge

end GameTheory.PeriodOneNormalizedSourceLimit
