/-
Copyright (c) 2026 UniformEquilibrium contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: UniformEquilibrium contributors
-/

import UniformEquilibrium.Quitting.Cycles.PeriodOneVanishingHazardTerminalCap
import UniformEquilibrium.Quitting.Paths.SureExitSet

/-! # Endpoint limits on actual one-period vanishing-hazard sources

The literal Never update deletes only its owner's marginal. Its limiting
singleton lottery is the normalized restriction of the original direction.
All endpoint and cap limits refer to the same selected actual profiles.
-/

noncomputable section

namespace GameTheory

open Filter Math.Probability
open scoped Topology

variable {ι : Type} [Fintype ι] [DecidableEq ι] [Nontrivial ι]
  {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
  {error : ℕ → ℝ} {source : PeriodOneVanishingHazardSource reward error}

namespace PeriodOneNormalizedSourceLimit

/-- The limiting payoff after one owner uses literal Never. -/
def neverLimit (limit : PeriodOneNormalizedSourceLimit source) (who : ι) : ℝ :=
  (limit.limitValue who - limit.direction.val who * quittingSoloReward reward who who) /
    (1 - limit.direction.val who)

/-- The Never limit is exactly the singleton lottery on all other players. -/
theorem neverLimit_eq_opponentSingletonLottery
    (limit : PeriodOneNormalizedSourceLimit source) (who : ι) :
    limit.neverLimit who =
      (∑ other ∈ Finset.univ.erase who,
        limit.direction.val other * quittingSoloReward reward other who) /
          (1 - limit.direction.val who) := by
  rw [neverLimit, limit.limitValue_eq_singletonDirectionPayoff]
  unfold quittingSingletonDirectionPayoff
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ who)]
  simp

private def deletedRoot (limit : PeriodOneNormalizedSourceLimit source)
    (index : ℕ) (who : ι) : ι → PMF Bool :=
  Function.update (source.root (limit.select index)) who (PMF.pure false)

private theorem deleted_totalHazard (limit : PeriodOneNormalizedSourceLimit source)
    (index : ℕ) (who : ι) :
    quittingStationaryTotalHazard (limit.deletedRoot index who) =
      quittingStationaryTotalHazard (source.root (limit.select index)) -
        (source.root (limit.select index) who true).toReal := by
  unfold quittingStationaryTotalHazard deletedRoot
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ who),
    ← Finset.sum_erase_add _ _ (Finset.mem_univ who)]
  simp only [Function.update_self, PMF.pure_apply, Bool.true_eq_false,
    ↓reduceIte, ENNReal.toReal_zero, add_zero, add_sub_cancel_right]
  apply Finset.sum_congr rfl
  intro other hother
  rw [Function.update_of_ne (Finset.ne_of_mem_erase hother)]

private theorem deleted_totalHazard_pos (limit : PeriodOneNormalizedSourceLimit source)
    (index : ℕ) (who : ι) :
    0 < quittingStationaryTotalHazard (limit.deletedRoot index who) := by
  obtain ⟨other, hother⟩ := exists_ne who
  have hterm : 0 < (limit.deletedRoot index who other true).toReal := by
    simpa [deletedRoot, Function.update_of_ne hother] using
      source.quitProbability_pos (limit.select index) other
  unfold quittingStationaryTotalHazard
  exact hterm.trans_le (Finset.single_le_sum
    (f := fun player ↦ (limit.deletedRoot index who player true).toReal)
    (fun _ _ ↦ ENNReal.toReal_nonneg) (Finset.mem_univ other))

private theorem selectedDirection_tendsto (limit : PeriodOneNormalizedSourceLimit source)
    (who : ι) :
    Tendsto (fun index ↦ (source.root (limit.select index) who true).toReal /
      quittingStationaryTotalHazard (source.root (limit.select index)))
      atTop (nhds (limit.direction.val who)) :=
  (((continuous_apply who).comp continuous_subtype_val).tendsto
    limit.direction).comp limit.direction_tendsto

/-- Immediate Quit converges to the owner's singleton payoff. -/
theorem selectedQuitNowPayoff_tendsto
    (limit : PeriodOneNormalizedSourceLimit source) (who : ι) :
    Tendsto (fun index ↦ quittingTerminalPayoff reward
      (Function.update (source.profile (limit.select index)) who
        (quittingPureTimeBehaviorStrategy reward who (some 0))) who)
      atTop (nhds (quittingSoloReward reward who who)) := by
  have hbound : ∀ index,
      |quittingTerminalPayoff reward
          (Function.update (source.profile (limit.select index)) who
            (quittingPureTimeBehaviorStrategy reward who (some 0))) who -
        quittingSoloReward reward who who| ≤
      2 * quittingRewardBound reward *
        quittingStationaryTotalHazard (source.root (limit.select index)) := by
    intro index
    rw [limit.selectedProfile_eq_stationary index]
    have hquit := abs_quittingStationaryFixedOpponentsQuitValue_sub_singleton_le
      (reward := reward) (source.root (limit.select index)) who
      (abs_reward_le_quittingRewardBound reward)
    have hmass := quittingRootOpponentAbsorptionMass_le_stationaryTotalHazard
      (source.root (limit.select index)) who
    rw [quittingTerminalPayoff_update_quitNow_eq_fixedOpponentsQuitValue]
    simp only [quittingProfileLiveRoot_stationary]
    exact hquit.trans (mul_le_mul_of_nonneg_left hmass
      (mul_nonneg (by norm_num) (quittingRewardBound_nonneg reward)))
  have hzero := Math.tendsto_zero_of_abs_le_of_tendsto_zero _ _
    (by simpa using
      (limit.totalHazard_tendsto_zero.const_mul (2 * quittingRewardBound reward)))
    (Eventually.of_forall hbound)
  simpa using hzero.add_const (quittingSoloReward reward who who)

/-- Literal Never has the normalized opponent singleton lottery as its limit.
The excluded direction-one boundary is retained explicitly. -/
theorem selectedNeverPayoff_tendsto
    (limit : PeriodOneNormalizedSourceLimit source) (who : ι)
    (hshare : limit.direction.val who < 1) :
    Tendsto (fun index ↦ quittingTerminalPayoff reward
      (Function.update (source.profile (limit.select index)) who
        (quittingPureTimeBehaviorStrategy reward who none)) who)
      atTop (nhds (limit.neverLimit who)) := by
  let roots := fun index ↦ source.root (limit.select index)
  let H := fun index ↦ quittingStationaryTotalHazard (roots index)
  let rate := fun index player ↦ (roots index player true).toReal / H index
  have hHpos : ∀ index, 0 < H index := fun index ↦
    source.totalHazard_pos (limit.select index)
  have hdeleted : Tendsto (fun index ↦
      quittingStationaryTotalHazard (limit.deletedRoot index who)) atTop (nhds 0) := by
    simp_rw [deleted_totalHazard]
    simpa using limit.totalHazard_tendsto_zero.sub
      (limit.selectedQuitProbability_tendsto_zero who)
  have hrate : ∀ player, Tendsto (fun index ↦ rate index player)
      atTop (nhds (limit.direction.val player)) := limit.selectedDirection_tendsto
  have hweights : ∀ player, Tendsto (fun index ↦
      (limit.deletedRoot index who player true).toReal /
        quittingStationaryTotalHazard (limit.deletedRoot index who)) atTop
      (nhds (if player = who then 0 else
        limit.direction.val player / (1 - limit.direction.val who))) := by
    intro player
    by_cases heq : player = who
    · subst player
      simp [deletedRoot]
    · have hratio := (hrate player).div
        (tendsto_const_nhds.sub (hrate who)) (sub_pos.mpr hshare).ne'
      rw [if_neg heq]
      apply hratio.congr'
      filter_upwards [] with index
      rw [deleted_totalHazard]
      simp only [deletedRoot, Function.update_of_ne heq]
      dsimp [rate, H, roots]
      field_simp [(hHpos index).ne']
      congr 1
      rw [mul_sub, mul_one, mul_div_cancel₀ _ (hHpos index).ne']
  have hbary := tendsto_finsetSum Finset.univ fun player _ ↦
    (hweights player).mul_const (quittingSoloReward reward player who)
  have htarget : (∑ player, (if player = who then 0 else
      limit.direction.val player / (1 - limit.direction.val who)) *
        quittingSoloReward reward player who) = limit.neverLimit who := by
    rw [neverLimit, limit.limitValue_eq_singletonDirectionPayoff]
    unfold quittingSingletonDirectionPayoff
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ who)]
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ who)]
    simp only [ite_true, zero_mul, add_zero, add_sub_cancel_right]
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro player hplayer
    rw [if_neg (Finset.ne_of_mem_erase hplayer)]
    ring
  rw [htarget] at hbary
  have hhalf : ∀ᶠ index in atTop,
      quittingStationaryTotalHazard (limit.deletedRoot index who) ≤ 1 / 2 :=
    (hdeleted.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))).mono
      fun _ h ↦ h.le
  have hdiff := Math.tendsto_zero_of_abs_le_of_tendsto_zero _ _
    (by simpa using hdeleted.const_mul (6 * quittingRewardBound reward))
    (hhalf.mono fun index h ↦
      abs_stationaryPayoff_sub_singletonDirectionBarycenter_le reward
        (abs_reward_le_quittingRewardBound reward) (limit.deletedRoot index who) who
        (limit.deleted_totalHazard_pos index who) h)
  have hpayoff := hdiff.add hbary
  simp only [zero_add] at hpayoff
  apply hpayoff.congr'
  filter_upwards [] with index
  rw [limit.selectedProfile_eq_stationary index,
    quittingPureTimeBehaviorStrategy_none_eq_alwaysContinue,
    update_quittingStationaryProfile_alwaysContinue]
  simp [quittingStationarySingletonDirectionBarycenter, deletedRoot]

/-- Two positive direction coordinates exclude unit mass at every player. -/
theorem direction_lt_one_of_two_positive
    (limit : PeriodOneNormalizedSourceLimit source)
    (htwo : ∃ first second : ι, first ≠ second ∧
      0 < limit.direction.val first ∧ 0 < limit.direction.val second)
    (who : ι) : limit.direction.val who < 1 := by
  obtain ⟨first, second, hne, hfirst, hsecond⟩ := htwo
  have hother : ∃ other : ι, other ≠ who ∧ 0 < limit.direction.val other := by
    by_cases hfirstWho : first = who
    · exact ⟨second, by simpa [hfirstWho] using hne.symm, hsecond⟩
    · exact ⟨first, hfirstWho, hfirst⟩
  obtain ⟨other, hne, hother⟩ := hother
  have hsingle : limit.direction.val other ≤
      ∑ player ∈ Finset.univ.erase who, limit.direction.val player :=
    Finset.single_le_sum (fun player _ ↦ limit.direction.property.1 player)
      (by simp [hne])
  have hsum := limit.direction.property.2
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ who)] at hsum
  linarith

/-- With four players, two positive shares leave exactly the support sizes
two, three, and four. -/
theorem positiveDirectionSupport_card
    (limit : PeriodOneNormalizedSourceLimit source)
    (hplayers : Fintype.card ι = 4)
    (htwo : ∃ first second : ι, first ≠ second ∧
      0 < limit.direction.val first ∧ 0 < limit.direction.val second) :
    (Finset.univ.filter fun who ↦ 0 < limit.direction.val who).card ∈
      ({2, 3, 4} : Finset ℕ) := by
  classical
  obtain ⟨first, second, hne, hfirst, hsecond⟩ := htwo
  have hsubset : ({first, second} : Finset ι) ⊆
      Finset.univ.filter (fun who ↦ 0 < limit.direction.val who) := by
    intro who hwho
    simp only [Finset.mem_insert, Finset.mem_singleton] at hwho
    rcases hwho with rfl | rfl <;> simp [hfirst, hsecond]
  have hlower := Finset.card_le_card hsubset
  have hupper := Finset.card_le_card
    (Finset.filter_subset (fun who ↦ 0 < limit.direction.val who) Finset.univ)
  simp [hne, hplayers] at hlower hupper ⊢
  omega

/-- The Never limit exceeds the singleton by the normalized singleton margin. -/
theorem neverLimit_sub_singleton
    (limit : PeriodOneNormalizedSourceLimit source) (who : ι)
    (hshare : limit.direction.val who < 1) :
    limit.neverLimit who - quittingSoloReward reward who who =
      limit.limitingSingletonMargin who / (1 - limit.direction.val who) := by
  rw [limit.limitingSingletonMargin_eq_limitValue_sub_solo]
  unfold neverLimit
  field_simp [(sub_pos.mpr hshare).ne']
  ring

/-- The exact limiting gain of the literal Never deviation. -/
theorem neverLimit_sub_value
    (limit : PeriodOneNormalizedSourceLimit source) (who : ι)
    (hshare : limit.direction.val who < 1) :
    limit.neverLimit who - limit.limitValue who =
      limit.direction.val who * limit.limitingSingletonMargin who /
        (1 - limit.direction.val who) := by
  rw [limit.limitingSingletonMargin_eq_limitValue_sub_solo]
  unfold neverLimit
  field_simp [(sub_pos.mpr hshare).ne']
  ring

/-- A positive limiting singleton margin selects Never as the exact complete
behavioral cap at every sufficiently late finite source. -/
theorem eventually_selectedNever_attains_completeCap
    (limit : PeriodOneNormalizedSourceLimit source) (who : ι)
    (hshare : limit.direction.val who < 1)
    (hmargin : 0 < limit.limitingSingletonMargin who) :
    ∀ᶠ index in atTop,
      quittingContinuationBestResponseValue reward
          (source.profile (limit.select index)) who =
        quittingTerminalPayoff reward
          (Function.update (source.profile (limit.select index)) who
            (quittingPureTimeBehaviorStrategy reward who none)) who := by
  have hgap : quittingSoloReward reward who who < limit.neverLimit who := by
    have hid := limit.neverLimit_sub_singleton who hshare
    have hpos := div_pos hmargin (sub_pos.mpr hshare)
    linarith
  have hlt := (limit.selectedQuitNowPayoff_tendsto who).eventually_lt
    (limit.selectedNeverPayoff_tendsto who hshare) hgap
  filter_upwards [hlt] with index hindex
  rw [limit.selectedCompleteBehavioralCap_eq_max_quitNow_never index who,
    max_eq_right hindex.le]

/-- Complete unrestricted caps converge to the literal Never limit. -/
theorem selectedCompleteCap_tendsto_neverLimit
    (limit : PeriodOneNormalizedSourceLimit source) (who : ι)
    (hshare : limit.direction.val who < 1)
    (hmargin : 0 < limit.limitingSingletonMargin who) :
    Tendsto (fun index ↦ quittingContinuationBestResponseValue reward
      (source.profile (limit.select index)) who) atTop (nhds (limit.neverLimit who)) :=
  (limit.selectedNeverPayoff_tendsto who hshare).congr'
    ((limit.eventually_selectedNever_attains_completeCap who hshare hmargin).mono
      fun _ h ↦ h.symm)

/-- Complete behavioral debt converges to the direction-weighted margin. -/
theorem selectedCompleteDebt_tendsto
    (limit : PeriodOneNormalizedSourceLimit source) (who : ι)
    (hshare : limit.direction.val who < 1)
    (hmargin : 0 < limit.limitingSingletonMargin who) :
    Tendsto (fun index ↦ quittingTerminalDeviationDebt reward
      (source.profile (limit.select index)) who) atTop
      (nhds (limit.direction.val who * limit.limitingSingletonMargin who /
        (1 - limit.direction.val who))) := by
  have hvalue : Tendsto (fun index ↦ quittingTerminalPayoff reward
      (source.profile (limit.select index)) who) atTop (nhds (limit.limitValue who)) := by
    simp_rw [limit.selectedTerminalPayoff_eq_value]
    exact ((continuous_apply who).tendsto limit.limitValue).comp limit.value_tendsto
  have h := (limit.selectedCompleteCap_tendsto_neverLimit who hshare hmargin).sub hvalue
  rw [limit.neverLimit_sub_value who hshare] at h
  exact h

/-- Every zero-share outsider has vanishing complete behavioral debt. -/
theorem selectedOutsiderDebt_tendsto_zero
    (limit : PeriodOneNormalizedSourceLimit source) (who : ι)
    (hzero : limit.direction.val who = 0)
    (hmargin : 0 < limit.limitingSingletonMargin who) :
    Tendsto (fun index ↦ quittingTerminalDeviationDebt reward
      (source.profile (limit.select index)) who) atTop (nhds 0) := by
  simpa [hzero] using limit.selectedCompleteDebt_tendsto who (by rw [hzero]; norm_num)
    hmargin

/-- The actual Never gain has the same limiting value as complete debt. -/
theorem selectedNeverGain_tendsto
    (limit : PeriodOneNormalizedSourceLimit source) (who : ι)
    (hshare : limit.direction.val who < 1) :
    Tendsto (fun index ↦ quittingTerminalPayoff reward
        (Function.update (source.profile (limit.select index)) who
          (quittingPureTimeBehaviorStrategy reward who none)) who -
      quittingTerminalPayoff reward (source.profile (limit.select index)) who)
      atTop (nhds (limit.direction.val who * limit.limitingSingletonMargin who /
        (1 - limit.direction.val who))) := by
  have hvalue : Tendsto (fun index ↦ quittingTerminalPayoff reward
      (source.profile (limit.select index)) who) atTop (nhds (limit.limitValue who)) := by
    simp_rw [limit.selectedTerminalPayoff_eq_value]
    exact ((continuous_apply who).tendsto limit.limitValue).comp limit.value_tendsto
  have h := (limit.selectedNeverPayoff_tendsto who hshare).sub hvalue
  rw [limit.neverLimit_sub_value who hshare] at h
  exact h

/-- Two fixed support players have uniformly profitable literal Never
deviations on the same selected source profiles. -/
theorem exists_two_fixed_neverDebtors
    (limit : PeriodOneNormalizedSourceLimit source)
    (hplayers : Fintype.card ι = 4)
    (hno : ¬ ∃ payoff : Payoff ι,
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff)
    (herrorPos : ∀ index, 0 < error index)
    (herror : Tendsto error atTop (nhds 0)) :
    ∃ first second : ι, first ≠ second ∧
      0 < limit.direction.val first ∧ 0 < limit.direction.val second ∧
      ∃ gain : ℝ, 0 < gain ∧ ∀ᶠ index in atTop,
        ∀ who ∈ ({first, second} : Finset ι), gain ≤
          quittingTerminalPayoff reward
              (Function.update (source.profile (limit.select index)) who
                (quittingPureTimeBehaviorStrategy reward who none)) who -
            quittingTerminalPayoff reward (source.profile (limit.select index)) who := by
  have htwo := limit.exists_two_distinct_direction_positive hplayers hno herrorPos herror
  obtain ⟨first, second, hne, hfirst, hsecond⟩ := htwo
  let gain := fun who ↦ limit.direction.val who * limit.limitingSingletonMargin who /
    (1 - limit.direction.val who)
  have hgain : ∀ who, 0 < limit.direction.val who → 0 < gain who := by
    intro who hwho
    exact div_pos (mul_pos hwho
      (limit.limitingSingletonMargin_pos_of_fourPlayer_noUniformPayoff
        hplayers hno herrorPos herror who))
      (sub_pos.mpr (limit.direction_lt_one_of_two_positive
        ⟨first, second, hne, hfirst, hsecond⟩ who))
  let gamma := min (gain first) (gain second) / 2
  have hgamma : 0 < gamma := half_pos (lt_min (hgain first hfirst) (hgain second hsecond))
  have hbound : ∀ who ∈ ({first, second} : Finset ι), gamma < gain who := by
    intro who hwho
    rcases Finset.mem_insert.mp hwho with heq | hwho
    · rw [heq]
      have hmin := min_le_left (gain first) (gain second)
      dsimp [gamma] at hgamma ⊢
      linarith
    · have heq := Finset.mem_singleton.mp hwho
      subst who
      have hmin := min_le_right (gain first) (gain second)
      dsimp [gamma] at hgamma ⊢
      linarith
  refine ⟨first, second, hne, hfirst, hsecond, gamma, hgamma, ?_⟩
  apply (Finset.eventually_all _).2
  intro who hwho
  exact ((tendsto_order.1 (limit.selectedNeverGain_tendsto who
    (limit.direction_lt_one_of_two_positive ⟨first, second, hne, hfirst, hsecond⟩ who))).1
      gamma (hbound who hwho)).mono fun _ h ↦ h.le

end PeriodOneNormalizedSourceLimit

/-- A four-player counterexample produces one stationary source family with
the common positive singleton margin, exact endpoint-regret density, complete
cap and debt limits, and two fixed profitable Never deviations. All limits
and finite responses use the same strict selection of that one family. -/
theorem exists_periodOne_tropical_twoNever_escape_of_fourPlayer_noUniformPayoff
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hplayers : Fintype.card ι = 4)
    (hno : ¬ ∃ payoff : Payoff ι,
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff)
    (error : ℕ → ℝ) (herrorPos : ∀ index, 0 < error index)
    (herror : Tendsto error atTop (nhds 0)) :
    ∃ source : PeriodOneVanishingHazardSource reward error,
      ∃ limit : PeriodOneNormalizedSourceLimit source,
        ∃ minimum : ℝ, 0 < minimum ∧
          (∀ who, minimum ≤ limit.limitingSingletonMargin who) ∧
          (∀ who, 0 < limit.direction.val who →
            limit.limitingSingletonMargin who = minimum) ∧
          Tendsto (fun index ↦ limit.selectedTotalEndpointRegret index /
            quittingStationaryTotalHazard (source.root (limit.select index)))
            atTop (nhds minimum) ∧
          (∀ who,
            limit.direction.val who < 1 ∧
            Tendsto (fun index ↦ quittingTerminalPayoff reward
              (Function.update (source.profile (limit.select index)) who
                (quittingPureTimeBehaviorStrategy reward who (some 0))) who)
              atTop (nhds (quittingSoloReward reward who who)) ∧
            Tendsto (fun index ↦ quittingTerminalPayoff reward
              (Function.update (source.profile (limit.select index)) who
                (quittingPureTimeBehaviorStrategy reward who none)) who)
              atTop (nhds (limit.neverLimit who)) ∧
            Tendsto (fun index ↦ quittingContinuationBestResponseValue reward
              (source.profile (limit.select index)) who)
              atTop (nhds (limit.neverLimit who)) ∧
            Tendsto (fun index ↦ quittingTerminalDeviationDebt reward
              (source.profile (limit.select index)) who) atTop
              (nhds (limit.direction.val who * minimum / (1 - limit.direction.val who))) ∧
            ∀ᶠ index in atTop,
              quittingContinuationBestResponseValue reward
                  (source.profile (limit.select index)) who =
                quittingTerminalPayoff reward
                  (Function.update (source.profile (limit.select index)) who
                    (quittingPureTimeBehaviorStrategy reward who none)) who) ∧
          ∃ first second : ι, first ≠ second ∧
            0 < limit.direction.val first ∧ 0 < limit.direction.val second ∧
            ∃ gain : ℝ, 0 < gain ∧ ∀ᶠ index in atTop,
              ∀ who ∈ ({first, second} : Finset ι), gain ≤
                quittingTerminalPayoff reward
                    (Function.update (source.profile (limit.select index)) who
                      (quittingPureTimeBehaviorStrategy reward who none)) who -
                  quittingTerminalPayoff reward (source.profile (limit.select index)) who := by
  obtain ⟨source, ⟨limit⟩⟩ :=
    exists_periodOneNormalizedSourceLimit_of_fourPlayer_noUniformPayoff
      reward hplayers hno error herrorPos herror
  obtain ⟨minimum, hminimum, hlower, hequal, hdensity⟩ :=
    limit.exists_positive_commonMinimum_and_totalEndpointRegretDensity_tendsto
      hplayers hno herrorPos herror
  refine ⟨source, limit, minimum, hminimum, hlower, hequal, hdensity, ?_,
    limit.exists_two_fixed_neverDebtors hplayers hno herrorPos herror⟩
  intro who
  have hshare := limit.direction_lt_one_of_two_positive
    (limit.exists_two_distinct_direction_positive hplayers hno herrorPos herror) who
  have hmargin : 0 < limit.limitingSingletonMargin who :=
    hminimum.trans_le (hlower who)
  have hproduct : limit.direction.val who * limit.limitingSingletonMargin who =
      limit.direction.val who * minimum := by
    by_cases hzero : limit.direction.val who = 0
    · simp [hzero]
    · rw [hequal who (lt_of_le_of_ne (limit.direction.property.1 who) (Ne.symm hzero))]
  refine ⟨hshare, limit.selectedQuitNowPayoff_tendsto who,
    limit.selectedNeverPayoff_tendsto who hshare,
    limit.selectedCompleteCap_tendsto_neverLimit who hshare hmargin, ?_,
    limit.eventually_selectedNever_attains_completeCap who hshare hmargin⟩
  simpa only [hproduct] using limit.selectedCompleteDebt_tendsto who hshare hmargin

end GameTheory
