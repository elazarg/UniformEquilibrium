/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.AbsorptionPath.SingletonPathSnell

/-!
# Tail laws for deleted singleton clocks

This module proves the residual-law consequences of finite deleted-clock
Snell identities.  In particular, finite limiting deleted hazard forces the
conditional residual singleton law to concentrate on the undeleted owner.
-/

noncomputable section

namespace GameTheory
namespace QuittingLCPClassification

open Filter Finset Set unitInterval
open MeasureTheory QuittingAbsorptionPath
open scoped Interval Topology unitInterval

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Conditional residual mass of one singleton owner in logarithmic time. -/
def ContinuousZeroPerfectSingletonPath.logResidualWeight
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (witness : ContinuousZeroPerfectSingletonPath reward)
    (owner : ι) (tau : ℝ) : ℝ :=
  Real.exp tau * (witness.terminal owner - witness.logMass owner tau)

theorem ContinuousZeroPerfectSingletonPath.logResidualWeight_nonneg
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (witness : ContinuousZeroPerfectSingletonPath reward)
    (owner : ι) {tau : ℝ} (htau : 0 ≤ tau) :
    0 ≤ witness.logResidualWeight owner tau := by
  unfold ContinuousZeroPerfectSingletonPath.logResidualWeight
  apply mul_nonneg (Real.exp_nonneg _)
  rw [witness.logMass_eq_mass owner htau]
  apply sub_nonneg.mpr
  let clock : unitInterval :=
    ⟨logarithmicPathClock tau, (logarithmicPathClock_mem_Ico htau).1,
      (logarithmicPathClock_mem_Ico htau).2.le⟩
  simpa only [clock, witness.mass.target] using
    witness.monotone owner (show clock ≤ (1 : unitInterval) by
      exact (logarithmicPathClock_mem_Ico htau).2.le)

theorem ContinuousZeroPerfectSingletonPath.sum_logResidualWeight
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (witness : ContinuousZeroPerfectSingletonPath reward)
    {tau : ℝ} (htau : 0 ≤ tau) :
    ∑ owner, witness.logResidualWeight owner tau = 1 := by
  unfold ContinuousZeroPerfectSingletonPath.logResidualWeight
  rw [← Finset.mul_sum, Finset.sum_sub_distrib, witness.sum_logMass htau]
  have hterminal : ∑ owner, witness.terminal owner = 1 := by
    simpa using witness.total (1 : unitInterval)
  rw [hterminal, logarithmicPathClock]
  rw [show Real.exp tau * (1 - (1 - Real.exp (-tau))) = 1 by
    rw [show 1 - (1 - Real.exp (-tau)) = Real.exp (-tau) by ring,
      ← Real.exp_add]
    simp]

/-- Logarithmic payoff is the residual singleton mixture. -/
theorem ContinuousZeroPerfectSingletonPath.logPayoff_eq_residualMixture
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (witness : ContinuousZeroPerfectSingletonPath reward)
    (tau : ℝ) (who : ι) :
    witness.logPayoff reward tau who =
      ∑ owner, witness.logResidualWeight owner tau *
        quittingSoloReward reward owner who := by
  unfold ContinuousZeroPerfectSingletonPath.logPayoff
    ContinuousZeroPerfectSingletonPath.logResidualWeight
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro owner _
  ring

theorem ContinuousZeroPerfectSingletonPath.logResidualWeight_le_one
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (witness : ContinuousZeroPerfectSingletonPath reward)
    (owner : ι) {tau : ℝ} (htau : 0 ≤ tau) :
    witness.logResidualWeight owner tau ≤ 1 := by
  rw [← witness.sum_logResidualWeight htau]
  exact Finset.single_le_sum
    (fun other _ => witness.logResidualWeight_nonneg other htau)
    (Finset.mem_univ owner)

/-- A path payoff is uniformly bounded by the finite sum of absolute
singleton rewards. -/
theorem ContinuousZeroPerfectSingletonPath.abs_logPayoff_le_sum_abs
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (witness : ContinuousZeroPerfectSingletonPath reward)
    {tau : ℝ} (htau : 0 ≤ tau) (who : ι) :
    |witness.logPayoff reward tau who| ≤
      ∑ owner, |quittingSoloReward reward owner who| := by
  rw [witness.logPayoff_eq_residualMixture reward tau who]
  calc
    |∑ owner, witness.logResidualWeight owner tau *
        quittingSoloReward reward owner who| ≤
        ∑ owner, |witness.logResidualWeight owner tau *
          quittingSoloReward reward owner who| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ owner, witness.logResidualWeight owner tau *
        |quittingSoloReward reward owner who| := by
      apply Finset.sum_congr rfl
      intro owner _
      rw [abs_mul, abs_of_nonneg
        (witness.logResidualWeight_nonneg owner htau)]
    _ ≤ ∑ owner, |quittingSoloReward reward owner who| := by
      apply Finset.sum_le_sum
      intro owner _
      simpa only [one_mul] using mul_le_mul_of_nonneg_right
        (witness.logResidualWeight_le_one owner htau) (abs_nonneg _)

/-- A logarithmic mass increment is the exponentially discounted integral of
its conditional hazard. -/
theorem ContinuousZeroPerfectSingletonPath.logMass_sub_eq_integral_logRate
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (witness : ContinuousZeroPerfectSingletonPath reward)
    (owner : ι) {first second : ℝ}
    (hfirst : 0 ≤ first) (hsecond : first ≤ second) :
    witness.logMass owner second - witness.logMass owner first =
      ∫ tau in first..second,
        Real.exp (-tau) * witness.logRate owner tau := by
  have hAC := (witness.logMass_absolutelyContinuousOnInterval owner
    (hfirst.trans hsecond)).mono (by
      rw [uIcc_of_le hsecond, uIcc_of_le (hfirst.trans hsecond)]
      intro tau htau
      exact ⟨hfirst.trans htau.1, htau.2⟩)
  rw [← hAC.integral_deriv_eq_sub]
  apply intervalIntegral.integral_congr
  intro tau _
  unfold ContinuousZeroPerfectSingletonPath.logRate
  change deriv (witness.logMass owner) tau =
    Real.exp (-tau) * (Real.exp tau * deriv (witness.logMass owner) tau)
  rw [← mul_assoc, ← Real.exp_add]
  simp

/-- Total opponent residual weight at a logarithmic time. -/
def ContinuousZeroPerfectSingletonPath.deletedResidualWeight
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (witness : ContinuousZeroPerfectSingletonPath reward)
    (who : ι) (tau : ℝ) : ℝ :=
  ∑ owner ∈ Finset.univ.erase who, witness.logResidualWeight owner tau

theorem ContinuousZeroPerfectSingletonPath.deletedResidualWeight_nonneg
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (witness : ContinuousZeroPerfectSingletonPath reward)
    (who : ι) {tau : ℝ} (htau : 0 ≤ tau) :
    0 ≤ witness.deletedResidualWeight who tau :=
  Finset.sum_nonneg fun owner _ => witness.logResidualWeight_nonneg owner htau

/-- A two-scale bound: residual opponent weight is controlled by the next
deleted-hazard increment and the residual mass beyond twice the time. -/
theorem ContinuousZeroPerfectSingletonPath.deletedResidualWeight_le
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (witness : ContinuousZeroPerfectSingletonPath reward)
    (who : ι) {T : ℝ} (hT : 0 ≤ T) :
    witness.deletedResidualWeight who T ≤
      witness.deletedHazard who (2 * T) - witness.deletedHazard who T +
        Real.exp (-T) := by
  have hT2 : T ≤ 2 * T := by linarith
  have h2T : 0 ≤ 2 * T := by linarith
  let others := Finset.univ.erase who
  have hinc : (∑ owner ∈ others,
      (witness.logMass owner (2 * T) - witness.logMass owner T)) =
      ∫ tau in T..2 * T,
        Real.exp (-tau) * witness.deletedHazardRate who tau := by
    calc
      _ = ∑ owner ∈ others, ∫ tau in T..2 * T,
          Real.exp (-tau) * witness.logRate owner tau := by
        apply Finset.sum_congr rfl
        intro owner _
        exact witness.logMass_sub_eq_integral_logRate owner hT hT2
      _ = ∫ tau in T..2 * T,
          ∑ owner ∈ others,
            Real.exp (-tau) * witness.logRate owner tau := by
        rw [intervalIntegral.integral_finsetSum]
        intro owner _
        exact (witness.logRate_intervalIntegrable owner hT hT2)
          |>.continuousOn_mul
            (Real.continuous_exp.comp continuous_neg).continuousOn
      _ = _ := by
        apply intervalIntegral.integral_congr_ae
        filter_upwards [witness.ae_sum_logRate_eq_one h2T,
          volume.ae_ne (2 * T)] with tau hsum hne htau
        rw [uIoc_of_le hT2] at htau
        have htauIoo : tau ∈ Set.Ioo (0 : ℝ) (2 * T) :=
          ⟨hT.trans_lt htau.1, htau.2.lt_of_ne hne⟩
        have hsplit : ∑ owner ∈ others, witness.logRate owner tau =
            witness.deletedHazardRate who tau := by
          have hall := hsum htauIoo
          have herase := Finset.sum_erase_add Finset.univ
            (fun owner => witness.logRate owner tau) (Finset.mem_univ who)
          unfold ContinuousZeroPerfectSingletonPath.deletedHazardRate
          rw [← herase] at hall
          linarith
        rw [← Finset.mul_sum, hsplit]
  have hweightedIntegrable : IntervalIntegrable
      (fun tau => Real.exp (-tau) * witness.deletedHazardRate who tau)
      volume T (2 * T) :=
    (witness.deletedHazardRate_intervalIntegrable who hT hT2)
      |>.continuousOn_mul
        (Real.continuous_exp.comp continuous_neg).continuousOn
  have hincBound : Real.exp T * (∑ owner ∈ others,
      (witness.logMass owner (2 * T) - witness.logMass owner T)) ≤
      witness.deletedHazard who (2 * T) - witness.deletedHazard who T := by
    rw [hinc, ← intervalIntegral.integral_const_mul,
      witness.deletedHazard_sub who hT hT2]
    apply intervalIntegral.integral_mono_ae_restrict hT2
      (hweightedIntegrable.const_mul _) 
      (witness.deletedHazardRate_intervalIntegrable who hT hT2)
    apply (ae_restrict_iff' measurableSet_Icc).2
    filter_upwards [witness.ae_deletedHazardRate_nonneg who h2T]
      with tau hrate htau
    have hrate' := hrate ⟨hT.trans htau.1, htau.2⟩
    have hexp : Real.exp T * Real.exp (-tau) ≤ 1 := by
      rw [← Real.exp_add, ← Real.exp_zero, Real.exp_le_exp]
      linarith [htau.1]
    nlinarith
  have htailNonneg (owner : ι) :
      0 ≤ witness.terminal owner - witness.logMass owner (2 * T) := by
    rw [witness.logMass_eq_mass owner h2T]
    apply sub_nonneg.mpr
    let clock : unitInterval :=
      ⟨logarithmicPathClock (2 * T),
        (logarithmicPathClock_mem_Ico h2T).1,
        (logarithmicPathClock_mem_Ico h2T).2.le⟩
    simpa only [clock, witness.mass.target] using
      witness.monotone owner (show clock ≤ (1 : unitInterval) by
        exact (logarithmicPathClock_mem_Ico h2T).2.le)
  have htailSum : (∑ owner,
      (witness.terminal owner - witness.logMass owner (2 * T))) =
      Real.exp (-(2 * T)) := by
    rw [Finset.sum_sub_distrib, witness.sum_logMass h2T]
    have hterminal : ∑ owner, witness.terminal owner = 1 := by
      simpa using witness.total (1 : unitInterval)
    rw [hterminal, logarithmicPathClock]
    ring
  have htailBound : (∑ owner ∈ others,
      (witness.terminal owner - witness.logMass owner (2 * T))) ≤
      Real.exp (-(2 * T)) := by
    have hsplit := Finset.sum_erase_add Finset.univ
      (fun owner => witness.terminal owner - witness.logMass owner (2 * T))
      (Finset.mem_univ who)
    rw [htailSum] at hsplit
    dsimp only [others]
    linarith [htailNonneg who]
  unfold ContinuousZeroPerfectSingletonPath.deletedResidualWeight
    ContinuousZeroPerfectSingletonPath.logResidualWeight
  rw [← Finset.mul_sum]
  change Real.exp T * (∑ owner ∈ others,
      (witness.terminal owner - witness.logMass owner T)) ≤ _
  have hsplitResidual : (∑ owner ∈ others,
      (witness.terminal owner - witness.logMass owner T)) =
      (∑ owner ∈ others,
        (witness.logMass owner (2 * T) - witness.logMass owner T)) +
      ∑ owner ∈ others,
        (witness.terminal owner - witness.logMass owner (2 * T)) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro owner _
    ring
  rw [hsplitResidual, mul_add]
  have htailScaled : Real.exp T * (∑ owner ∈ others,
      (witness.terminal owner - witness.logMass owner (2 * T))) ≤
      Real.exp (-T) := by
    calc
      _ ≤ Real.exp T * Real.exp (-(2 * T)) := by
        gcongr
      _ = Real.exp (-T) := by
        rw [← Real.exp_add]
        congr 1
        ring
  linarith

/-- A positive deleted-survival limit gives a finite cumulative-hazard
limit, obtained by taking logarithms. -/
theorem ContinuousZeroPerfectSingletonPath.tendsto_deletedHazard_of_survival
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (witness : ContinuousZeroPerfectSingletonPath reward)
    (who : ι) {limit : ℝ}
    (htendsto : Tendsto (witness.deletedSurvival who) atTop (nhds limit))
    (hlimit : 0 < limit) :
    Tendsto (witness.deletedHazard who) atTop
      (nhds (-Real.log limit)) := by
  have hlog := (Real.continuousAt_log hlimit.ne').tendsto.comp htendsto
  have hneg := hlog.neg
  have heq : (fun T => -Real.log (witness.deletedSurvival who T)) =
      witness.deletedHazard who := by
    funext T
    simp only [witness.deletedSurvival_apply, Real.log_exp, neg_neg]
  rw [← heq]
  exact hneg

/-- Finite limiting deleted hazard forces the opponent residual law to
vanish. -/
theorem ContinuousZeroPerfectSingletonPath.tendsto_deletedResidualWeight
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (witness : ContinuousZeroPerfectSingletonPath reward)
    (who : ι) {limit : ℝ}
    (htendsto : Tendsto (witness.deletedHazard who) atTop (nhds limit)) :
    Tendsto (witness.deletedResidualWeight who) atTop (nhds 0) := by
  have htwo : Tendsto (fun T : ℝ => 2 * T) atTop atTop :=
    tendsto_id.const_mul_atTop (by norm_num)
  have htwice : Tendsto (fun T : ℝ => witness.deletedHazard who (2 * T))
      atTop (nhds limit) := htendsto.comp htwo
  have hupper : Tendsto (fun T : ℝ =>
      witness.deletedHazard who (2 * T) - witness.deletedHazard who T +
        Real.exp (-T)) atTop (nhds 0) := by
    simpa only [sub_self, zero_add] using
      (htwice.sub htendsto).add Real.tendsto_exp_neg_atTop_nhds_zero
  apply squeeze_zero'
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with T hT
    exact witness.deletedResidualWeight_nonneg who hT
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with T hT
    exact witness.deletedResidualWeight_le who hT
  · exact hupper

/-- Every deleted-survival clock has a finite nonnegative limit. -/
theorem ContinuousZeroPerfectSingletonPath.exists_deletedSurvival_limit
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (witness : ContinuousZeroPerfectSingletonPath reward)
    (who : ι) :
    ∃ limit : ℝ, 0 ≤ limit ∧
      Tendsto (witness.deletedSurvival who) atTop (nhds limit) := by
  let clamped : ℝ → ℝ := fun T =>
    witness.deletedSurvival who (max 0 T)
  have hanti : Antitone clamped := by
    intro first second hle
    exact witness.deletedSurvival_anti who (le_max_left 0 first)
      (max_le_max_left 0 hle)
  rcases tendsto_atTop_of_antitone hanti with hbot | ⟨limit, hlimit⟩
  · have hnegative := (tendsto_atBot.1 hbot) (-1)
    obtain ⟨T, hT⟩ := hnegative.exists
    have hpositive : 0 < clamped T := Real.exp_pos _
    linarith
  · refine ⟨limit, ?_, ?_⟩
    · apply ge_of_tendsto hlimit
      filter_upwards with T
      exact Real.exp_nonneg _
    · apply hlimit.congr'
      filter_upwards [eventually_ge_atTop (0 : ℝ)] with T hT
      simp only [clamped, max_eq_right hT]

/-- Exact exceptional split for deleted clocks: either one owner has a
positive limit, or every deleted survival vanishes. -/
theorem ContinuousZeroPerfectSingletonPath.exists_positive_deletedLimit_or_all_zero
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (witness : ContinuousZeroPerfectSingletonPath reward) :
    (∃ owner limit, 0 < limit ∧
      Tendsto (witness.deletedSurvival owner) atTop (nhds limit)) ∨
      ∀ who, Tendsto (witness.deletedSurvival who) atTop (nhds 0) := by
  by_cases hpositive : ∃ owner limit, 0 < limit ∧
      Tendsto (witness.deletedSurvival owner) atTop (nhds limit)
  · exact Or.inl hpositive
  · right
    intro who
    obtain ⟨limit, hlimitNonneg, htendsto⟩ :=
      witness.exists_deletedSurvival_limit who
    have hnotPos : ¬0 < limit := by
      intro hlimitPos
      exact hpositive ⟨who, limit, hlimitPos, htendsto⟩
    have hzero : limit = 0 := le_antisymm (le_of_not_gt hnotPos) hlimitNonneg
    simpa only [hzero] using htendsto

/-- Under finite deleted hazard, the residual singleton law concentrates on
the undeleted owner. -/
theorem ContinuousZeroPerfectSingletonPath.tendsto_logResidualWeight
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (witness : ContinuousZeroPerfectSingletonPath reward)
    (owner : ι) {limit : ℝ}
    (htendsto : Tendsto (witness.deletedHazard owner) atTop (nhds limit)) :
    ∀ who, Tendsto (witness.logResidualWeight who) atTop
      (nhds (if who = owner then 1 else 0)) := by
  have hdeleted := witness.tendsto_deletedResidualWeight owner htendsto
  intro who
  by_cases hwho : who = owner
  · subst who
    rw [if_pos rfl]
    have heq : ∀ T : ℝ, 0 ≤ T →
        witness.logResidualWeight owner T =
          1 - witness.deletedResidualWeight owner T := by
      intro T hT
      have hsplit := Finset.sum_erase_add Finset.univ
        (fun who => witness.logResidualWeight who T) (Finset.mem_univ owner)
      rw [witness.sum_logResidualWeight hT] at hsplit
      unfold ContinuousZeroPerfectSingletonPath.deletedResidualWeight
      linarith
    have hsub : Tendsto (fun T : ℝ =>
        (1 : ℝ) - witness.deletedResidualWeight owner T) atTop (nhds 1) := by
      simpa using (tendsto_const_nhds.sub hdeleted)
    apply Tendsto.congr' _ hsub
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with T hT
    exact (heq T hT).symm
  · rw [if_neg hwho]
    refine squeeze_zero' ?_ ?_ hdeleted
    · filter_upwards [eventually_ge_atTop (0 : ℝ)] with T hT
      exact witness.logResidualWeight_nonneg who hT
    · filter_upwards [eventually_ge_atTop (0 : ℝ)] with T hT
      unfold ContinuousZeroPerfectSingletonPath.deletedResidualWeight
      exact Finset.single_le_sum
        (fun other _ => witness.logResidualWeight_nonneg other hT)
        (by simp [hwho])

/-- Positive deleted survival identifies the terminal residual payoff with
the singleton row of the exceptional owner. -/
theorem ContinuousZeroPerfectSingletonPath.tendsto_logPayoff_of_positive_survival
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (witness : ContinuousZeroPerfectSingletonPath reward)
    (owner : ι) {limit : ℝ}
    (htendsto : Tendsto (witness.deletedSurvival owner) atTop (nhds limit))
    (hlimit : 0 < limit) (who : ι) :
    Tendsto (witness.logPayoff reward · who) atTop
      (nhds (quittingSoloReward reward owner who)) := by
  have hweight := witness.tendsto_logResidualWeight owner
    (witness.tendsto_deletedHazard_of_survival owner htendsto hlimit)
  rw [show (fun tau => witness.logPayoff reward tau who) =
      fun tau => ∑ other,
        witness.logResidualWeight other tau *
          quittingSoloReward reward other who by
    funext tau
    exact witness.logPayoff_eq_residualMixture reward tau who]
  have hsum := tendsto_finsetSum (Finset.univ : Finset ι)
    (fun other _ => (hweight other).mul_const
      (quittingSoloReward reward other who))
  convert hsum using 1
  simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq',
    Finset.mem_univ, if_pos]

/-- The terminal residual product in the deleted Snell identity has its exact
positive-survival limit. -/
theorem ContinuousZeroPerfectSingletonPath.tendsto_deletedProduct_of_positive_survival
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (witness : ContinuousZeroPerfectSingletonPath reward)
    (owner : ι) {limit : ℝ}
    (htendsto : Tendsto (witness.deletedSurvival owner) atTop (nhds limit))
    (hlimit : 0 < limit) :
    Tendsto (fun T => witness.deletedSurvival owner T *
      witness.logPayoff reward T owner) atTop
      (nhds (limit * quittingSoloReward reward owner owner)) :=
  htendsto.mul
    (witness.tendsto_logPayoff_of_positive_survival reward owner
      htendsto hlimit owner)

/-- If deleted survival vanishes, the terminal residual term in the Snell
identity vanishes without requiring convergence of the payoff itself. -/
theorem ContinuousZeroPerfectSingletonPath.tendsto_deletedProduct_of_zero_survival
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (witness : ContinuousZeroPerfectSingletonPath reward)
    (who : ι)
    (htendsto : Tendsto (witness.deletedSurvival who) atTop (nhds 0)) :
    Tendsto (fun T => witness.deletedSurvival who T *
      witness.logPayoff reward T who) atTop (nhds 0) := by
  rw [tendsto_zero_iff_abs_tendsto_zero]
  let B : ℝ := ∑ owner, |quittingSoloReward reward owner who|
  have hupper : Tendsto (fun T => witness.deletedSurvival who T * B)
      atTop (nhds 0) := by
    simpa only [zero_mul] using htendsto.mul_const B
  refine squeeze_zero' ?_ ?_ hupper
  · filter_upwards with T
    exact abs_nonneg _
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with T hT
    change |witness.deletedSurvival who T *
      witness.logPayoff reward T who| ≤
        witness.deletedSurvival who T * B
    have hsurvival : 0 ≤ witness.deletedSurvival who T := Real.exp_nonneg _
    rw [abs_mul, abs_of_nonneg hsurvival]
    dsimp only [B]
    exact mul_le_mul_of_nonneg_left
      (witness.abs_logPayoff_le_sum_abs reward hT who)
      (Real.exp_nonneg _)

/-- Continuum opponent-only payoff accumulated before logarithmic time `T`. -/
def ContinuousZeroPerfectSingletonPath.deletedOpponentLedger
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (witness : ContinuousZeroPerfectSingletonPath reward)
    (who : ι) (T : ℝ) : ℝ :=
  ∫ tau in 0..T, witness.deletedSurvival who tau *
    witness.deletedOpponentPayoffRate reward who tau

/-- Positive deleted survival gives the exact continuum Never payoff. -/
theorem ContinuousZeroPerfectSingletonPath.tendsto_deletedOpponentLedger_of_positive_survival
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (witness : ContinuousZeroPerfectSingletonPath reward)
    (owner : ι) {limit : ℝ}
    (htendsto : Tendsto (witness.deletedSurvival owner) atTop (nhds limit))
    (hlimit : 0 < limit) :
    Tendsto (witness.deletedOpponentLedger reward owner) atTop
      (nhds (witness.logPayoff reward 0 owner -
        limit * quittingSoloReward reward owner owner)) := by
  have hproduct := witness.tendsto_deletedProduct_of_positive_survival
    reward owner htendsto hlimit
  apply Tendsto.congr' _ (tendsto_const_nhds.sub hproduct)
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with T hT
  have hsnell := witness.deletedSnell_identity reward owner hT
  unfold ContinuousZeroPerfectSingletonPath.deletedOpponentLedger
  linarith

/-- When deleted survival vanishes, the continuum Never payoff equals the
initial continuation value and is therefore capped exactly. -/
theorem ContinuousZeroPerfectSingletonPath.tendsto_deletedOpponentLedger_of_zero_survival
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (witness : ContinuousZeroPerfectSingletonPath reward)
    (who : ι)
    (htendsto : Tendsto (witness.deletedSurvival who) atTop (nhds 0)) :
    Tendsto (witness.deletedOpponentLedger reward who) atTop
      (nhds (witness.logPayoff reward 0 who)) := by
  have hproduct := witness.tendsto_deletedProduct_of_zero_survival
    reward who htendsto
  have hsub : Tendsto (fun T => witness.logPayoff reward 0 who -
      witness.deletedSurvival who T * witness.logPayoff reward T who)
      atTop (nhds (witness.logPayoff reward 0 who)) := by
    simpa using tendsto_const_nhds.sub hproduct
  apply Tendsto.congr' _ hsub
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with T hT
  have hsnell := witness.deletedSnell_identity reward who hT
  unfold ContinuousZeroPerfectSingletonPath.deletedOpponentLedger
  linarith

end QuittingLCPClassification
end GameTheory
