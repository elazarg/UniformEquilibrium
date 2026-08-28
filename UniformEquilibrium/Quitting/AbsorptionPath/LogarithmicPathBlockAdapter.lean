/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.AbsorptionPath.LogarithmicProductDecoder
import UniformEquilibrium.Quitting.AbsorptionPath.PunishmentNormalPathSnell

/-!
# Finite-block adapter for logarithmic singleton paths

This file integrates the logarithmic rates of a continuous zero-perfect
singleton path over a fixed positive mesh.  The only asymptotic input is kept
in the separate `LogarithmicPathNeverCertificate`; all finite block identities
and bounds are derived from the path.
-/

noncomputable section

namespace GameTheory
namespace QuittingLCPClassification

open Filter Finset Set
open MeasureTheory QuittingAbsorptionPath
open scoped BigOperators Interval Topology

variable {ι : Type} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] [DecidableEq ι] in
private theorem quittingSoloReward_eq_quittingSingletonTerminal
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (owner who : ι) :
    quittingSoloReward reward owner who =
      reward (quittingSingletonTerminal owner) who := by
  rfl

/-- The left endpoint of a logarithmic mesh block. -/
def logarithmicBlockStart (h : ℝ) (time : ℕ) : ℝ :=
  (time : ℝ) * h

/-- The right endpoint of a logarithmic mesh block. -/
def logarithmicBlockEnd (h : ℝ) (time : ℕ) : ℝ :=
  (time + 1 : ℝ) * h

/-- Singleton absorption mass in one full logarithmic block, transported to
the beginning of that block. -/
def ContinuousZeroPerfectSingletonPath.logFullBlockMass
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (witness : ContinuousZeroPerfectSingletonPath reward)
    (h : ℝ) (time : ℕ) (owner : ι) : ℝ :=
  ∫ tau in logarithmicBlockStart h time..logarithmicBlockEnd h time,
    Real.exp (-(tau - logarithmicBlockStart h time)) *
      witness.logRate owner tau

/-- Singleton absorption mass in one logarithmic block after deleting
`who`, normalized by survival at the beginning of the block. -/
def ContinuousZeroPerfectSingletonPath.logOpponentBlockMass
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (witness : ContinuousZeroPerfectSingletonPath reward)
    (h : ℝ) (who : ι) (time : ℕ) (owner : ι) : ℝ :=
  if owner = who then 0 else
    ∫ tau in logarithmicBlockStart h time..logarithmicBlockEnd h time,
      (witness.deletedSurvival who tau /
          witness.deletedSurvival who (logarithmicBlockStart h time)) *
        witness.logRate owner tau

private theorem logarithmicBlockStart_nonneg {h : ℝ} (hh : 0 ≤ h) (time : ℕ) :
    0 ≤ logarithmicBlockStart h time := by
  exact mul_nonneg (Nat.cast_nonneg time) hh

private theorem logarithmicBlockStart_le_end {h : ℝ} (hh : 0 ≤ h) (time : ℕ) :
    logarithmicBlockStart h time ≤ logarithmicBlockEnd h time := by
  unfold logarithmicBlockStart logarithmicBlockEnd
  have htime : (0 : ℝ) ≤ time := Nat.cast_nonneg time
  nlinarith

private theorem logarithmicBlockEnd_sub_start (h : ℝ) (time : ℕ) :
    logarithmicBlockEnd h time - logarithmicBlockStart h time = h := by
  unfold logarithmicBlockStart logarithmicBlockEnd
  ring

theorem ContinuousZeroPerfectSingletonPath.logFullBlockMass_lower
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (witness : ContinuousZeroPerfectSingletonPath reward)
    {h : ℝ} (hh : 0 ≤ h) (time : ℕ) (owner : ι) :
    Real.exp (-h) * witness.logBlockHazard h time owner ≤
      witness.logFullBlockMass h time owner := by
  let first := logarithmicBlockStart h time
  let second := logarithmicBlockEnd h time
  have hfirst : 0 ≤ first := logarithmicBlockStart_nonneg hh time
  have hle : first ≤ second := logarithmicBlockStart_le_end hh time
  rw [ContinuousZeroPerfectSingletonPath.logFullBlockMass,
    ContinuousZeroPerfectSingletonPath.logBlockHazard,
    ← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_mono_on hle
  · exact (witness.logRate_intervalIntegrable owner hfirst hle).const_mul _
  · exact (witness.logRate_intervalIntegrable owner hfirst hle).continuousOn_mul
      (Real.continuous_exp.comp_continuousOn
        (continuousOn_id.sub (continuousOn_const :
          ContinuousOn (fun _ : ℝ => first) _)).neg)
  · intro tau htau
    have hdelta : tau - first ≤ h := by
      rw [← logarithmicBlockEnd_sub_start h time]
      linarith [htau.2]
    exact mul_le_mul_of_nonneg_right
      (Real.exp_le_exp.mpr (neg_le_neg hdelta))
      (witness.logRate_nonneg owner tau)

theorem ContinuousZeroPerfectSingletonPath.logFullBlockMass_upper
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (witness : ContinuousZeroPerfectSingletonPath reward)
    {h : ℝ} (hh : 0 ≤ h) (time : ℕ) (owner : ι) :
    witness.logFullBlockMass h time owner ≤
      witness.logBlockHazard h time owner := by
  let first := logarithmicBlockStart h time
  let second := logarithmicBlockEnd h time
  have hfirst : 0 ≤ first := logarithmicBlockStart_nonneg hh time
  have hle : first ≤ second := logarithmicBlockStart_le_end hh time
  rw [ContinuousZeroPerfectSingletonPath.logFullBlockMass,
    ContinuousZeroPerfectSingletonPath.logBlockHazard]
  apply intervalIntegral.integral_mono_on hle
  · exact (witness.logRate_intervalIntegrable owner hfirst hle).continuousOn_mul
      (Real.continuous_exp.comp_continuousOn
        (continuousOn_id.sub (continuousOn_const :
          ContinuousOn (fun _ : ℝ => first) _)).neg)
  · exact witness.logRate_intervalIntegrable owner hfirst hle
  · intro tau htau
    have hdelta : 0 ≤ tau - first := sub_nonneg.mpr htau.1
    simpa only [one_mul] using mul_le_mul_of_nonneg_right
      (Real.exp_le_one_iff.mpr (neg_nonpos.mpr hdelta))
      (witness.logRate_nonneg owner tau)

private theorem ContinuousZeroPerfectSingletonPath.logOpponentRatio_continuousOn
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (witness : ContinuousZeroPerfectSingletonPath reward)
    {h : ℝ} (hh : 0 ≤ h) (who : ι) (time : ℕ) :
    ContinuousOn (fun tau => witness.deletedSurvival who tau /
      witness.deletedSurvival who (logarithmicBlockStart h time))
      (Set.uIcc (logarithmicBlockStart h time) (logarithmicBlockEnd h time)) := by
  have hfirst := logarithmicBlockStart_nonneg hh time
  have hle := logarithmicBlockStart_le_end hh time
  have hAC := witness.deletedSurvival_absolutelyContinuousOnInterval who
    (hfirst.trans hle)
  exact (hAC.mono (by
    rw [uIcc_of_le hle, uIcc_of_le (hfirst.trans hle)]
    intro tau htau
    exact ⟨hfirst.trans htau.1, htau.2⟩)).continuousOn.div_const _

theorem ContinuousZeroPerfectSingletonPath.logOpponentBlockMass_self
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (witness : ContinuousZeroPerfectSingletonPath reward)
    (h : ℝ) (who : ι) (time : ℕ) :
    witness.logOpponentBlockMass h who time who = 0 := by
  simp [ContinuousZeroPerfectSingletonPath.logOpponentBlockMass]

theorem ContinuousZeroPerfectSingletonPath.logOpponentBlockMass_lower
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (witness : ContinuousZeroPerfectSingletonPath reward)
    {h : ℝ} (hh : 0 < h) (who : ι) (time : ℕ) (owner : ι)
    (hne : owner ≠ who) :
    Real.exp (-logarithmicOpponentBlockHazard
        (witness.logBlockHazard h) who time) *
        witness.logBlockHazard h time owner ≤
      witness.logOpponentBlockMass h who time owner := by
  let first := logarithmicBlockStart h time
  let second := logarithmicBlockEnd h time
  have hfirst : 0 ≤ first := logarithmicBlockStart_nonneg hh.le time
  have hle : first ≤ second := logarithmicBlockStart_le_end hh.le time
  have hincrement : witness.deletedHazard who second -
      witness.deletedHazard who first =
      logarithmicOpponentBlockHazard
        (witness.logBlockHazard h) who time := by
    exact witness.deletedHazard_blockIncrement who hh time
  rw [ContinuousZeroPerfectSingletonPath.logOpponentBlockMass, if_neg hne,
    ContinuousZeroPerfectSingletonPath.logBlockHazard,
    ← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_mono_on hle
  · exact (witness.logRate_intervalIntegrable owner hfirst hle).const_mul _
  · exact (witness.logRate_intervalIntegrable owner hfirst hle).continuousOn_mul
      (witness.logOpponentRatio_continuousOn hh.le who time)
  · intro tau htau
    have hratio := witness.deletedSurvival_ratio_bounds who hfirst
      htau.1 htau.2
    rw [hincrement] at hratio
    exact mul_le_mul_of_nonneg_right hratio.1
      (witness.logRate_nonneg owner tau)

theorem ContinuousZeroPerfectSingletonPath.logOpponentBlockMass_upper
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (witness : ContinuousZeroPerfectSingletonPath reward)
    {h : ℝ} (hh : 0 < h) (who : ι) (time : ℕ) (owner : ι)
    (hne : owner ≠ who) :
    witness.logOpponentBlockMass h who time owner ≤
      witness.logBlockHazard h time owner := by
  let first := logarithmicBlockStart h time
  let second := logarithmicBlockEnd h time
  have hfirst : 0 ≤ first := logarithmicBlockStart_nonneg hh.le time
  have hle : first ≤ second := logarithmicBlockStart_le_end hh.le time
  rw [ContinuousZeroPerfectSingletonPath.logOpponentBlockMass, if_neg hne,
    ContinuousZeroPerfectSingletonPath.logBlockHazard]
  apply intervalIntegral.integral_mono_on hle
  · exact (witness.logRate_intervalIntegrable owner hfirst hle).continuousOn_mul
      (witness.logOpponentRatio_continuousOn hh.le who time)
  · exact witness.logRate_intervalIntegrable owner hfirst hle
  · intro tau htau
    have hratio := witness.deletedSurvival_ratio_bounds who hfirst
      htau.1 htau.2
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hratio.2
      (witness.logRate_nonneg owner tau)

/-- The full block mass is the exact increment of the cumulative singleton
mass, transported to the left block endpoint. -/
theorem ContinuousZeroPerfectSingletonPath.logFullBlockMass_eq
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (witness : ContinuousZeroPerfectSingletonPath reward)
    {h : ℝ} (hh : 0 ≤ h) (time : ℕ) (owner : ι) :
    witness.logFullBlockMass h time owner =
      Real.exp (logarithmicBlockStart h time) *
        (witness.logMass owner (logarithmicBlockEnd h time) -
          witness.logMass owner (logarithmicBlockStart h time)) := by
  let first := logarithmicBlockStart h time
  let second := logarithmicBlockEnd h time
  have hfirst : 0 ≤ first := logarithmicBlockStart_nonneg hh time
  have hle : first ≤ second := logarithmicBlockStart_le_end hh time
  have hAC := (witness.logMass_absolutelyContinuousOnInterval owner
    (hfirst.trans hle)).mono (by
      rw [uIcc_of_le hle, uIcc_of_le (hfirst.trans hle)]
      intro tau htau
      exact ⟨hfirst.trans htau.1, htau.2⟩)
  rw [ContinuousZeroPerfectSingletonPath.logFullBlockMass]
  calc
    (∫ tau in first..second,
        Real.exp (-(tau - first)) * witness.logRate owner tau) =
        ∫ tau in first..second,
          Real.exp first * deriv (witness.logMass owner) tau := by
      apply intervalIntegral.integral_congr
      intro tau _
      unfold ContinuousZeroPerfectSingletonPath.logRate
      change Real.exp (-(tau - first)) *
          (Real.exp tau * deriv (witness.logMass owner) tau) =
        Real.exp first * deriv (witness.logMass owner) tau
      rw [← mul_assoc, ← Real.exp_add]
      rw [show -(tau - first) + tau = first by ring]
    _ = Real.exp first *
        (witness.logMass owner second - witness.logMass owner first) := by
      rw [intervalIntegral.integral_const_mul, hAC.integral_deriv_eq_sub]

theorem ContinuousZeroPerfectSingletonPath.logPayoff_blockBellman
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (witness : ContinuousZeroPerfectSingletonPath reward)
    {h : ℝ} (hh : 0 ≤ h) (time : ℕ) (who : ι) :
    witness.logPayoff reward (logarithmicBlockStart h time) who =
      (∑ owner, witness.logFullBlockMass h time owner *
        quittingSoloReward reward owner who) +
      Real.exp (-h) *
        witness.logPayoff reward (logarithmicBlockEnd h time) who := by
  simp_rw [witness.logFullBlockMass_eq hh]
  unfold ContinuousZeroPerfectSingletonPath.logPayoff
  have hexp : Real.exp (-h) *
      Real.exp (logarithmicBlockEnd h time) =
      Real.exp (logarithmicBlockStart h time) := by
    rw [← Real.exp_add]
    congr 1
    nlinarith [logarithmicBlockEnd_sub_start h time]
  rw [← mul_assoc, hexp, Finset.mul_sum, Finset.mul_sum]
  simp_rw [mul_assoc]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro owner _
  ring

theorem ContinuousZeroPerfectSingletonPath.terminal_sub_logMass_nonneg
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (witness : ContinuousZeroPerfectSingletonPath reward)
    (owner : ι) {tau : ℝ} (htau : 0 ≤ tau) :
    0 ≤ witness.terminal owner - witness.logMass owner tau := by
  rw [sub_nonneg, witness.logMass_eq_mass owner htau]
  rw [← congrFun witness.mass.target owner]
  exact witness.monotone owner (logarithmicPathClock_mem_Ico htau).2.le

theorem ContinuousZeroPerfectSingletonPath.sum_terminal_sub_logMass
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (witness : ContinuousZeroPerfectSingletonPath reward)
    {tau : ℝ} (htau : 0 ≤ tau) :
    ∑ owner, (witness.terminal owner - witness.logMass owner tau) =
      Real.exp (-tau) := by
  rw [Finset.sum_sub_distrib, witness.sum_logMass htau]
  have hterminal : ∑ owner, witness.terminal owner = 1 := by
    calc
      ∑ owner, witness.terminal owner =
          ∑ owner, witness.mass 1 owner := by
        simp_rw [congrFun witness.mass.target]
      _ = 1 := witness.total 1
  rw [hterminal, logarithmicPathClock]
  ring

theorem ContinuousZeroPerfectSingletonPath.logPayoff_bound
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (witness : ContinuousZeroPerfectSingletonPath reward)
    {M tau : ℝ} (htau : 0 ≤ tau)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (who : ι) :
    |witness.logPayoff reward tau who| ≤ M := by
  unfold ContinuousZeroPerfectSingletonPath.logPayoff
  rw [abs_mul]
  have hexpNonneg : 0 ≤ Real.exp tau := Real.exp_nonneg tau
  have hsum : |∑ owner,
      (witness.terminal owner - witness.logMass owner tau) *
        quittingSoloReward reward owner who| ≤
      ∑ owner, (witness.terminal owner - witness.logMass owner tau) * M := by
    calc
      |∑ owner, (witness.terminal owner - witness.logMass owner tau) *
          quittingSoloReward reward owner who| ≤
          ∑ owner, |(witness.terminal owner - witness.logMass owner tau) *
            quittingSoloReward reward owner who| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ owner,
          (witness.terminal owner - witness.logMass owner tau) * M := by
        apply Finset.sum_le_sum
        intro owner _
        rw [abs_mul, abs_of_nonneg
          (witness.terminal_sub_logMass_nonneg owner htau)]
        exact mul_le_mul_of_nonneg_left
          (hreward (quittingSingletonTerminal owner) who)
          (witness.terminal_sub_logMass_nonneg owner htau)
  rw [abs_of_nonneg hexpNonneg]
  calc
    Real.exp tau * |∑ owner,
        (witness.terminal owner - witness.logMass owner tau) *
          quittingSoloReward reward owner who| ≤
        Real.exp tau * ∑ owner,
          (witness.terminal owner - witness.logMass owner tau) * M :=
      mul_le_mul_of_nonneg_left hsum hexpNonneg
    _ = M := by
      rw [← Finset.sum_mul,
        witness.sum_terminal_sub_logMass htau, ← mul_assoc,
        ← Real.exp_add]
      simp

/-- Integrated opponent block hazards telescope to the continuum deleted
hazard at the sampled endpoint. -/
theorem ContinuousZeroPerfectSingletonPath.sum_opponentBlockHazard_eq
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (witness : ContinuousZeroPerfectSingletonPath reward)
    {h : ℝ} (hh : 0 < h) (who : ι) (fuel : ℕ) :
    ∑ time ∈ Finset.range fuel,
        logarithmicOpponentBlockHazard
          (witness.logBlockHazard h) who time =
      witness.deletedHazard who ((fuel : ℝ) * h) := by
  induction fuel with
  | zero => simp [ContinuousZeroPerfectSingletonPath.deletedHazard]
  | succ fuel ih =>
      rw [Finset.sum_range_succ, ih]
      have hincrement := witness.deletedHazard_blockIncrement who hh fuel
      change witness.deletedHazard who ((fuel : ℝ) * h) +
          logarithmicOpponentBlockHazard
            (witness.logBlockHazard h) who fuel =
        witness.deletedHazard who (((fuel + 1 : ℕ) : ℝ) * h)
      rw [Nat.cast_add, Nat.cast_one]
      unfold logarithmicOpponentBlockHazard
      linarith

theorem ContinuousZeroPerfectSingletonPath.logarithmicDeletedSurvival_eq
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (witness : ContinuousZeroPerfectSingletonPath reward)
    {h : ℝ} (hh : 0 < h) (who : ι) (fuel : ℕ) :
    logarithmicDeletedSurvival
        (logarithmicOpponentBlockHazard (witness.logBlockHazard h) who) fuel =
      witness.deletedSurvival who ((fuel : ℝ) * h) := by
  rw [logarithmicDeletedSurvival,
    witness.sum_opponentBlockHazard_eq hh who fuel]
  rfl

private theorem ContinuousZeroPerfectSingletonPath.deletedOpponentPayoffRate_eq_sum_erase
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (witness : ContinuousZeroPerfectSingletonPath reward)
    (who : ι) (tau : ℝ) :
    witness.deletedOpponentPayoffRate reward who tau =
      ∑ owner ∈ Finset.univ.erase who,
        witness.logRate owner tau * quittingSoloReward reward owner who := by
  unfold ContinuousZeroPerfectSingletonPath.deletedOpponentPayoffRate
  rw [← Finset.sum_erase_add Finset.univ
    (fun owner => witness.logRate owner tau *
      quittingSoloReward reward owner who) (Finset.mem_univ who)]
  ring

/-- Summing normalized opponent masses against solo rewards gives exactly
the normalized continuum opponent flow over that block. -/
theorem ContinuousZeroPerfectSingletonPath.sum_logOpponentBlockMass_mul_reward
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (witness : ContinuousZeroPerfectSingletonPath reward)
    {h : ℝ} (hh : 0 < h) (who : ι) (time : ℕ) :
    ∑ owner, witness.logOpponentBlockMass h who time owner *
        quittingSoloReward reward owner who =
      ∫ tau in logarithmicBlockStart h time..logarithmicBlockEnd h time,
        (witness.deletedSurvival who tau /
            witness.deletedSurvival who (logarithmicBlockStart h time)) *
          witness.deletedOpponentPayoffRate reward who tau := by
  let first := logarithmicBlockStart h time
  let second := logarithmicBlockEnd h time
  have hfirst : 0 ≤ first := logarithmicBlockStart_nonneg hh.le time
  have hle : first ≤ second := logarithmicBlockStart_le_end hh.le time
  rw [show witness.deletedOpponentPayoffRate reward who =
      fun tau => ∑ owner ∈ Finset.univ.erase who,
        witness.logRate owner tau * quittingSoloReward reward owner who by
    funext tau
    exact witness.deletedOpponentPayoffRate_eq_sum_erase reward who tau]
  rw [show (∫ tau in first..second,
      (witness.deletedSurvival who tau /
          witness.deletedSurvival who first) *
        ∑ owner ∈ Finset.univ.erase who,
          witness.logRate owner tau * quittingSoloReward reward owner who) =
      ∑ owner ∈ Finset.univ.erase who,
        ∫ tau in first..second,
          (witness.deletedSurvival who tau /
              witness.deletedSurvival who first) *
            (witness.logRate owner tau *
              quittingSoloReward reward owner who) by
    rw [← intervalIntegral.integral_finsetSum]
    · apply intervalIntegral.integral_congr
      intro tau _
      change (witness.deletedSurvival who tau /
          witness.deletedSurvival who first) *
          (∑ owner ∈ Finset.univ.erase who,
            witness.logRate owner tau * quittingSoloReward reward owner who) = _
      rw [Finset.mul_sum]
    · intro owner _
      simpa only [mul_assoc] using
        ((witness.logRate_intervalIntegrable owner hfirst hle).continuousOn_mul
          (witness.logOpponentRatio_continuousOn hh.le who time)).mul_const
            (quittingSoloReward reward owner who)]
  rw [← Finset.sum_erase_add Finset.univ
    (fun owner => witness.logOpponentBlockMass h who time owner *
      quittingSoloReward reward owner who) (Finset.mem_univ who),
    witness.logOpponentBlockMass_self, zero_mul, add_zero]
  apply Finset.sum_congr rfl
  intro owner howner
  have hne : owner ≠ who := Finset.ne_of_mem_erase howner
  rw [ContinuousZeroPerfectSingletonPath.logOpponentBlockMass, if_neg hne,
    ← intervalIntegral.integral_mul_const]
  apply intervalIntegral.integral_congr
  intro tau _
  ring

private theorem ContinuousZeroPerfectSingletonPath.deletedOpponentPayoffRate_intervalIntegrable
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (witness : ContinuousZeroPerfectSingletonPath reward)
    (who : ι) {first second : ℝ} (hfirst : 0 ≤ first)
    (hle : first ≤ second) :
    IntervalIntegrable (witness.deletedOpponentPayoffRate reward who)
      volume first second := by
  rw [show witness.deletedOpponentPayoffRate reward who =
      fun tau => ∑ owner ∈ Finset.univ.erase who,
        witness.logRate owner tau * quittingSoloReward reward owner who by
    funext tau
    exact witness.deletedOpponentPayoffRate_eq_sum_erase reward who tau]
  have hfun : (fun tau => ∑ owner ∈ Finset.univ.erase who,
      witness.logRate owner tau * quittingSoloReward reward owner who) =
      ∑ owner ∈ Finset.univ.erase who,
        fun tau => witness.logRate owner tau *
          quittingSoloReward reward owner who := by
    funext tau
    simp
  rw [hfun]
  exact IntervalIntegrable.sum (Finset.univ.erase who) fun owner _ =>
    (witness.logRate_intervalIntegrable owner hfirst hle).mul_const _

private theorem ContinuousZeroPerfectSingletonPath.deletedOpponentFlow_intervalIntegrable
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (witness : ContinuousZeroPerfectSingletonPath reward)
    (who : ι) {first second : ℝ} (hfirst : 0 ≤ first)
    (hle : first ≤ second) :
    IntervalIntegrable (fun tau => witness.deletedSurvival who tau *
      witness.deletedOpponentPayoffRate reward who tau) volume first second := by
  have hAC := (witness.deletedSurvival_absolutelyContinuousOnInterval who
    (hfirst.trans hle)).mono (by
      rw [uIcc_of_le hle, uIcc_of_le (hfirst.trans hle)]
      intro tau htau
      exact ⟨hfirst.trans htau.1, htau.2⟩)
  exact (witness.deletedOpponentPayoffRate_intervalIntegrable reward who hfirst hle)
    |>.continuousOn_mul hAC.continuousOn

private theorem ContinuousZeroPerfectSingletonPath.deletedBlockLedgerTerm_eq_integral
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (witness : ContinuousZeroPerfectSingletonPath reward)
    {h : ℝ} (hh : 0 < h) (who : ι) (time : ℕ) :
    logarithmicDeletedSurvival
        (logarithmicOpponentBlockHazard (witness.logBlockHazard h) who) time *
      (∑ owner, witness.logOpponentBlockMass h who time owner *
        reward (quittingSingletonTerminal owner) who) =
      ∫ tau in logarithmicBlockStart h time..logarithmicBlockEnd h time,
        witness.deletedSurvival who tau *
          witness.deletedOpponentPayoffRate reward who tau := by
  rw [witness.logarithmicDeletedSurvival_eq hh who time]
  change witness.deletedSurvival who (logarithmicBlockStart h time) *
      (∑ owner, witness.logOpponentBlockMass h who time owner *
        quittingSoloReward reward owner who) = _
  rw [witness.sum_logOpponentBlockMass_mul_reward reward hh who time,
    ← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro tau _
  have hne : witness.deletedSurvival who
      (logarithmicBlockStart h time) ≠ 0 := Real.exp_ne_zero _
  field_simp

/-- The discrete source ledger obtained from the normalized block masses is
exactly the continuum deleted-clock integral through the sampled endpoint. -/
theorem ContinuousZeroPerfectSingletonPath.logarithmicSourceOpponentLedger_eq
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (witness : ContinuousZeroPerfectSingletonPath reward)
    {h : ℝ} (hh : 0 < h) (who : ι) (fuel : ℕ) :
    logarithmicSourceOpponentLedger reward (witness.logBlockHazard h)
        (witness.logOpponentBlockMass h) who fuel =
      ∫ tau in 0..(fuel : ℝ) * h,
        witness.deletedSurvival who tau *
          witness.deletedOpponentPayoffRate reward who tau := by
  induction fuel with
  | zero => simp [logarithmicSourceOpponentLedger]
  | succ fuel ih =>
      unfold logarithmicSourceOpponentLedger
      rw [Finset.sum_range_succ]
      change logarithmicSourceOpponentLedger reward (witness.logBlockHazard h)
          (witness.logOpponentBlockMass h) who fuel + _ = _
      rw [ih, witness.deletedBlockLedgerTerm_eq_integral reward hh who fuel]
      simp only [logarithmicBlockStart, logarithmicBlockEnd,
        Nat.cast_add, Nat.cast_one]
      rw [intervalIntegral.integral_add_adjacent_intervals]
      · exact witness.deletedOpponentFlow_intervalIntegrable reward who
          le_rfl (logarithmicBlockStart_nonneg hh.le fuel)
      · exact witness.deletedOpponentFlow_intervalIntegrable reward who
          (logarithmicBlockStart_nonneg hh.le fuel)
          (logarithmicBlockStart_le_end hh.le fuel)

theorem ContinuousZeroPerfectSingletonPath.logarithmicFiniteQuit_cap
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (witness : ContinuousZeroPerfectSingletonPath reward)
    {h : ℝ} (hh : 0 < h) (who : ι) (fuel : ℕ) :
    logarithmicSourceOpponentLedger reward (witness.logBlockHazard h)
          (witness.logOpponentBlockMass h) who fuel +
        logarithmicDeletedSurvival
            (logarithmicOpponentBlockHazard
              (witness.logBlockHazard h) who) fuel *
          quittingSoloReward reward who who ≤
      witness.logPayoff reward 0 who := by
  rw [witness.logarithmicSourceOpponentLedger_eq reward hh who fuel,
    witness.logarithmicDeletedSurvival_eq hh who fuel]
  exact witness.deletedFiniteQuit_cap reward who
    (mul_nonneg (Nat.cast_nonneg fuel) hh.le)

/-- The mesh-independent asymptotic datum not implied by the finite Snell
identity.  It says that the continuum opponent ledger has a finite limiting
value and that this Never value is capped by the initial continuation value. -/
structure LogarithmicPathNeverCertificate
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (witness : ContinuousZeroPerfectSingletonPath reward) where
  neverValue : Payoff ι
  tendsto_deletedOpponentIntegral : ∀ who,
    Tendsto (fun T => ∫ tau in 0..T,
      witness.deletedSurvival who tau *
        witness.deletedOpponentPayoffRate reward who tau)
      atTop (nhds (neverValue who))
  neverValue_le : ∀ who,
    neverValue who ≤ witness.logPayoff reward 0 who

/-- Vanishing deleted survival for every owner supplies the exact Never
certificate, with Never payoff equal to the initial continuation payoff. -/
def LogarithmicPathNeverCertificate.of_all_tendsto_deletedSurvival_zero
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (witness : ContinuousZeroPerfectSingletonPath reward)
    (hzero : ∀ who, Tendsto (witness.deletedSurvival who) atTop (nhds 0)) :
    LogarithmicPathNeverCertificate reward witness where
  neverValue := witness.logPayoff reward 0
  tendsto_deletedOpponentIntegral := by
    intro who
    have ht := witness.tendsto_deletedOpponentLedger_of_zero_survival
      reward who (hzero who)
    unfold ContinuousZeroPerfectSingletonPath.deletedOpponentLedger at ht
    exact ht
  neverValue_le := fun _ => le_rfl

private theorem ContinuousZeroPerfectSingletonPath.index_nonempty
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (witness : ContinuousZeroPerfectSingletonPath reward) :
    Nonempty ι := by
  by_contra hempty
  letI : IsEmpty ι := not_nonempty_iff.mp hempty
  have htotal := witness.total 1
  simp at htotal

/-- Every positive mesh of a singleton path, together with only the separate
Never/transversality datum, supplies the complete decoder certificate. -/
def ContinuousZeroPerfectSingletonPath.logarithmicRateSnellCertificate
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (witness : ContinuousZeroPerfectSingletonPath reward)
    (never : LogarithmicPathNeverCertificate reward witness)
    (M h : ℝ) (hh : 0 < h)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M) :
    LogarithmicRateSnellCertificate reward M h := by
  letI : Nonempty ι := witness.index_nonempty
  have hM := quittingRewardCoordinateBound_nonneg_of_nonempty reward hreward
  exact {
  h_pos := hh
  M_nonneg := hM
  reward_bound := hreward
  A := witness.logBlockHazard h
  A_nonneg := witness.logBlockHazard_nonneg hh.le
  A_sum := witness.sum_logBlockHazard hh
  fullMass := witness.logFullBlockMass h
  fullMass_lower := witness.logFullBlockMass_lower hh.le
  fullMass_upper := witness.logFullBlockMass_upper hh.le
  value := fun time who =>
    witness.logPayoff reward (logarithmicBlockStart h time) who
  value_bound := fun time who => witness.logPayoff_bound reward
    (logarithmicBlockStart_nonneg hh.le time) hreward who
  value_bellman := by
    intro time who
    simpa only [logarithmicBlockStart, logarithmicBlockEnd,
      Nat.cast_add, Nat.cast_one,
      quittingSoloReward_eq_quittingSingletonTerminal] using
        witness.logPayoff_blockBellman reward hh.le time who
  opponentMass := witness.logOpponentBlockMass h
  opponentMass_self := witness.logOpponentBlockMass_self h
  opponentMass_lower := witness.logOpponentBlockMass_lower hh
  opponentMass_upper := witness.logOpponentBlockMass_upper hh
  finiteQuit_cap := by
    intro who time
    simpa only [logarithmicBlockStart, Nat.cast_zero, zero_mul,
      quittingSoloReward_eq_quittingSingletonTerminal] using
        witness.logarithmicFiniteQuit_cap reward hh who time
  neverValue := never.neverValue
  tendsto_opponentLedger := by
    intro who
    have hmesh : Tendsto (fun fuel : ℕ => (fuel : ℝ) * h) atTop atTop :=
      tendsto_natCast_atTop_atTop.atTop_mul_const hh
    have htendsto := (never.tendsto_deletedOpponentIntegral who).comp hmesh
    apply htendsto.congr'
    filter_upwards [] with fuel
    exact witness.logarithmicSourceOpponentLedger_eq reward hh who fuel |>.symm
  neverValue_le := by
    intro who
    simpa only [logarithmicBlockStart, Nat.cast_zero, zero_mul] using
      never.neverValue_le who
  }

@[simp] theorem ContinuousZeroPerfectSingletonPath.logarithmicRateSnellCertificate_value
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (witness : ContinuousZeroPerfectSingletonPath reward)
    (never : LogarithmicPathNeverCertificate reward witness)
    (M h : ℝ) (hh : 0 < h)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (time : ℕ) (who : ι) :
    (witness.logarithmicRateSnellCertificate reward never M h hh hreward).value
        time who =
      witness.logPayoff reward (logarithmicBlockStart h time) who :=
  rfl

@[simp] theorem ContinuousZeroPerfectSingletonPath.logarithmicRateSnellCertificate_value_zero
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (witness : ContinuousZeroPerfectSingletonPath reward)
    (never : LogarithmicPathNeverCertificate reward witness)
    (M h : ℝ) (hh : 0 < h)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M) :
    (witness.logarithmicRateSnellCertificate reward never M h hh hreward).value
        0 = witness.logPayoff reward 0 := by
  funext who
  simp only [ContinuousZeroPerfectSingletonPath.logarithmicRateSnellCertificate_value,
    logarithmicBlockStart, Nat.cast_zero, zero_mul]

/-- Cofinal decoder data for the fixed initial payoff of a path. -/
theorem ContinuousZeroPerfectSingletonPath.logarithmicRateSnellFamilyCertificate
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (witness : ContinuousZeroPerfectSingletonPath reward)
    (never : LogarithmicPathNeverCertificate reward witness)
    (M : ℝ)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M) :
    LogarithmicRateSnellFamilyCertificate reward
      (witness.logPayoff reward 0) M := by
  letI : Nonempty ι := witness.index_nonempty
  have hM := quittingRewardCoordinateBound_nonneg_of_nonempty reward hreward
  exact {
  cofinal := by
    intro error herror
    let C := M * (4 + Real.exp 1) + 1
    have hC : 0 < C := by
      dsimp only [C]
      have hnonneg : 0 ≤ M * (4 + Real.exp 1) :=
        mul_nonneg hM (add_nonneg (by norm_num) (Real.exp_nonneg 1))
      linarith
    let h := min 1 (error / (2 * C))
    have hh : 0 < h := by
      dsimp only [h]
      exact lt_min one_pos (div_pos herror (mul_pos (by norm_num) hC))
    let data := witness.logarithmicRateSnellCertificate
      reward never M h hh hreward
    refine ⟨h, data, ?_, ?_⟩
    · have hh1 : h ≤ 1 := min_le_left _ _
      have hexp : Real.exp h ≤ Real.exp 1 := Real.exp_le_exp.mpr hh1
      have hcoefficient : M * (4 + Real.exp h) ≤ C := by
        dsimp only [C]
        have hscaled := mul_le_mul_of_nonneg_left
          (add_le_add_left hexp 4) hM
        linarith
      have hlinear := data.decoderError_le_linear
      have hscaled : M * h * (4 + Real.exp h) ≤ h * C := by
        calc
          M * h * (4 + Real.exp h) = h * (M * (4 + Real.exp h)) := by ring
          _ ≤ h * C := mul_le_mul_of_nonneg_left hcoefficient hh.le
      have hratio : h ≤ error / (2 * C) := min_le_right _ _
      have hbudget : h * (2 * C) ≤ error :=
        (le_div_iff₀ (mul_pos (by norm_num) hC)).mp hratio
      have hstrict : h * C < error := by nlinarith [mul_pos hh hC]
      exact hlinear.trans_lt (hscaled.trans_lt hstrict)
    · exact witness.logarithmicRateSnellCertificate_value_zero
        reward never M h hh hreward
  }

/-- On an ambient punishment-normal embedding, the sampled target is exactly
the fixed strategic path target. -/
theorem ContinuousZeroPerfectSingletonPath.ambientLogarithmicRateSnellFamilyCertificate
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (witness : ContinuousZeroPerfectSingletonPath
      (quittingPunishmentNormalReward reward))
    (never : LogarithmicPathNeverCertificate reward
      witness.ambientSingletonWitness) :
    LogarithmicRateSnellFamilyCertificate reward
      (punishmentNormalPathTarget reward witness) (quittingRewardBound reward) where
  cofinal := by
    intro error herror
    obtain ⟨h, data, hsmall, htarget⟩ :=
      (witness.ambientSingletonWitness.logarithmicRateSnellFamilyCertificate
        reward never (quittingRewardBound reward)
        (fun terminal player =>
          abs_reward_le_quittingRewardBound reward terminal player)).cofinal
          error herror
    refine ⟨h, data, hsmall, htarget.trans ?_⟩
    funext who
    exact witness.ambient_logPayoff_zero who

/-- The all-zero-limit branch yields the fixed-target pure-time certificate
consumed by the unrestricted behavioral semantics. -/
theorem ContinuousZeroPerfectSingletonPath.ambientLogarithmicPureTimeTargetCertificate
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (witness : ContinuousZeroPerfectSingletonPath
      (quittingPunishmentNormalReward reward))
    (never : LogarithmicPathNeverCertificate reward
      witness.ambientSingletonWitness) :
    QuittingPureTimeTargetApproximationCertificate reward
      (punishmentNormalPathTarget reward witness) :=
  (witness.ambientLogarithmicRateSnellFamilyCertificate reward never)
    |>.toPureTimeTargetCertificate

/-- Direct zero-limit source form of the right strategic disjunct. -/
theorem ContinuousZeroPerfectSingletonPath.ambientLogarithmicPureTimeTargetCertificate_of_zero
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (witness : ContinuousZeroPerfectSingletonPath
      (quittingPunishmentNormalReward reward))
    (hzero : ∀ who, Tendsto
      (witness.ambientSingletonWitness.deletedSurvival who)
      atTop (nhds 0)) :
    QuittingPureTimeTargetApproximationCertificate reward
      (punishmentNormalPathTarget reward witness) :=
  witness.ambientLogarithmicPureTimeTargetCertificate reward
    (LogarithmicPathNeverCertificate.of_all_tendsto_deletedSurvival_zero
      reward witness.ambientSingletonWitness hzero)


end QuittingLCPClassification
end GameTheory
