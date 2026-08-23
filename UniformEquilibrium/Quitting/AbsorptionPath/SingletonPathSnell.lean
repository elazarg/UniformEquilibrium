/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import UniformEquilibrium.Quitting.AbsorptionPath.SingletonPathRates

/-!
# Logarithmic rates and the singleton-path Snell identity

This file supplies the finite-interval analytic core of the direct decoder for
continuous zero-perfect singleton absorption paths.  It reparametrizes the
unit absorption clock by `t = 1 - exp (-tau)`, proves absolute continuity of
the resulting mass and payoff coordinates, and records their almost-everywhere
Bellman derivatives.  The deleted-clock product identity is then an ordinary
fundamental-theorem-of-calculus consequence.
-/

noncomputable section

namespace GameTheory
namespace QuittingLCPClassification

open Filter Finset Set unitInterval
open MeasureTheory QuittingAbsorptionPath
open scoped Interval Topology unitInterval

variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem absolutelyContinuousOnInterval_finset_sum
    {κ : Type} (owners : Finset κ) (f : κ → ℝ → ℝ)
    {first second : ℝ}
    (hf : ∀ owner ∈ owners,
      AbsolutelyContinuousOnInterval (f owner) first second) :
    AbsolutelyContinuousOnInterval (∑ owner ∈ owners, f owner) first second := by
  apply Finset.sum_induction f
    (fun g => AbsolutelyContinuousOnInterval g first second)
  · intro firstFun secondFun hfirst hsecond
    exact hfirst.add hsecond
  · exact (LipschitzWith.const (α := ℝ) (0 : ℝ)).lipschitzOnWith
      |>.absolutelyContinuousOnInterval
  · exact hf

/-- Postcomposition by a Lipschitz map preserves absolute continuity when
the Lipschitz estimate is available on the image of the interval. -/
theorem LipschitzOnWith.comp_absolutelyContinuousOnInterval
    {X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y]
    {K : NNReal} {outer : X → Y} {inner : ℝ → X} {first second : ℝ}
    (houter : LipschitzOnWith K outer (inner '' Set.uIcc first second))
    (hinner : AbsolutelyContinuousOnInterval inner first second) :
    AbsolutelyContinuousOnInterval (outer ∘ inner) first second := by
  rw [absolutelyContinuousOnInterval_iff] at hinner ⊢
  intro epsilon hepsilon
  have houterDist := lipschitzOnWith_iff_dist_le_mul.mp houter
  by_cases hK : K = 0
  · refine ⟨1, by norm_num, fun E hE _ => ?_⟩
    have hzero (index : ℕ) (hindex : index ∈ Finset.range E.1) :
        dist (outer (inner (E.2 index).1))
          (outer (inner (E.2 index).2)) = 0 := by
      have hle := houterDist
        (inner (E.2 index).1)
        ⟨(E.2 index).1, (hE.1 index hindex).1, rfl⟩
        (inner (E.2 index).2)
        ⟨(E.2 index).2, (hE.1 index hindex).2, rfl⟩
      rw [hK] at hle
      have hle0 : dist (outer (inner (E.2 index).1))
          (outer (inner (E.2 index).2)) ≤ 0 := by
        simpa only [NNReal.coe_zero, zero_mul] using hle
      exact le_antisymm hle0 dist_nonneg
    have hsum : (∑ index ∈ Finset.range E.1,
        dist ((outer ∘ inner) (E.2 index).1)
          ((outer ∘ inner) (E.2 index).2)) = 0 := by
      apply Finset.sum_eq_zero
      intro index hindex
      exact hzero index hindex
    rw [hsum]
    exact hepsilon
  · have hKpos : 0 < (K : ℝ) := (NNReal.coe_pos.mpr (pos_of_ne_zero hK))
    obtain ⟨delta, hdelta, hcontrol⟩ :=
      hinner (epsilon / (K : ℝ)) (div_pos hepsilon hKpos)
    refine ⟨delta, hdelta, fun E hE hlength => ?_⟩
    have hinnerSum := hcontrol E hE hlength
    have hterm (index : ℕ) (hindex : index ∈ Finset.range E.1) :
        dist (outer (inner (E.2 index).1))
            (outer (inner (E.2 index).2)) ≤
          (K : ℝ) * dist (inner (E.2 index).1) (inner (E.2 index).2) := by
      exact houterDist
        (inner (E.2 index).1)
        ⟨(E.2 index).1, (hE.1 index hindex).1, rfl⟩
        (inner (E.2 index).2)
        ⟨(E.2 index).2, (hE.1 index hindex).2, rfl⟩
    calc
      ∑ index ∈ Finset.range E.1,
          dist ((outer ∘ inner) (E.2 index).1)
            ((outer ∘ inner) (E.2 index).2) ≤
          ∑ index ∈ Finset.range E.1,
            (K : ℝ) * dist (inner (E.2 index).1)
              (inner (E.2 index).2) :=
        Finset.sum_le_sum fun index hindex => hterm index hindex
      _ = (K : ℝ) * ∑ index ∈ Finset.range E.1,
          dist (inner (E.2 index).1) (inner (E.2 index).2) := by
        rw [Finset.mul_sum]
      _ < (K : ℝ) * (epsilon / (K : ℝ)) := by gcongr
      _ = epsilon := by field_simp

/-- The unit absorption clock written in logarithmic time. -/
def logarithmicPathClock (tau : ℝ) : ℝ :=
  1 - Real.exp (-tau)

theorem logarithmicPathClock_mem_Ico {tau : ℝ} (htau : 0 ≤ tau) :
    logarithmicPathClock tau ∈ Set.Ico (0 : ℝ) 1 := by
  constructor
  · rw [logarithmicPathClock, sub_nonneg, Real.exp_le_one_iff]
    linarith
  · rw [logarithmicPathClock]
    linarith [Real.exp_pos (-tau)]

theorem logarithmicPathClock_monotone : Monotone logarithmicPathClock := by
  intro first second hle
  rw [logarithmicPathClock, logarithmicPathClock]
  exact sub_le_sub_left (Real.exp_le_exp.mpr (neg_le_neg hle)) 1

/-- A singleton cumulative-mass coordinate in logarithmic time. -/
def ContinuousZeroPerfectSingletonPath.logMass
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (witness : ContinuousZeroPerfectSingletonPath reward)
    (who : ι) (tau : ℝ) : ℝ :=
  witness.mass.extend (logarithmicPathClock tau) who

theorem ContinuousZeroPerfectSingletonPath.logMass_monotone
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (witness : ContinuousZeroPerfectSingletonPath reward) (who : ι) :
    Monotone (witness.logMass who) :=
  (witness.monotone_mass_extend who).comp logarithmicPathClock_monotone

theorem ContinuousZeroPerfectSingletonPath.logMass_eq_mass
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (witness : ContinuousZeroPerfectSingletonPath reward)
    (who : ι) {tau : ℝ} (htau : 0 ≤ tau) :
    witness.logMass who tau =
      witness.mass ⟨logarithmicPathClock tau,
        (logarithmicPathClock_mem_Ico htau).1,
        (logarithmicPathClock_mem_Ico htau).2.le⟩ who := by
  exact congrFun (Path.extend_apply witness.mass
    ⟨(logarithmicPathClock_mem_Ico htau).1,
      (logarithmicPathClock_mem_Ico htau).2.le⟩) who

theorem ContinuousZeroPerfectSingletonPath.sum_logMass
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (witness : ContinuousZeroPerfectSingletonPath reward)
    {tau : ℝ} (htau : 0 ≤ tau) :
    ∑ who, witness.logMass who tau = logarithmicPathClock tau := by
  simp_rw [witness.logMass_eq_mass _ htau]
  exact witness.total _

/-- The conditional singleton hazard in logarithmic time.  The exponential
factor divides cumulative absorption density by current survival. -/
def ContinuousZeroPerfectSingletonPath.logRate
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (witness : ContinuousZeroPerfectSingletonPath reward)
    (who : ι) (tau : ℝ) : ℝ :=
  Real.exp tau * deriv (witness.logMass who) tau

theorem ContinuousZeroPerfectSingletonPath.logRate_nonneg
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (witness : ContinuousZeroPerfectSingletonPath reward)
    (who : ι) (tau : ℝ) :
    0 ≤ witness.logRate who tau := by
  exact mul_nonneg (Real.exp_nonneg tau)
    (witness.logMass_monotone who).deriv_nonneg

theorem ContinuousZeroPerfectSingletonPath.measurable_logRate
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (witness : ContinuousZeroPerfectSingletonPath reward) (who : ι) :
    Measurable (witness.logRate who) := by
  exact Real.measurable_exp.mul (measurable_deriv _)

theorem ContinuousZeroPerfectSingletonPath.lipschitzOnWith_mass_extend_apply
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (witness : ContinuousZeroPerfectSingletonPath reward) (who : ι) :
    LipschitzOnWith 1 (fun time => witness.mass.extend time who)
      (Set.Icc (0 : ℝ) 1) := by
  rw [lipschitzOnWith_iff_dist_le_mul]
  intro first hfirst second hsecond
  let firstClock : unitInterval := ⟨first, hfirst⟩
  let secondClock : unitInterval := ⟨second, hsecond⟩
  rw [Path.extend_apply witness.mass hfirst,
    Path.extend_apply witness.mass hsecond]
  simp only [NNReal.coe_one, one_mul]
  have hordered (a b : unitInterval) (hab : a ≤ b) :
      witness.mass b who - witness.mass a who ≤ (b : ℝ) - (a : ℝ) := by
    calc
      witness.mass b who - witness.mass a who ≤
          ∑ owner, (witness.mass b owner - witness.mass a owner) := by
        exact Finset.single_le_sum
          (fun owner _ => sub_nonneg.mpr (witness.monotone owner hab))
          (Finset.mem_univ who)
      _ = (b : ℝ) - (a : ℝ) := by
        rw [Finset.sum_sub_distrib, witness.total, witness.total]
  rcases le_total first second with hle | hle
  · rw [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr
      (witness.monotone who hle))]
    rw [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hle)]
    simpa only [neg_sub] using hordered firstClock secondClock hle
  · rw [dist_comm first second, dist_comm
      (witness.mass firstClock who) (witness.mass secondClock who)]
    rw [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr
      (witness.monotone who hle))]
    rw [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hle)]
    simpa only [neg_sub] using hordered secondClock firstClock hle

theorem ContinuousZeroPerfectSingletonPath.logMass_absolutelyContinuousOnInterval
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (witness : ContinuousZeroPerfectSingletonPath reward)
    (who : ι) {T : ℝ} (hT : 0 ≤ T) :
    AbsolutelyContinuousOnInterval (witness.logMass who) 0 T := by
  have hclockContDiff : ContDiffOn ℝ 1 logarithmicPathClock (Set.Icc 0 T) := by
    unfold logarithmicPathClock
    exact (contDiff_const.sub contDiff_neg.exp).contDiffOn
  obtain ⟨K, hclockLip⟩ := hclockContDiff.exists_lipschitzOnWith
    (by norm_num) (convex_Icc (0 : ℝ) T) isCompact_Icc
  have hmaps : Set.MapsTo logarithmicPathClock (Set.Icc 0 T) (Set.Icc 0 1) := by
    intro tau htau
    exact ⟨(logarithmicPathClock_mem_Ico htau.1).1,
      (logarithmicPathClock_mem_Ico htau.1).2.le⟩
  have hcomp :=
    (ContinuousZeroPerfectSingletonPath.lipschitzOnWith_mass_extend_apply
      witness who).comp hclockLip hmaps
  change LipschitzOnWith (1 * K) (witness.logMass who) (Set.Icc 0 T) at hcomp
  rw [← uIcc_of_le hT] at hcomp
  exact hcomp.absolutelyContinuousOnInterval

/-- Every logarithmic mass coordinate is differentiable almost everywhere
on each finite positive clock interval. -/
theorem ContinuousZeroPerfectSingletonPath.ae_forall_differentiableAt_logMass
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (witness : ContinuousZeroPerfectSingletonPath reward)
    {T : ℝ} (hT : 0 ≤ T) :
    ∀ᵐ tau : ℝ, tau ∈ Set.Icc (0 : ℝ) T → ∀ who,
      DifferentiableAt ℝ (witness.logMass who) tau := by
  have hforall : ∀ᵐ tau : ℝ, ∀ who, tau ∈ Set.Icc (0 : ℝ) T →
      DifferentiableAt ℝ (witness.logMass who) tau := by
    apply Filter.eventually_all.mpr
    intro who
    simpa only [uIcc_of_le hT] using
      (witness.logMass_absolutelyContinuousOnInterval who hT
        |>.ae_differentiableAt)
  filter_upwards [hforall] with tau htau hmem who
  exact htau who hmem

/-- The conditional logarithmic rates sum to one almost everywhere on every
finite positive interval. -/
theorem ContinuousZeroPerfectSingletonPath.ae_sum_logRate_eq_one
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (witness : ContinuousZeroPerfectSingletonPath reward)
    {T : ℝ} (hT : 0 ≤ T) :
    ∀ᵐ tau : ℝ, tau ∈ Set.Ioo (0 : ℝ) T →
      ∑ who, witness.logRate who tau = 1 := by
  filter_upwards [witness.ae_forall_differentiableAt_logMass hT]
    with tau hdifferentiable htau
  have hsumDeriv := HasDerivAt.sum fun who (_ : who ∈ Finset.univ) =>
    (hdifferentiable ⟨htau.1.le, htau.2.le⟩ who).hasDerivAt
  have hclockRaw := (hasDerivAt_const tau 1).sub
    ((Real.hasDerivAt_exp (-tau)).comp tau (hasDerivAt_neg tau))
  have hclock := hclockRaw.congr_of_eventuallyEq
      (f₁ := ∑ who, witness.logMass who) (by
    filter_upwards [Ioi_mem_nhds htau.1] with second hsecond
    rw [Finset.sum_apply, witness.sum_logMass hsecond.le]
    rfl)
  have hsumRaw := hsumDeriv.unique hclock
  have hsum : ∑ who, deriv (witness.logMass who) tau = Real.exp (-tau) := by
    simpa only [zero_sub, mul_neg, mul_one, neg_neg] using hsumRaw
  simp only [ContinuousZeroPerfectSingletonPath.logRate, ← Finset.mul_sum,
    hsum, ← Real.exp_add]
  rw [show tau + -tau = 0 by ring, Real.exp_zero]

/-- Differentiability of a logarithmic mass coordinate transfers back to the
ordinary absorption clock.  Its ordinary density is exactly `logRate`. -/
theorem ContinuousZeroPerfectSingletonPath.differentiableAt_mass_extend_of_logMass
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (witness : ContinuousZeroPerfectSingletonPath reward)
    (who : ι) {tau : ℝ} (htau : 0 < tau)
    (hdifferentiable : DifferentiableAt ℝ (witness.logMass who) tau) :
    HasDerivAt (fun time => witness.mass.extend time who)
      (witness.logRate who tau) (logarithmicPathClock tau) := by
  let time := logarithmicPathClock tau
  have htime : time ∈ Set.Ioo (0 : ℝ) 1 := by
    constructor
    · change 0 < logarithmicPathClock tau
      rw [logarithmicPathClock, sub_pos, Real.exp_lt_one_iff]
      linarith
    · exact (logarithmicPathClock_mem_Ico htau.le).2
  have hone : 1 - time ≠ 0 := ne_of_gt (sub_pos.mpr htime.2)
  have hsub := (hasDerivAt_id time).const_sub 1
  have hinverse := (hsub.log hone).neg
  have hinverseValue : (-fun second => Real.log (1 - second)) time = tau := by
    change -Real.log (1 - time) = tau
    rw [show 1 - time = Real.exp (-tau) by
      simp only [time, logarithmicPathClock]
      ring, Real.log_exp]
    ring
  have hcomp := hdifferentiable.hasDerivAt.comp_of_eq
    time hinverse hinverseValue.symm
  have heq :
      (witness.logMass who ∘ (-fun second => Real.log (1 - second))) =ᶠ[𝓝 time]
        fun second => witness.mass.extend second who := by
    filter_upwards [Ioo_mem_nhds htime.1 htime.2] with second hsecond
    change witness.logMass who (-Real.log (1 - second)) =
      witness.mass.extend second who
    simp only [ContinuousZeroPerfectSingletonPath.logMass,
      logarithmicPathClock, neg_neg,
      Real.exp_log (sub_pos.mpr hsecond.2)]
    ring_nf
  have hmass := heq.hasDerivAt_iff.mp hcomp
  simp only [id_eq] at hmass
  have hcoef : deriv (witness.logMass who) tau *
      (-(-1 / (1 - time))) = witness.logRate who tau := by
    rw [show 1 - time = Real.exp (-tau) by
      simp only [time, logarithmicPathClock]
      ring, div_eq_mul_inv, Real.exp_neg]
    simp only [inv_inv, neg_mul, neg_neg, one_mul,
      ContinuousZeroPerfectSingletonPath.logRate]
    ring
  rw [hcoef] at hmass
  exact hmass

/-- Positive logarithmic hazard activates exact owner indifference. -/
theorem ContinuousZeroPerfectSingletonPath.payoff_eq_solo_of_logRate_pos
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (witness : ContinuousZeroPerfectSingletonPath reward)
    (who : ι) {tau : ℝ} (htau : 0 < tau)
    (hdifferentiable : DifferentiableAt ℝ (witness.logMass who) tau)
    (hpositive : 0 < witness.logRate who tau) :
    absorptionPathPayoff reward witness.path (logarithmicPathClock tau) who =
      quittingSoloReward reward who who := by
  have htime : logarithmicPathClock tau ∈ Set.Ioo (0 : ℝ) 1 := by
    constructor
    · rw [logarithmicPathClock, sub_pos, Real.exp_lt_one_iff]
      linarith
    · exact (logarithmicPathClock_mem_Ico htau.le).2
  have hmass := witness.differentiableAt_mass_extend_of_logMass
    who htau hdifferentiable
  apply witness.payoff_eq_solo_of_clockRate_pos
    htime who hmass.differentiableAt
  simpa only [ContinuousZeroPerfectSingletonPath.clockRate, hmass.deriv]
    using hpositive

/-- Almost everywhere on finite positive logarithmic intervals, each active
owner is exactly indifferent. -/
theorem ContinuousZeroPerfectSingletonPath.ae_active_logRate_indifferent
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (witness : ContinuousZeroPerfectSingletonPath reward)
    {T : ℝ} (hT : 0 ≤ T) :
    ∀ᵐ tau : ℝ, tau ∈ Set.Ioo (0 : ℝ) T → ∀ who,
      0 < witness.logRate who tau →
        absorptionPathPayoff reward witness.path
            (logarithmicPathClock tau) who =
          quittingSoloReward reward who who := by
  filter_upwards [witness.ae_forall_differentiableAt_logMass hT]
    with tau hdifferentiable htau who hpositive
  exact witness.payoff_eq_solo_of_logRate_pos who htau.1
    (hdifferentiable ⟨htau.1.le, htau.2.le⟩ who) hpositive

/-- The residual singleton payoff written in logarithmic time. -/
def ContinuousZeroPerfectSingletonPath.logPayoff
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (witness : ContinuousZeroPerfectSingletonPath reward)
    (tau : ℝ) (who : ι) : ℝ :=
  Real.exp tau * ∑ owner,
    (witness.terminal owner - witness.logMass owner tau) *
      quittingSoloReward reward owner who

omit [Fintype ι] [DecidableEq ι] in
theorem quittingSoloReward_eq_projectiveSingletonTerminal
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (owner who : ι) :
    quittingSoloReward reward owner who =
      reward (quittingProjectiveSingletonTerminal owner) who := by
  unfold quittingSoloReward quittingProjectiveSingletonTerminal
  congr

theorem ContinuousZeroPerfectSingletonPath.logPayoff_eq_absorptionPathPayoff
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (witness : ContinuousZeroPerfectSingletonPath reward)
    {tau : ℝ} (htau : 0 ≤ tau) (who : ι) :
    witness.logPayoff reward tau who =
      absorptionPathPayoff reward witness.path
        (logarithmicPathClock tau) who := by
  let time : unitInterval :=
    ⟨logarithmicPathClock tau,
      (logarithmicPathClock_mem_Ico htau).1,
      (logarithmicPathClock_mem_Ico htau).2.le⟩
  have htimeOne : time ≠ 1 := by
    intro heq
    have := congrArg Subtype.val heq
    exact (ne_of_lt (logarithmicPathClock_mem_Ico htau).2) this
  change witness.logPayoff reward tau who =
    absorptionPathPayoff reward
      (singletonAbsorptionPathOfPlayerPath witness.mass
        witness.monotone witness.total) (time : ℝ) who
  rw [absorptionPathPayoff_singletonAbsorptionPathOfPlayerPath
    witness.mass witness.monotone witness.total reward time htimeOne who]
  simp_rw [witness.mass.target]
  have hmass (owner : ι) : witness.mass time owner = witness.logMass owner tau := by
    exact (witness.logMass_eq_mass owner htau).symm
  simp_rw [hmass]
  have hdenom : 1 - (time : ℝ) = Real.exp (-tau) := by
    simp only [time, logarithmicPathClock]
    ring
  rw [hdenom, div_eq_mul_inv, Real.exp_neg, inv_inv]
  unfold ContinuousZeroPerfectSingletonPath.logPayoff
  simp_rw [quittingSoloReward_eq_projectiveSingletonTerminal]
  ring

/-- Every logarithmic payoff coordinate is absolutely continuous on a finite
positive interval. -/
theorem ContinuousZeroPerfectSingletonPath.logPayoff_absolutelyContinuousOnInterval
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (witness : ContinuousZeroPerfectSingletonPath reward)
    (who : ι) {T : ℝ} (hT : 0 ≤ T) :
    AbsolutelyContinuousOnInterval (witness.logPayoff reward · who) 0 T := by
  have hterm (owner : ι) : AbsolutelyContinuousOnInterval
      (fun tau => (witness.terminal owner - witness.logMass owner tau) *
        quittingSoloReward reward owner who) 0 T := by
    have hconst : AbsolutelyContinuousOnInterval
        (fun _ : ℝ => witness.terminal owner) 0 T :=
      contDiff_const.contDiffOn.absolutelyContinuousOnInterval
    have hdiff := hconst.fun_sub
      (witness.logMass_absolutelyContinuousOnInterval owner hT)
    have hmul := AbsolutelyContinuousOnInterval.const_mul
      (quittingSoloReward reward owner who) hdiff
    simpa only [mul_comm] using hmul
  have hsumRaw := absolutelyContinuousOnInterval_finset_sum
    (Finset.univ : Finset ι)
    (fun owner tau => (witness.terminal owner - witness.logMass owner tau) *
      quittingSoloReward reward owner who)
    (fun owner _ => hterm owner)
  have hsum : AbsolutelyContinuousOnInterval
      (fun tau => ∑ owner,
        (witness.terminal owner - witness.logMass owner tau) *
          quittingSoloReward reward owner who) 0 T := by
    rw [show (∑ owner,
        fun tau => (witness.terminal owner - witness.logMass owner tau) *
          quittingSoloReward reward owner who) =
        (fun tau => ∑ owner,
          (witness.terminal owner - witness.logMass owner tau) *
            quittingSoloReward reward owner who) by
      funext tau
      exact Finset.sum_apply tau Finset.univ _] at hsumRaw
    exact hsumRaw
  have hexp : AbsolutelyContinuousOnInterval Real.exp 0 T :=
    Real.contDiff_exp.contDiffOn.absolutelyContinuousOnInterval
  simpa only [ContinuousZeroPerfectSingletonPath.logPayoff] using
    hexp.fun_mul hsum

/-- At a common differentiability point of the logarithmic mass coordinates,
the residual payoff satisfies the exact Bellman differential equation. -/
theorem ContinuousZeroPerfectSingletonPath.deriv_logPayoff_eq
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (witness : ContinuousZeroPerfectSingletonPath reward)
    (who : ι) {tau : ℝ}
    (hdifferentiable : ∀ owner,
      DifferentiableAt ℝ (witness.logMass owner) tau) :
    deriv (witness.logPayoff reward · who) tau =
      witness.logPayoff reward tau who -
        ∑ owner, witness.logRate owner tau *
          quittingSoloReward reward owner who := by
  have hterm (owner : ι) :=
    ((hasDerivAt_const tau (witness.terminal owner)).sub
      (hdifferentiable owner).hasDerivAt).mul_const
        (quittingSoloReward reward owner who)
  have hsum := HasDerivAt.sum fun owner (_ : owner ∈ Finset.univ) => hterm owner
  have hraw := (Real.hasDerivAt_exp tau).mul hsum
  have hraw' := hraw.congr_of_eventuallyEq
    (f₁ := fun second => Real.exp second * ∑ owner,
      (witness.terminal owner - witness.logMass owner second) *
        quittingSoloReward reward owner who)
    (Filter.Eventually.of_forall fun second => by
      simp only [Pi.mul_apply, Finset.sum_apply, Pi.sub_apply])
  have hderiv := hraw'.deriv
  unfold ContinuousZeroPerfectSingletonPath.logPayoff
  rw [hderiv]
  simp only [ContinuousZeroPerfectSingletonPath.logRate,
    Finset.sum_apply, Pi.sub_apply, zero_sub]
  simp_rw [sub_mul]
  rw [Finset.sum_sub_distrib, Finset.mul_sum]
  simp_rw [mul_assoc]
  have hneg : (∑ owner, Real.exp tau *
      (-deriv (witness.logMass owner) tau *
        quittingSoloReward reward owner who)) =
      -(∑ owner, Real.exp tau *
        (deriv (witness.logMass owner) tau *
          quittingSoloReward reward owner who)) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro owner _
    ring
  rw [hneg]
  ring

/-- The logarithmic Bellman derivative identity holds almost everywhere on
every finite positive interval. -/
theorem ContinuousZeroPerfectSingletonPath.ae_deriv_logPayoff_eq
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (witness : ContinuousZeroPerfectSingletonPath reward)
    (who : ι) {T : ℝ} (hT : 0 ≤ T) :
    ∀ᵐ tau : ℝ, tau ∈ Set.Icc (0 : ℝ) T →
      deriv (witness.logPayoff reward · who) tau =
        witness.logPayoff reward tau who -
          ∑ owner, witness.logRate owner tau *
            quittingSoloReward reward owner who := by
  filter_upwards [witness.ae_forall_differentiableAt_logMass hT]
    with tau hdifferentiable htau
  exact witness.deriv_logPayoff_eq reward who (hdifferentiable htau)

/-- The conditional logarithmic rate is interval integrable on every finite
nonnegative clock interval. -/
theorem ContinuousZeroPerfectSingletonPath.logRate_intervalIntegrable
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (witness : ContinuousZeroPerfectSingletonPath reward)
    (who : ι) {first second : ℝ}
    (hfirst : 0 ≤ first) (hsecond : first ≤ second) :
    IntervalIntegrable (witness.logRate who) volume first second := by
  have hsecond0 : 0 ≤ second := hfirst.trans hsecond
  have hderiv :=
    (witness.logMass_absolutelyContinuousOnInterval who hsecond0)
      |>.intervalIntegrable_deriv
  have hsubset : Set.uIcc first second ⊆ Set.uIcc 0 second := by
    rw [uIcc_of_le hsecond, uIcc_of_le hsecond0]
    intro time htime
    exact ⟨hfirst.trans htime.1, htime.2⟩
  have hderiv' := hderiv.mono_set hsubset
  have hexp : ContinuousOn Real.exp (Set.uIcc first second) :=
    Real.continuous_exp.continuousOn
  change IntervalIntegrable
    (fun tau => Real.exp tau * deriv (witness.logMass who) tau)
      volume first second
  exact hderiv'.continuousOn_mul hexp

/-- Integrated logarithmic hazard of one owner in block `time`. -/
def ContinuousZeroPerfectSingletonPath.logBlockHazard
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (witness : ContinuousZeroPerfectSingletonPath reward)
    (h : ℝ) (time : ℕ) (owner : ι) : ℝ :=
  ∫ tau in (time : ℝ) * h..(time + 1 : ℝ) * h,
    witness.logRate owner tau

theorem ContinuousZeroPerfectSingletonPath.logBlockHazard_nonneg
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (witness : ContinuousZeroPerfectSingletonPath reward)
    {h : ℝ} (hh : 0 ≤ h) (time : ℕ) (owner : ι) :
    0 ≤ witness.logBlockHazard h time owner := by
  unfold ContinuousZeroPerfectSingletonPath.logBlockHazard
  apply intervalIntegral.integral_nonneg
  · have htime : (0 : ℝ) ≤ time := Nat.cast_nonneg time
    nlinarith
  · intro tau _
    exact witness.logRate_nonneg owner tau

/-- Integrated logarithmic hazards have exact block total `h`. -/
theorem ContinuousZeroPerfectSingletonPath.sum_logBlockHazard
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (witness : ContinuousZeroPerfectSingletonPath reward)
    {h : ℝ} (hh : 0 < h) (time : ℕ) :
    ∑ owner, witness.logBlockHazard h time owner = h := by
  let first : ℝ := (time : ℝ) * h
  let second : ℝ := (time + 1 : ℝ) * h
  have hfirst : 0 ≤ first := mul_nonneg (Nat.cast_nonneg time) hh.le
  have hsecond : first ≤ second := by
    dsimp only [first, second]
    nlinarith
  have hsecondPos : 0 < second := by
    dsimp only [second]
    positivity
  rw [show (∑ owner, witness.logBlockHazard h time owner) =
      ∑ owner, ∫ tau in first..second, witness.logRate owner tau by rfl,
    ← intervalIntegral.integral_finsetSum]
  · calc
      (∫ tau in first..second, ∑ owner, witness.logRate owner tau) =
          ∫ _tau in first..second, (1 : ℝ) := by
        apply intervalIntegral.integral_congr_ae
        filter_upwards [witness.ae_sum_logRate_eq_one hsecondPos.le,
          volume.ae_ne second] with tau hsum hne htau
        apply hsum
        rw [uIoc_of_le hsecond] at htau
        exact ⟨hfirst.trans_lt htau.1, htau.2.lt_of_ne hne⟩
      _ = h := by
        simp only [intervalIntegral.integral_const, smul_eq_mul, mul_one]
        dsimp only [first, second]
        ring
  · intro owner _
    exact witness.logRate_intervalIntegrable owner hfirst hsecond

/-- Opponent-clock hazard rate after deleting `who`. -/
def ContinuousZeroPerfectSingletonPath.deletedHazardRate
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (witness : ContinuousZeroPerfectSingletonPath reward)
    (who : ι) (tau : ℝ) : ℝ :=
  1 - witness.logRate who tau

/-- The opponent hazard rate is nonnegative almost everywhere on every
positive finite interval. -/
theorem ContinuousZeroPerfectSingletonPath.ae_deletedHazardRate_nonneg
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (witness : ContinuousZeroPerfectSingletonPath reward)
    (who : ι) {T : ℝ} (hT : 0 ≤ T) :
    ∀ᵐ tau : ℝ, tau ∈ Set.Icc (0 : ℝ) T →
      0 ≤ witness.deletedHazardRate who tau := by
  filter_upwards [witness.ae_sum_logRate_eq_one hT,
    volume.ae_ne 0, volume.ae_ne T] with tau hsum hzero htop htau
  unfold ContinuousZeroPerfectSingletonPath.deletedHazardRate
  rw [← hsum ⟨lt_of_le_of_ne htau.1 hzero.symm,
    lt_of_le_of_ne htau.2 htop⟩]
  exact sub_nonneg.mpr (Finset.single_le_sum
    (fun owner _ => witness.logRate_nonneg owner tau) (Finset.mem_univ who))

/-- Cumulative opponent-clock hazard through logarithmic time `tau`. -/
def ContinuousZeroPerfectSingletonPath.deletedHazard
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (witness : ContinuousZeroPerfectSingletonPath reward)
    (who : ι) (tau : ℝ) : ℝ :=
  ∫ u in 0..tau, witness.deletedHazardRate who u

/-- Survival of the logarithmic clock after deleting `who`. -/
def ContinuousZeroPerfectSingletonPath.deletedSurvival
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (witness : ContinuousZeroPerfectSingletonPath reward)
    (who : ι) : ℝ → ℝ :=
  Real.exp ∘ (-fun tau => witness.deletedHazard who tau)

@[simp] theorem ContinuousZeroPerfectSingletonPath.deletedSurvival_apply
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (witness : ContinuousZeroPerfectSingletonPath reward)
    (who : ι) (tau : ℝ) :
    witness.deletedSurvival who tau =
      Real.exp (-witness.deletedHazard who tau) :=
  rfl

@[simp] theorem ContinuousZeroPerfectSingletonPath.deletedSurvival_zero
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (witness : ContinuousZeroPerfectSingletonPath reward)
    (who : ι) :
    witness.deletedSurvival who 0 = 1 := by
  simp [ContinuousZeroPerfectSingletonPath.deletedHazard]

theorem ContinuousZeroPerfectSingletonPath.deletedHazardRate_intervalIntegrable
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (witness : ContinuousZeroPerfectSingletonPath reward)
    (who : ι) {first second : ℝ}
    (hfirst : 0 ≤ first) (hsecond : first ≤ second) :
    IntervalIntegrable (witness.deletedHazardRate who)
      volume first second := by
  have hone : IntervalIntegrable (fun _ : ℝ => (1 : ℝ)) volume first second :=
    continuousOn_const.intervalIntegrable
  exact hone.sub (witness.logRate_intervalIntegrable who hfirst hsecond)

/-- Increment of cumulative opponent hazard over a positive interval. -/
theorem ContinuousZeroPerfectSingletonPath.deletedHazard_sub
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (witness : ContinuousZeroPerfectSingletonPath reward)
    (who : ι) {first second : ℝ}
    (hfirst : 0 ≤ first) (hsecond : first ≤ second) :
    witness.deletedHazard who second - witness.deletedHazard who first =
      ∫ tau in first..second, witness.deletedHazardRate who tau := by
  unfold ContinuousZeroPerfectSingletonPath.deletedHazard
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (witness.deletedHazardRate_intervalIntegrable who le_rfl hfirst)
    (witness.deletedHazardRate_intervalIntegrable who hfirst hsecond)]
  ring

/-- Cumulative deleted hazard is monotone on nonnegative times. -/
theorem ContinuousZeroPerfectSingletonPath.deletedHazard_mono
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (witness : ContinuousZeroPerfectSingletonPath reward)
    (who : ι) {first second : ℝ}
    (hfirst : 0 ≤ first) (hsecond : first ≤ second) :
    witness.deletedHazard who first ≤ witness.deletedHazard who second := by
  rw [← sub_nonneg, witness.deletedHazard_sub who hfirst hsecond]
  apply intervalIntegral.integral_nonneg_of_ae_restrict hsecond
  apply (ae_restrict_iff' measurableSet_Icc).2
  filter_upwards [witness.ae_deletedHazardRate_nonneg who
    (hfirst.trans hsecond)] with tau hnonneg htau
  exact hnonneg ⟨hfirst.trans htau.1, htau.2⟩

/-- Deleted survival is antitone on nonnegative logarithmic times. -/
theorem ContinuousZeroPerfectSingletonPath.deletedSurvival_anti
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (witness : ContinuousZeroPerfectSingletonPath reward)
    (who : ι) {first second : ℝ}
    (hfirst : 0 ≤ first) (hsecond : first ≤ second) :
    witness.deletedSurvival who second ≤ witness.deletedSurvival who first := by
  simp only [witness.deletedSurvival_apply, Real.exp_le_exp]
  exact neg_le_neg (witness.deletedHazard_mono who hfirst hsecond)

/-- Exact survival ratio across a positive interval. -/
theorem ContinuousZeroPerfectSingletonPath.deletedSurvival_div
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (witness : ContinuousZeroPerfectSingletonPath reward)
    (who : ι) {first second : ℝ} :
    witness.deletedSurvival who second /
        witness.deletedSurvival who first =
      Real.exp (-(witness.deletedHazard who second -
        witness.deletedHazard who first)) := by
  simp only [witness.deletedSurvival_apply, ← Real.exp_sub]
  congr 1
  ring

/-- Survival ratios on a positive interval lie between the endpoint ratio
and one. -/
theorem ContinuousZeroPerfectSingletonPath.deletedSurvival_ratio_bounds
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (witness : ContinuousZeroPerfectSingletonPath reward)
    (who : ι) {first middle second : ℝ}
    (hfirst : 0 ≤ first) (hfm : first ≤ middle) (hms : middle ≤ second) :
    Real.exp (-(witness.deletedHazard who second -
        witness.deletedHazard who first)) ≤
      witness.deletedSurvival who middle /
        witness.deletedSurvival who first ∧
      witness.deletedSurvival who middle /
        witness.deletedSurvival who first ≤ 1 := by
  rw [← witness.deletedSurvival_div who]
  constructor
  · exact div_le_div_of_nonneg_right
      (witness.deletedSurvival_anti who (hfirst.trans hfm) hms)
      (Real.exp_nonneg _)
  · exact (div_le_one (Real.exp_pos _)).2
      (witness.deletedSurvival_anti who hfirst hfm)

theorem ContinuousZeroPerfectSingletonPath.deletedHazard_absolutelyContinuousOnInterval
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (witness : ContinuousZeroPerfectSingletonPath reward)
    (who : ι) {T : ℝ} (hT : 0 ≤ T) :
    AbsolutelyContinuousOnInterval (witness.deletedHazard who) 0 T := by
  exact (witness.deletedHazardRate_intervalIntegrable who le_rfl hT)
    |>.absolutelyContinuousOnInterval_intervalIntegral (by
      simp only [uIcc_of_le hT, Set.mem_Icc]
      exact ⟨le_rfl, hT⟩)

/-- Deleted survival is absolutely continuous on every finite positive
interval. -/
theorem ContinuousZeroPerfectSingletonPath.deletedSurvival_absolutelyContinuousOnInterval
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (witness : ContinuousZeroPerfectSingletonPath reward)
    (who : ι) {T : ℝ} (hT : 0 ≤ T) :
    AbsolutelyContinuousOnInterval (witness.deletedSurvival who) 0 T := by
  let inner : ℝ → ℝ := -fun tau => witness.deletedHazard who tau
  have hinner : AbsolutelyContinuousOnInterval inner 0 T :=
    (witness.deletedHazard_absolutelyContinuousOnInterval who hT).neg
  obtain ⟨C, hC⟩ := hinner.exists_bound
  have hC0 : 0 ≤ C := by
    exact (norm_nonneg (inner 0)).trans (hC 0 (by simp [hT]))
  have hexpContDiff : ContDiffOn ℝ 1 Real.exp (Set.Icc (-C) C) :=
    Real.contDiff_exp.contDiffOn
  obtain ⟨K, hK⟩ := hexpContDiff.exists_lipschitzOnWith
    (by norm_num) (convex_Icc (-C) C) isCompact_Icc
  have himage : inner '' Set.uIcc (0 : ℝ) T ⊆ Set.Icc (-C) C := by
    intro value hvalue
    obtain ⟨tau, htau, rfl⟩ := hvalue
    have hbound := hC tau htau
    exact (show -C ≤ inner tau ∧ inner tau ≤ C by
      simpa only [Real.norm_eq_abs, abs_le] using hbound)
  exact LipschitzOnWith.comp_absolutelyContinuousOnInterval
    (hK.mono himage) hinner

/-- Almost everywhere, deleted survival has the expected scalar ODE. -/
theorem ContinuousZeroPerfectSingletonPath.ae_deriv_deletedSurvival_eq
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (witness : ContinuousZeroPerfectSingletonPath reward)
    (who : ι) {T : ℝ} (hT : 0 ≤ T) :
    ∀ᵐ tau : ℝ, tau ∈ Set.Icc (0 : ℝ) T →
      deriv (witness.deletedSurvival who) tau =
        -witness.deletedSurvival who tau *
          witness.deletedHazardRate who tau := by
  have hint := witness.deletedHazardRate_intervalIntegrable who le_rfl hT
  filter_upwards [hint.ae_hasDerivAt_integral] with tau htau hmem
  have hhazard := htau (by simpa [uIcc_of_le hT] using hmem)
    0 (by simp [hT])
  have hneg := hhazard.neg
  have hexp := (Real.hasDerivAt_exp (-witness.deletedHazard who tau)).comp
    tau hneg
  have hraw := hexp.deriv
  change deriv (Real.exp ∘ (-fun x => ∫ t in 0..x,
    witness.deletedHazardRate who t)) tau =
      -(Real.exp (-∫ t in 0..tau, witness.deletedHazardRate who t)) *
        witness.deletedHazardRate who tau
  rw [hraw]
  unfold ContinuousZeroPerfectSingletonPath.deletedHazard
  ring

/-- Opponent payoff flow after deleting `who`; the subtracted self term makes
the definition insensitive to the chosen representation of the finite sum. -/
def ContinuousZeroPerfectSingletonPath.deletedOpponentPayoffRate
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (witness : ContinuousZeroPerfectSingletonPath reward)
    (who : ι) (tau : ℝ) : ℝ :=
  (∑ owner, witness.logRate owner tau *
    quittingSoloReward reward owner who) -
      witness.logRate who tau * quittingSoloReward reward who who

/-- Almost everywhere, the deleted-survival-weighted continuation payoff has
derivative equal to minus the opponent payoff flow. -/
theorem ContinuousZeroPerfectSingletonPath.ae_deriv_deletedProduct_eq
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (witness : ContinuousZeroPerfectSingletonPath reward)
    (who : ι) {T : ℝ} (hT : 0 ≤ T) :
    ∀ᵐ tau : ℝ, tau ∈ Set.Ioo (0 : ℝ) T →
      deriv (fun second => witness.deletedSurvival who second *
        witness.logPayoff reward second who) tau =
        -witness.deletedSurvival who tau *
          witness.deletedOpponentPayoffRate reward who tau := by
  have hsurvivalDiff :=
    (witness.deletedSurvival_absolutelyContinuousOnInterval who hT)
      |>.ae_differentiableAt
  have hpayoffDiff :=
    (witness.logPayoff_absolutelyContinuousOnInterval reward who hT)
      |>.ae_differentiableAt
  filter_upwards [hsurvivalDiff, hpayoffDiff,
      witness.ae_deriv_deletedSurvival_eq who hT,
      witness.ae_deriv_logPayoff_eq reward who hT,
      witness.ae_active_logRate_indifferent hT]
    with tau hsurvivalDiff hpayoffDiff hsurvivalDeriv hpayoffDeriv
      hactive htau
  have htauIcc : tau ∈ Set.Icc (0 : ℝ) T := ⟨htau.1.le, htau.2.le⟩
  have hsurvivalDiff' := hsurvivalDiff (by
    simpa [uIcc_of_le hT] using htauIcc)
  have hpayoffDiff' := hpayoffDiff (by
    simpa [uIcc_of_le hT] using htauIcc)
  have hproduct := hsurvivalDiff'.hasDerivAt.mul hpayoffDiff'.hasDerivAt
  have hproduct' := hproduct.congr_of_eventuallyEq
    (f₁ := fun second => witness.deletedSurvival who second *
      witness.logPayoff reward second who)
    (Filter.Eventually.of_forall fun _ => rfl)
  have hproductDeriv := hproduct'.deriv
  have hcomplementarity : witness.logRate who tau *
      (witness.logPayoff reward tau who -
        quittingSoloReward reward who who) = 0 := by
    by_cases hzero : witness.logRate who tau = 0
    · rw [hzero, zero_mul]
    · have hpositive : 0 < witness.logRate who tau :=
        lt_of_le_of_ne (witness.logRate_nonneg who tau) (Ne.symm hzero)
      have hindifferent := hactive htau who hpositive
      rw [witness.logPayoff_eq_absorptionPathPayoff reward htau.1.le,
        hindifferent, sub_self, mul_zero]
  rw [hproductDeriv, hsurvivalDeriv htauIcc, hpayoffDeriv htauIcc]
  unfold ContinuousZeroPerfectSingletonPath.deletedHazardRate
    ContinuousZeroPerfectSingletonPath.deletedOpponentPayoffRate
  have hscaled := congrArg
    (fun value => witness.deletedSurvival who tau * value)
    hcomplementarity
  ring_nf at hcomplementarity ⊢
  ring_nf at hscaled
  linarith [hscaled]

/-- Sequential perfection gives the lower solo-payoff inequality at every
finite logarithmic time. -/
theorem ContinuousZeroPerfectSingletonPath.solo_le_logPayoff
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (witness : ContinuousZeroPerfectSingletonPath reward)
    (who : ι) {tau : ℝ} (htau : 0 ≤ tau) :
    quittingSoloReward reward who who ≤ witness.logPayoff reward tau who := by
  let time : unitInterval :=
    ⟨logarithmicPathClock tau,
      (logarithmicPathClock_mem_Ico htau).1,
      (logarithmicPathClock_mem_Ico htau).2.le⟩
  have htimeOne : (time : ℝ) ≠ 1 :=
    ne_of_lt (logarithmicPathClock_mem_Ico htau).2
  have hpathTime : (time : ℝ) ∈ pathTimes witness.path.1 := by
    rw [witness.continuous]
    exact time.property
  have hlower := (witness.zeroPerfect who).2 (time : ℝ)
    hpathTime htimeOne |>.1
  rw [witness.logPayoff_eq_absorptionPathPayoff reward htau]
  simpa [ContinuousZeroPerfectSingletonPath.path,
    quittingSoloReward, quittingProjectiveSingletonTerminal] using hlower

/-- Exact finite deleted-clock Snell identity. -/
theorem ContinuousZeroPerfectSingletonPath.deletedSnell_identity
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (witness : ContinuousZeroPerfectSingletonPath reward)
    (who : ι) {T : ℝ} (hT : 0 ≤ T) :
    witness.logPayoff reward 0 who =
      (∫ tau in 0..T, witness.deletedSurvival who tau *
        witness.deletedOpponentPayoffRate reward who tau) +
        witness.deletedSurvival who T * witness.logPayoff reward T who := by
  have hproductAC : AbsolutelyContinuousOnInterval
      (fun tau => witness.deletedSurvival who tau *
        witness.logPayoff reward tau who) 0 T :=
    (witness.deletedSurvival_absolutelyContinuousOnInterval who hT).fun_mul
      (witness.logPayoff_absolutelyContinuousOnInterval reward who hT)
  have hFTC := hproductAC.integral_deriv_eq_sub
  have hderiv := witness.ae_deriv_deletedProduct_eq reward who hT
  have hcongr : (∫ tau in 0..T, deriv (fun second =>
      witness.deletedSurvival who second *
        witness.logPayoff reward second who) tau) =
      ∫ tau in 0..T, -witness.deletedSurvival who tau *
        witness.deletedOpponentPayoffRate reward who tau := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [hderiv, volume.ae_ne T] with tau hderiv hne htau
    apply hderiv
    rw [uIoc_of_le hT] at htau
    exact ⟨htau.1, htau.2.lt_of_ne hne⟩
  rw [hcongr] at hFTC
  have hneg : (∫ tau in 0..T, -witness.deletedSurvival who tau *
      witness.deletedOpponentPayoffRate reward who tau) =
      -(∫ tau in 0..T, witness.deletedSurvival who tau *
        witness.deletedOpponentPayoffRate reward who tau) := by
    rw [← intervalIntegral.integral_neg]
    apply intervalIntegral.integral_congr
    intro tau _
    ring
  rw [hneg] at hFTC
  simp only [witness.deletedSurvival_zero, one_mul] at hFTC
  linarith

/-- Every finite deterministic quit time is weakly unprofitable in the
continuum deleted-clock model. -/
theorem ContinuousZeroPerfectSingletonPath.deletedFiniteQuit_cap
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (witness : ContinuousZeroPerfectSingletonPath reward)
    (who : ι) {T : ℝ} (hT : 0 ≤ T) :
    (∫ tau in 0..T, witness.deletedSurvival who tau *
      witness.deletedOpponentPayoffRate reward who tau) +
        witness.deletedSurvival who T *
          quittingSoloReward reward who who ≤
      witness.logPayoff reward 0 who := by
  rw [witness.deletedSnell_identity reward who hT]
  gcongr
  · exact Real.exp_nonneg _
  · exact witness.solo_le_logPayoff reward who hT

/-- Cumulative deleted hazard is total time minus the owner's integrated
hazard. -/
theorem ContinuousZeroPerfectSingletonPath.deletedHazard_eq_sub_blockHazard
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (witness : ContinuousZeroPerfectSingletonPath reward)
    (who : ι) {T : ℝ} (hT : 0 ≤ T) :
    witness.deletedHazard who T = T - witness.logBlockHazard T 0 who := by
  unfold ContinuousZeroPerfectSingletonPath.deletedHazard
    ContinuousZeroPerfectSingletonPath.deletedHazardRate
    ContinuousZeroPerfectSingletonPath.logBlockHazard
  rw [intervalIntegral.integral_sub]
  · simp
  · exact continuousOn_const.intervalIntegrable
  · exact witness.logRate_intervalIntegrable who le_rfl hT

/-- Deleted-hazard increment over one mesh block is the sum of the opponents'
integrated block hazards. -/
theorem ContinuousZeroPerfectSingletonPath.deletedHazard_blockIncrement
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (witness : ContinuousZeroPerfectSingletonPath reward)
    (who : ι) {h : ℝ} (hh : 0 < h) (time : ℕ) :
    witness.deletedHazard who ((time + 1 : ℝ) * h) -
        witness.deletedHazard who ((time : ℝ) * h) =
      ∑ owner ∈ Finset.univ.erase who,
        witness.logBlockHazard h time owner := by
  have hfirst : 0 ≤ (time : ℝ) * h :=
    mul_nonneg (Nat.cast_nonneg time) hh.le
  have hsecond : (time : ℝ) * h ≤ (time + 1 : ℝ) * h := by
    nlinarith
  rw [witness.deletedHazard_sub who hfirst hsecond]
  change (∫ tau in (time : ℝ) * h..(time + 1 : ℝ) * h,
      witness.deletedHazardRate who tau) = _
  rw [show (∑ owner ∈ Finset.univ.erase who,
      witness.logBlockHazard h time owner) =
      ∑ owner ∈ Finset.univ.erase who,
        ∫ tau in (time : ℝ) * h..(time + 1 : ℝ) * h,
          witness.logRate owner tau by rfl,
    ← intervalIntegral.integral_finsetSum]
  · apply intervalIntegral.integral_congr_ae
    filter_upwards [witness.ae_sum_logRate_eq_one
      (show 0 ≤ (time + 1 : ℝ) * h by positivity),
      volume.ae_ne ((time + 1 : ℝ) * h)]
      with tau hsum hne htau
    rw [uIoc_of_le hsecond] at htau
    have htau' : tau ∈ Set.Ioo (0 : ℝ) ((time + 1 : ℝ) * h) :=
      ⟨hfirst.trans_lt htau.1, htau.2.lt_of_ne hne⟩
    have hsplit : witness.logRate who tau +
        ∑ owner ∈ Finset.univ.erase who, witness.logRate owner tau = 1 := by
      calc
        _ = ∑ owner, witness.logRate owner tau := by
          rw [← Finset.sum_erase_add Finset.univ
            (fun owner => witness.logRate owner tau) (Finset.mem_univ who)]
          ring
        _ = 1 := hsum htau'
    unfold ContinuousZeroPerfectSingletonPath.deletedHazardRate
    linarith
  · intro owner howner
    exact witness.logRate_intervalIntegrable owner hfirst hsecond

/-- Two distinct deleted clocks cannot both retain more survival than the
undeleted exponential clock.  This finite-time inequality is the quantitative
exceptional-owner split and does not assume either survival has a limit. -/
theorem ContinuousZeroPerfectSingletonPath.mul_deletedSurvival_le_exp_neg
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (witness : ContinuousZeroPerfectSingletonPath reward)
    {first second : ι} (hne : first ≠ second)
    {T : ℝ} (hT : 0 ≤ T) :
    witness.deletedSurvival first T * witness.deletedSurvival second T ≤
      Real.exp (-T) := by
  rcases hT.eq_or_lt with rfl | hTpos
  · simp [ContinuousZeroPerfectSingletonPath.deletedSurvival,
      ContinuousZeroPerfectSingletonPath.deletedHazard]
  let A : ι → ℝ := fun owner => witness.logBlockHazard T 0 owner
  have hA0 : ∀ owner, 0 ≤ A owner := fun owner =>
    witness.logBlockHazard_nonneg hTpos.le 0 owner
  have hsum : ∑ owner, A owner = T :=
    witness.sum_logBlockHazard hTpos 0
  have hpair : A first + A second ≤ T := by
    have hsecondMem : second ∈ Finset.univ.erase first := by
      simp [hne.symm]
    have hsecondLe : A second ≤ ∑ owner ∈ Finset.univ.erase first, A owner :=
      Finset.single_le_sum (fun owner _ => hA0 owner) hsecondMem
    have hsplit : A first + ∑ owner ∈ Finset.univ.erase first, A owner = T := by
      calc
        A first + ∑ owner ∈ Finset.univ.erase first, A owner =
            (∑ owner ∈ Finset.univ.erase first, A owner) + A first := by ring
        _ = ∑ owner, A owner :=
          Finset.sum_erase_add Finset.univ A (Finset.mem_univ first)
        _ = T := hsum
    linarith
  rw [witness.deletedSurvival_apply, witness.deletedSurvival_apply,
    ← Real.exp_add, Real.exp_le_exp]
  rw [witness.deletedHazard_eq_sub_blockHazard first hT,
    witness.deletedHazard_eq_sub_blockHazard second hT]
  change -(T - A first) + -(T - A second) ≤ -T
  linarith

/-- At most one player can have a strictly positive limiting deleted
survival. -/
theorem ContinuousZeroPerfectSingletonPath.unique_positive_deletedSurvivalLimit
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (witness : ContinuousZeroPerfectSingletonPath reward)
    {first second : ι} {firstLimit secondLimit : ℝ}
    (hfirst : Tendsto (witness.deletedSurvival first) atTop
      (nhds firstLimit))
    (hsecond : Tendsto (witness.deletedSurvival second) atTop
      (nhds secondLimit))
    (hfirstPos : 0 < firstLimit) (hsecondPos : 0 < secondLimit) :
    first = second := by
  by_contra hne
  have hproduct : Tendsto (fun T => witness.deletedSurvival first T *
      witness.deletedSurvival second T) atTop
      (nhds (firstLimit * secondLimit)) := hfirst.mul hsecond
  have hzero : Tendsto (fun T => witness.deletedSurvival first T *
      witness.deletedSurvival second T) atTop (nhds 0) := by
    apply squeeze_zero'
    · filter_upwards with T
      exact mul_nonneg (Real.exp_nonneg _) (Real.exp_nonneg _)
    · filter_upwards [eventually_ge_atTop (0 : ℝ)] with T hT
      exact witness.mul_deletedSurvival_le_exp_neg hne hT
    · exact Real.tendsto_exp_neg_atTop_nhds_zero
  have hlimit : firstLimit * secondLimit = 0 :=
    tendsto_nhds_unique hproduct hzero
  nlinarith

end QuittingLCPClassification
end GameTheory
