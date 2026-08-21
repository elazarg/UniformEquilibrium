/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Mathlib.Analysis.Convex.PathConnected
import MathUE.Viability.LipschitzCompactness
import UniformEquilibrium.Quitting.AbsorptionPath.ContinuousPath
import UniformEquilibrium.Quitting.Projective.SingletonLCP

/-!
# Continuous singleton absorption paths

A coordinatewise monotone path of player masses whose total is the clock
canonically defines a continuous absorption path supported on singleton
quitting coalitions.  This is the reusable semantic adapter from cumulative
player controls to absorption paths.
-/

noncomputable section

namespace GameTheory.QuittingAbsorptionPath

open Filter Finset Set unitInterval
open GameTheory Math
open scoped Topology unitInterval

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Push an arbitrary player-mass vector onto singleton quitting coalitions. -/
def singletonCoalitionMass (mass : ι → ℝ)
    (coalition : {S : Finset ι // S.Nonempty}) : ℝ :=
  ∑ owner, if coalition = quittingProjectiveSingletonTerminal owner then
    mass owner else 0

@[simp] theorem singletonCoalitionMass_singleton
    (mass : ι → ℝ) (who : ι) :
    singletonCoalitionMass mass (quittingProjectiveSingletonTerminal who) =
      mass who := by
  unfold singletonCoalitionMass
  rw [Finset.sum_eq_single who]
  · simp
  · intro owner _ hne
    have hcoalition : quittingProjectiveSingletonTerminal who ≠
        quittingProjectiveSingletonTerminal owner := by
      intro heq
      apply hne
      have heq' : who = owner := by
        simpa [quittingProjectiveSingletonTerminal] using
          congrArg (fun S => S.1) heq
      exact heq'.symm
    simp [hcoalition]
  · simp

theorem singletonCoalitionMass_eq_zero_of_card_ne_one
    (mass : ι → ℝ) (coalition : {S : Finset ι // S.Nonempty})
    (hcard : coalition.1.card ≠ 1) :
    singletonCoalitionMass mass coalition = 0 := by
  unfold singletonCoalitionMass
  apply Finset.sum_eq_zero
  intro owner _
  have hne : coalition ≠ quittingProjectiveSingletonTerminal owner := by
    intro heq
    apply hcard
    rw [congrArg (fun S => S.1.card) heq]
    simp [quittingProjectiveSingletonTerminal]
  simp [hne]

theorem sum_singletonCoalitionMass (mass : ι → ℝ) :
    ∑ coalition, singletonCoalitionMass mass coalition = ∑ who, mass who := by
  simp only [singletonCoalitionMass]
  rw [Finset.sum_comm]
  simp

/-- Integrating a payoff over singleton coalition mass is the corresponding
player-mass mixture. -/
theorem sum_singletonCoalitionMass_mul
    (mass : ι → ℝ)
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (who : ι) :
    ∑ coalition, singletonCoalitionMass mass coalition * reward coalition who =
      ∑ owner, mass owner *
        reward (quittingProjectiveSingletonTerminal owner) who := by
  unfold singletonCoalitionMass
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro owner _
  rw [Finset.sum_eq_single (quittingProjectiveSingletonTerminal owner)]
  · simp
  · intro coalition _ hne
    simp [hne]
  · simp

/-! ## Compactness of normalized player-mass paths -/

/-- Regard a path into a metric space as a bounded continuous function on
the compact unit interval. -/
def boundedFunctionOfPath {terminal : ι → ℝ}
    (mass : Path (0 : ι → ℝ) terminal) :
    BoundedContinuousFunction unitInterval (ι → ℝ) :=
  BoundedContinuousFunction.mkOfCompact mass.toContinuousMap

omit [DecidableEq ι] in
/-- Coordinatewise monotonicity and exact total mass force a normalized
player-mass path to be 1-Lipschitz. -/
theorem lipschitzWith_one_of_monotone_of_sum_eq
    {terminal : ι → ℝ} (mass : Path (0 : ι → ℝ) terminal)
    (hmono : ∀ who, Monotone fun time => mass time who)
    (htotal : ∀ time, ∑ who, mass time who = (time : ℝ)) :
    LipschitzWith 1 (boundedFunctionOfPath mass) := by
  rw [lipschitzWith_iff_dist_le_mul]
  have hordered : ∀ first second : unitInterval, first ≤ second →
      dist (mass first) (mass second) ≤ dist first second := by
    intro first second hle
    have hreal : (first : ℝ) ≤ (second : ℝ) := hle
    rw [dist_eq_norm]
    apply (pi_norm_le_iff_of_nonneg dist_nonneg).2
    intro who
    simp only [Pi.sub_apply, Real.norm_eq_abs]
    rw [abs_of_nonpos (sub_nonpos.mpr (hmono who hle))]
    calc
      -(mass first who - mass second who) =
          mass second who - mass first who := by ring
      _ ≤ ∑ owner, (mass second owner - mass first owner) := by
        exact Finset.single_le_sum
          (fun owner _ => sub_nonneg.mpr (hmono owner hle))
          (Finset.mem_univ who)
      _ = (second : ℝ) - (first : ℝ) := by
        rw [Finset.sum_sub_distrib, htotal, htotal]
      _ = dist first second := by
        change (second : ℝ) - (first : ℝ) =
          |(first : ℝ) - (second : ℝ)|
        rw [abs_of_nonpos (sub_nonpos.mpr hreal)]
        ring
  intro first second
  simp only [NNReal.coe_one, one_mul]
  change dist (mass first) (mass second) ≤ dist first second
  rcases le_total first second with hle | hle
  · exact hordered first second hle
  · rw [dist_comm]
    simpa only [dist_comm first second] using hordered second first hle

omit [DecidableEq ι] in
/-- Every sequence of normalized monotone player-mass paths has a uniformly
convergent subsequence whose limit is again normalized and monotone. -/
theorem exists_tendsto_subsequence_monotone_playerMass
    (terminal : ℕ → ι → ℝ)
    (mass : ∀ n, Path (0 : ι → ℝ) (terminal n))
    (hmono : ∀ n who, Monotone fun time => mass n time who)
    (htotal : ∀ n time, ∑ who, mass n time who = (time : ℝ)) :
    ∃ limit : BoundedContinuousFunction unitInterval (ι → ℝ),
      ∃ subsequence : ℕ → ℕ, StrictMono subsequence ∧
        Tendsto (fun n => boundedFunctionOfPath (mass (subsequence n)))
          atTop (nhds limit) ∧
        limit 0 = 0 ∧
        (∀ who, Monotone fun time => limit time who) ∧
        ∀ time, ∑ who, limit time who = (time : ℝ) := by
  let rangeSet : Set (ι → ℝ) := Metric.closedBall 0 1
  have hfamily (n : ℕ) : boundedFunctionOfPath (mass n) ∈
      Viability.compactRangeLipschitzFamily 1 rangeSet := by
    constructor
    · exact lipschitzWith_one_of_monotone_of_sum_eq
        (mass n) (hmono n) (htotal n)
    · intro time
      rw [Metric.mem_closedBall]
      have hlipschitz :=
        (lipschitzWith_one_of_monotone_of_sum_eq
          (mass n) (hmono n) (htotal n)).dist_le_mul time 0
      simp only [NNReal.coe_one, one_mul] at hlipschitz
      change dist (mass n time) (mass n 0) ≤ dist time 0 at hlipschitz
      calc
        dist (mass n time) 0 = dist (mass n time) (mass n 0) := by
          rw [(mass n).source]
        _ ≤ dist time 0 := hlipschitz
        _ ≤ 1 := by
          change |(time : ℝ) - 0| ≤ 1
          rw [sub_zero, abs_of_nonneg time.property.1]
          exact time.property.2
  obtain ⟨limit, _hlimit, subsequence, hsubsequence, htendsto⟩ :=
    Viability.exists_tendsto_subsequence_compactRangeLipschitzFamily
      1 (isCompact_closedBall (0 : ι → ℝ) 1)
      (fun n => boundedFunctionOfPath (mass n)) hfamily
  have htendstoAt (time : unitInterval) : Tendsto
      (fun n => mass (subsequence n) time) atTop (nhds (limit time)) := by
    exact ((BoundedContinuousFunction.lipschitz_eval_const time).continuous
      |>.tendsto limit).comp htendsto
  refine ⟨limit, subsequence, hsubsequence, htendsto, ?_, ?_, ?_⟩
  · apply tendsto_nhds_unique (htendstoAt 0)
    exact (tendsto_const_nhds : Tendsto
      (fun _ : ℕ => (0 : ι → ℝ)) atTop (nhds 0)) |>.congr'
        (Eventually.of_forall fun n => (mass (subsequence n)).source.symm)
  · intro who first second hle
    exact le_of_tendsto_of_tendsto'
      (((continuous_apply who).tendsto _).comp (htendstoAt first))
      (((continuous_apply who).tendsto _).comp (htendstoAt second))
      (fun n => hmono (subsequence n) who hle)
  · intro time
    have hsum : Tendsto (fun n => ∑ who, mass (subsequence n) time who)
        atTop (nhds (∑ who, limit time who)) := by
      apply tendsto_finsetSum
      intro who _
      exact ((continuous_apply who).tendsto _).comp (htendstoAt time)
    apply tendsto_nhds_unique hsum
    exact tendsto_const_nhds.congr' (Eventually.of_forall fun n =>
      (htotal (subsequence n) time).symm)

/-- Extend a player-mass path to real time and place every coordinate on its
singleton quitting coalition. -/
def singletonCadlagPathOfPlayerPath
    {terminal : ι → ℝ} (mass : Path (0 : ι → ℝ) terminal)
    (hmono : ∀ who, Monotone fun time => mass time who)
    (htotal : ∀ time, ∑ who, mass time who = (time : ℝ)) :
    CadlagPath (ι := ι) where
  value time coalition := singletonCoalitionMass (mass.extend time) coalition
  leftValue time coalition :=
    singletonCoalitionMass (mass.extend time) coalition
  value_mem := by
    intro time htime coalition
    let clock : unitInterval := ⟨time, htime⟩
    have hnonneg (who : ι) : 0 ≤ mass.extend time who := by
      rw [show mass.extend time = mass clock from Path.extend_apply mass htime]
      simpa only [mass.source, Pi.zero_apply] using
        hmono who (show (0 : unitInterval) ≤ clock from clock.property.1)
    constructor
    · unfold singletonCoalitionMass
      exact Finset.sum_nonneg fun who _ => by
        split <;> simp_all
    · by_cases hcard : coalition.1.card = 1
      · obtain ⟨owner, howner⟩ := Finset.card_eq_one.mp hcard
        have hcoalition : coalition =
            quittingProjectiveSingletonTerminal owner := by
          apply Subtype.ext
          simpa [quittingProjectiveSingletonTerminal] using howner
        rw [hcoalition, singletonCoalitionMass_singleton]
        calc
          mass.extend time owner ≤ ∑ who, mass.extend time who :=
            Finset.single_le_sum (fun who _ => hnonneg who)
              (Finset.mem_univ owner)
          _ = time := by
            rw [show mass.extend time = mass clock from
              Path.extend_apply mass htime, htotal]
          _ ≤ 1 := htime.2
      · rw [singletonCoalitionMass_eq_zero_of_card_ne_one _ coalition hcard]
        exact zero_le_one
  monotone := by
    intro coalition first hfirst second hsecond hle
    let firstClock : unitInterval := ⟨first, hfirst⟩
    let secondClock : unitInterval := ⟨second, hsecond⟩
    unfold singletonCoalitionMass
    apply Finset.sum_le_sum
    intro who _
    split_ifs
    · rw [show mass.extend first = mass firstClock from
          Path.extend_apply mass hfirst,
        show mass.extend second = mass secondClock from
          Path.extend_apply mass hsecond]
      exact hmono who hle
    · exact le_rfl
  right_continuous := by
    intro coalition time _
    have hcontinuous : Continuous
        (fun s => singletonCoalitionMass (mass.extend s) coalition) := by
      unfold singletonCoalitionMass
      apply continuous_finsetSum
      intro owner _
      split_ifs <;> fun_prop
    exact hcontinuous.continuousAt.tendsto.mono_left inf_le_left
  left_limit := by
    intro coalition time _
    have hcontinuous : Continuous
        (fun s => singletonCoalitionMass (mass.extend s) coalition) := by
      unfold singletonCoalitionMass
      apply continuous_finsetSum
      intro owner _
      split_ifs <;> fun_prop
    exact hcontinuous.continuousAt.tendsto.mono_left inf_le_left
  left_zero := by
    simp [singletonCoalitionMass]

@[simp] theorem pathTotal_singletonCadlagPathOfPlayerPath
    {terminal : ι → ℝ} (mass : Path (0 : ι → ℝ) terminal)
    (hmono : ∀ who, Monotone fun time => mass time who)
    (htotal : ∀ time, ∑ who, mass time who = (time : ℝ))
    {time : ℝ} (htime : time ∈ Icc (0 : ℝ) 1) :
    pathTotal (singletonCadlagPathOfPlayerPath mass hmono htotal) time =
      time := by
  let clock : unitInterval := ⟨time, htime⟩
  rw [pathTotal]
  change ∑ coalition, singletonCoalitionMass (mass.extend time) coalition = _
  rw [sum_singletonCoalitionMass,
    show mass.extend time = mass clock from Path.extend_apply mass htime,
    htotal]

@[simp] theorem pathJump_singletonCadlagPathOfPlayerPath
    {terminal : ι → ℝ} (mass : Path (0 : ι → ℝ) terminal)
    (hmono : ∀ who, Monotone fun time => mass time who)
    (htotal : ∀ time, ∑ who, mass time who = (time : ℝ))
    (time : ℝ) (coalition : {S : Finset ι // S.Nonempty}) :
    pathJump (singletonCadlagPathOfPlayerPath mass hmono htotal)
      time coalition = 0 := by
  simp [pathJump, singletonCadlagPathOfPlayerPath]

theorem pathTimes_singletonCadlagPathOfPlayerPath
    {terminal : ι → ℝ} (mass : Path (0 : ι → ℝ) terminal)
    (hmono : ∀ who, Monotone fun time => mass time who)
    (htotal : ∀ time, ∑ who, mass time who = (time : ℝ)) :
    pathTimes (singletonCadlagPathOfPlayerPath mass hmono htotal) =
      Set.Icc 0 1 := by
  ext time
  simp only [pathTimes, Set.mem_setOf_eq]
  constructor
  · exact fun h => h.1
  · intro htime
    exact ⟨htime,
      pathTotal_singletonCadlagPathOfPlayerPath mass hmono htotal htime⟩

theorem pathJumps_singletonCadlagPathOfPlayerPath
    {terminal : ι → ℝ} (mass : Path (0 : ι → ℝ) terminal)
    (hmono : ∀ who, Monotone fun time => mass time who)
    (htotal : ∀ time, ∑ who, mass time who = (time : ℝ)) :
    pathJumps (singletonCadlagPathOfPlayerPath mass hmono htotal) = ∅ := by
  ext time
  simp [pathJumps]

private theorem pathRightDerivative_singletonCadlagPathOfPlayerPath_eq_zero
    {terminal : ι → ℝ} (mass : Path (0 : ι → ℝ) terminal)
    (hmono : ∀ who, Monotone fun time => mass time who)
    (htotal : ∀ time, ∑ who, mass time who = (time : ℝ))
    {time : ℝ} (htime : time < 1)
    (coalition : {S : Finset ι // S.Nonempty})
    (hcard : coalition.1.card ≠ 1) :
    pathRightDerivative
        (singletonCadlagPathOfPlayerPath mass hmono htotal)
        time coalition = 0 := by
  letI : NeBot (nhdsWithin time (Set.Ioo time 1)) :=
    left_nhdsWithin_Ioo_neBot htime
  unfold pathRightDerivative
  have hzero (s : ℝ) :
      (singletonCadlagPathOfPlayerPath mass hmono htotal).value
        s coalition = 0 :=
    singletonCoalitionMass_eq_zero_of_card_ne_one _ coalition hcard
  simp_rw [hzero]
  simp only [sub_self, zero_div]
  exact Filter.liminf_const (f := nhdsWithin time (Set.Ioo time 1)) 0

/-- A monotone player-mass path with total equal to time satisfies all four
absorption-path axioms. -/
theorem isAbsorptionPath_singletonCadlagPathOfPlayerPath
    {terminal : ι → ℝ} (mass : Path (0 : ι → ℝ) terminal)
    (hmono : ∀ who, Monotone fun time => mass time who)
    (htotal : ∀ time, ∑ who, mass time who = (time : ℝ)) :
    IsAbsorptionPath
      (singletonCadlagPathOfPlayerPath mass hmono htotal) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro time htime
    rw [pathTotal_singletonCadlagPathOfPlayerPath mass hmono htotal htime]
  · intro time htime
    have hpathTime : time ∈ pathTimes
        (singletonCadlagPathOfPlayerPath mass hmono htotal) := by
      rw [pathTimes_singletonCadlagPathOfPlayerPath mass hmono htotal]
      exact htime.1
    exact (htime.2 (Or.inr hpathTime)).elim
  · intro time htime
    rw [pathJumps_singletonCadlagPathOfPlayerPath mass hmono htotal] at htime
    exact htime.elim
  · intro time htime hneOne coalition hderivative
    by_contra hcard
    apply hderivative
    exact pathRightDerivative_singletonCadlagPathOfPlayerPath_eq_zero
      mass hmono htotal (lt_of_le_of_ne htime.1.2 hneOne)
      coalition hcard

/-- The bundled continuous singleton absorption path associated with a
player-mass path. -/
def singletonAbsorptionPathOfPlayerPath
    {terminal : ι → ℝ} (mass : Path (0 : ι → ℝ) terminal)
    (hmono : ∀ who, Monotone fun time => mass time who)
    (htotal : ∀ time, ∑ who, mass time who = (time : ℝ)) :
    AbsorptionPath (ι := ι) :=
  ⟨singletonCadlagPathOfPlayerPath mass hmono htotal,
    isAbsorptionPath_singletonCadlagPathOfPlayerPath mass hmono htotal⟩

/-- The singleton absorption path induced by a player-mass path is
continuous. -/
theorem singletonAbsorptionPathOfPlayerPath_continuous
    {terminal : ι → ℝ} (mass : Path (0 : ι → ℝ) terminal)
    (hmono : ∀ who, Monotone fun time => mass time who)
    (htotal : ∀ time, ∑ who, mass time who = (time : ℝ)) :
    IsContinuousAbsorptionPath
      (singletonAbsorptionPathOfPlayerPath mass hmono htotal) :=
  pathTimes_singletonCadlagPathOfPlayerPath mass hmono htotal

/-- Before terminal time, the payoff of a continuous singleton path is the
normalized mixture of its remaining player masses. -/
theorem absorptionPathPayoff_singletonAbsorptionPathOfPlayerPath
    {terminal : ι → ℝ} (mass : Path (0 : ι → ℝ) terminal)
    (hmono : ∀ who, Monotone fun time => mass time who)
    (htotal : ∀ time, ∑ who, mass time who = (time : ℝ))
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (time : unitInterval) (htimeOne : time ≠ 1) (who : ι) :
    absorptionPathPayoff reward
        (singletonAbsorptionPathOfPlayerPath mass hmono htotal)
        (time : ℝ) who =
      (∑ owner, (mass 1 owner - mass time owner) *
        reward (quittingProjectiveSingletonTerminal owner) who) /
          (1 - (time : ℝ)) := by
  have htime : (time : ℝ) ∈ Icc (0 : ℝ) 1 := time.property
  have htimeLt : (time : ℝ) < 1 :=
    lt_of_le_of_ne time.property.2 fun heq => htimeOne (Subtype.ext heq)
  rw [absorptionPathPayoff, if_pos htime]
  change (if pathTotal
      (singletonCadlagPathOfPlayerPath mass hmono htotal) (time : ℝ) < 1 then
      fun owner => (∑ coalition,
        ((singletonCadlagPathOfPlayerPath mass hmono htotal).value 1 coalition -
          (singletonCadlagPathOfPlayerPath mass hmono htotal).value
            (time : ℝ) coalition) * reward coalition owner) /
              (1 - pathTotal
                (singletonCadlagPathOfPlayerPath mass hmono htotal)
                  (time : ℝ)) else 0) who = _
  rw [pathTotal_singletonCadlagPathOfPlayerPath mass hmono htotal htime,
    if_pos htimeLt]
  change (∑ coalition,
      (singletonCoalitionMass (mass.extend 1) coalition -
        singletonCoalitionMass (mass.extend time) coalition) *
          reward coalition who) / (1 - (time : ℝ)) = _
  rw [show mass.extend 1 = mass 1 from Path.extend_apply mass (by norm_num),
    show mass.extend (time : ℝ) = mass time from Path.extend_apply mass htime]
  congr 1
  simp_rw [sub_mul]
  rw [Finset.sum_sub_distrib,
    sum_singletonCoalitionMass_mul,
    sum_singletonCoalitionMass_mul,
    Finset.sum_sub_distrib]

end GameTheory.QuittingAbsorptionPath
