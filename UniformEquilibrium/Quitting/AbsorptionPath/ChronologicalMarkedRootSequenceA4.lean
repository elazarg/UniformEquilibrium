/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.AbsorptionPath.ChronologicalMarkedRootSequenceCollision

/-!
# Singleton right derivatives of chronological weak limits

The quadratic finite collision estimate and the clock-gap law force every
nonsingleton coordinate to have zero lower right derivative at a clock time.
This is the decoder-facing form of absorption-path axiom A4.  No jump-root,
sequential-perfection, or full absorption-path assertion is made here.
-/

noncomputable section

namespace GameTheory.QuittingAbsorptionPath

open Filter Finset MeasureTheory Set
open scoped Topology

variable {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]
variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}

omit [Nonempty ι] in
/-- One nonsingleton coordinate increment is bounded by the total collision
coordinate increment. -/
theorem chronologicalCoalitionCDF_sub_le_collisionCDF_sub
    (law : ProbabilityMeasure (QuittingChronologicalEvent reward))
    {lower upper : ℝ} (hlowerUpper : lower ≤ upper)
    (coalition : {S : Finset ι // S.Nonempty})
    (hcard : 2 ≤ coalition.1.card) :
    chronologicalCoalitionCDF law coalition upper -
        chronologicalCoalitionCDF law coalition lower ≤
      chronologicalCollisionCDF law upper -
        chronologicalCollisionCDF law lower := by
  unfold chronologicalCollisionCDF
  rw [← Finset.sum_sub_distrib]
  apply Finset.single_le_sum
    (s := chronologicalCollisionCoalitions)
    (f := fun other ↦ chronologicalCoalitionCDF law other upper -
      chronologicalCoalitionCDF law other lower)
  · intro other hother
    exact sub_nonneg.mpr <|
      ProbabilityTheory.monotone_cdf
        (chronologicalCoalitionClockLaw law other) hlowerUpper
  · simp [chronologicalCollisionCoalitions, hcard]

omit [Nonempty ι] in
/-- At a clock time below one, every nonsingleton coordinate of a
chronological weak limit has zero lower right derivative. -/
theorem pathRightDerivative_chronologicalCadlagPath_eq_zero_of_card_ne_one
    {roots : ℕ → ℕ → ι → PMF Bool}
    (certificates : ∀ rank,
      QuittingFiniteRootSequenceAbsorption (roots rank))
    (law : ProbabilityMeasure (QuittingChronologicalEvent reward))
    (hlaw : Tendsto
      (fun rank ↦ (certificates rank).chronologicalLaw reward)
      atTop (nhds law))
    (hA1 : ∀ time ∈ Icc (0 : ℝ) 1,
      time ≤ pathTotal (chronologicalCadlagPath law) time)
    (hgap : MathUE.HasClockGap (chronologicalClockCDF law))
    {time : ℝ} (htime : time ∈ pathTimes (chronologicalCadlagPath law))
    (htime_ne_one : time ≠ 1)
    (coalition : {S : Finset ι // S.Nonempty})
    (hcard : coalition.1.card ≠ 1) :
    pathRightDerivative (chronologicalCadlagPath law) time coalition = 0 := by
  let distribution := chronologicalClockCDF law
  have htime_lt_one : time < 1 :=
    lt_of_le_of_ne htime.1.2 htime_ne_one
  have hdistributionPath (point : ℝ) (hpoint : point ≤ 1) :
      pathTotal (chronologicalCadlagPath law) point = distribution point := by
    exact pathTotal_chronologicalCadlagPath_eq_chronologicalClockCDF
      law hpoint
  have hfixed : distribution time = time := by
    rw [← hdistributionPath time htime.1.2]
    exact htime.2
  have hdomination (point : ℝ) (hpoint : point < 1) :
      point ≤ distribution point := by
    by_cases hpoint_nonneg : 0 ≤ point
    · rw [← hdistributionPath point hpoint.le]
      exact hA1 point ⟨hpoint_nonneg, hpoint.le⟩
    · exact (not_le.mp hpoint_nonneg).le.trans
        (ProbabilityTheory.cdf_nonneg _ point)
  have hcontinuousTime : ContinuousAt distribution time :=
    MathUE.HasClockGap.continuousAt_of_fixedPoint
      (ProbabilityTheory.monotone_cdf (chronologicalClockLaw law))
      (fun point ↦
        (ProbabilityTheory.cdf (chronologicalClockLaw law)).right_continuous
          point)
      hdomination htime_lt_one hfixed
  let controlled := Classical.choice <|
    MathUE.HasClockGap.nonempty_controlledRightSequence hgap
      (ProbabilityTheory.monotone_cdf (chronologicalClockLaw law))
      (fun point ↦
        (ProbabilityTheory.cdf (chronologicalClockLaw law)).right_continuous
          point)
      hdomination
      (fun point ↦ ProbabilityTheory.cdf_le_one _ point)
      htime_lt_one hfixed
  have hcard_two : 2 ≤ coalition.1.card := by
    have hcard_pos := coalition.2.card_pos
    omega
  let slope := fun point : ℝ ↦
    ((chronologicalCadlagPath law).value point coalition -
      (chronologicalCadlagPath law).value time coalition) / (point - time)
  let bound := fun rank : ℕ ↦
    4 * (Fintype.card ι).choose 2 *
      (controlled.point rank - time) /
        (1 - controlled.point rank)
  have hslope_nonneg (rank : ℕ) :
      0 ≤ slope (controlled.point rank) := by
    apply div_nonneg
    · exact sub_nonneg.mpr <|
        (chronologicalCadlagPath law).monotone coalition htime.1
          ⟨htime.1.1.trans (controlled.point_mem rank).1.le,
            (controlled.point_mem rank).2.le⟩
          (controlled.point_mem rank).1.le
    · exact sub_nonneg.mpr (controlled.point_mem rank).1.le
  have hslope_le (rank : ℕ) :
      slope (controlled.point rank) ≤ bound rank := by
    let point := controlled.point rank
    have htimePoint : time ≤ point := (controlled.point_mem rank).1.le
    have hpoint_lt_one : point < 1 := (controlled.point_mem rank).2
    have hpointContinuous : ContinuousAt distribution point :=
      controlled.continuousAt rank
    have hquadratic :=
      one_sub_upper_mul_collisionCDF_sub_le_choose_mul_clockCDF_sub_sq_of_tendsto
        certificates law hlaw htimePoint hpoint_lt_one
          hcontinuousTime hpointContinuous
    have hcoordinate :=
      chronologicalCoalitionCDF_sub_le_collisionCDF_sub
        law htimePoint coalition hcard_two
    have hcoordinate_nonneg :
        0 ≤ chronologicalCoalitionCDF law coalition point -
          chronologicalCoalitionCDF law coalition time :=
      sub_nonneg.mpr <| ProbabilityTheory.monotone_cdf
        (chronologicalCoalitionClockLaw law coalition) htimePoint
    have hcollision_nonneg :
        0 ≤ chronologicalCollisionCDF law point -
          chronologicalCollisionCDF law time := by
      exact hcoordinate_nonneg.trans hcoordinate
    have hone_sub_pos : 0 < 1 - point := sub_pos.mpr hpoint_lt_one
    have hcoordinateQuadratic :
        (1 - point) *
            (chronologicalCoalitionCDF law coalition point -
              chronologicalCoalitionCDF law coalition time) ≤
          (Fintype.card ι).choose 2 *
            (distribution point - distribution time) ^ 2 := by
      exact (mul_le_mul_of_nonneg_left hcoordinate hone_sub_pos.le).trans
        hquadratic
    have hdistribution_nonneg :
        0 ≤ distribution point - distribution time :=
      sub_nonneg.mpr <| ProbabilityTheory.monotone_cdf
        (chronologicalClockLaw law) htimePoint
    have hdistribution_le :
        distribution point - distribution time ≤ 2 * (point - time) :=
      controlled.distribution_sub_le_two_mul rank
    have hsquare : (distribution point - distribution time) ^ 2 ≤
        (2 * (point - time)) ^ 2 := by
      nlinarith
    have hcoefficient_nonneg :
        (0 : ℝ) ≤ (Fintype.card ι).choose 2 := by positivity
    have hmass :
        (1 - point) *
            (chronologicalCoalitionCDF law coalition point -
              chronologicalCoalitionCDF law coalition time) ≤
          4 * (Fintype.card ι).choose 2 * (point - time) ^ 2 := by
      calc
        _ ≤ (Fintype.card ι).choose 2 *
            (distribution point - distribution time) ^ 2 :=
          hcoordinateQuadratic
        _ ≤ (Fintype.card ι).choose 2 *
            (2 * (point - time)) ^ 2 :=
          mul_le_mul_of_nonneg_left hsquare hcoefficient_nonneg
        _ = 4 * (Fintype.card ι).choose 2 * (point - time) ^ 2 := by ring
    have hpoint_sub_pos : 0 < point - time :=
      sub_pos.mpr (controlled.point_mem rank).1
    change (chronologicalCoalitionCDF law coalition point -
        chronologicalCoalitionCDF law coalition time) / (point - time) ≤
      4 * (Fintype.card ι).choose 2 * (point - time) / (1 - point)
    apply (div_le_div_iff₀ hpoint_sub_pos hone_sub_pos).mpr
    nlinarith
  have hbound_tendsto : Tendsto bound atTop (nhds 0) := by
    have htime_tendsto : Tendsto (fun _ : ℕ ↦ time) atTop (nhds time) :=
      tendsto_const_nhds
    have hone_tendsto : Tendsto (fun _ : ℕ ↦ (1 : ℝ)) atTop
        (nhds 1) := tendsto_const_nhds
    have hnumerator : Tendsto
        (fun rank ↦ controlled.point rank - time) atTop (nhds 0) := by
      simpa only [sub_self] using controlled.tendsto.sub htime_tendsto
    have hdenominator : Tendsto
        (fun rank ↦ 1 - controlled.point rank) atTop (nhds (1 - time)) :=
      hone_tendsto.sub controlled.tendsto
    have hratio := hnumerator.div hdenominator
      (sub_ne_zero.mpr htime_ne_one.symm)
    have hcoefficient : Tendsto
        (fun _ : ℕ ↦ (4 * (Fintype.card ι).choose 2 : ℝ)) atTop
        (nhds (4 * (Fintype.card ι).choose 2 : ℝ)) :=
      tendsto_const_nhds
    convert hcoefficient.mul hratio using 1
    · funext rank
      dsimp only [bound]
      simp only [Pi.div_apply]
      ring
    · norm_num
  have hslope_tendsto : Tendsto
      (fun rank ↦ slope (controlled.point rank)) atTop (nhds 0) := by
    exact squeeze_zero hslope_nonneg hslope_le hbound_tendsto
  let rightFilter := nhdsWithin time (Ioo time 1)
  letI : rightFilter.NeBot := left_nhdsWithin_Ioo_neBot htime_lt_one
  have hcontrolled_right : Tendsto controlled.point atTop rightFilter := by
    rw [tendsto_nhdsWithin_iff]
    exact ⟨controlled.tendsto,
      Filter.Eventually.of_forall controlled.point_mem⟩
  have hslope_eventually_nonneg : ∀ᶠ point in rightFilter,
      0 ≤ slope point := by
    filter_upwards [self_mem_nhdsWithin] with point hpoint
    apply div_nonneg
    · apply sub_nonneg.mpr
      exact (chronologicalCadlagPath law).monotone coalition htime.1
        ⟨htime.1.1.trans hpoint.1.le, hpoint.2.le⟩ hpoint.1.le
    · exact sub_nonneg.mpr hpoint.1.le
  have hslope_frequently_le {tolerance : ℝ} (htolerance : 0 < tolerance) :
      ∃ᶠ point in rightFilter, slope point ≤ tolerance := by
    rw [Filter.frequently_iff]
    intro neighborhood hneighborhood
    have hpointNeighborhood : ∀ᶠ rank in atTop,
        controlled.point rank ∈ neighborhood :=
      hcontrolled_right hneighborhood
    have hslopeTolerance : ∀ᶠ rank in atTop,
        slope (controlled.point rank) ≤ tolerance :=
      (hslope_tendsto.eventually_lt_const htolerance).mono
        fun _ hlt ↦ hlt.le
    obtain ⟨rank, hrankNeighborhood, hrankSlope⟩ :=
      (hpointNeighborhood.and hslopeTolerance).exists
    exact ⟨controlled.point rank, hrankNeighborhood, hrankSlope⟩
  have hliminf_le : Filter.liminf slope rightFilter ≤ 0 := by
    refine le_of_forall_pos_le_add fun tolerance htolerance ↦ ?_
    simpa only [zero_add] using
      (liminf_le_of_frequently_le (hslope_frequently_le htolerance)
        ⟨0, hslope_eventually_nonneg⟩)
  have hslope_cobounded :
      rightFilter.IsCoboundedUnder (fun first second : ℝ ↦ first ≥ second)
        slope := by
    change (Filter.map slope rightFilter).IsCobounded
      (fun first second : ℝ ↦ first ≥ second)
    refine ⟨1, ?_⟩
    intro lower hlower
    change ∀ᶠ point in rightFilter, slope point ≥ lower at hlower
    obtain ⟨point, hpointOne, hpointLower⟩ :=
      ((hslope_frequently_le zero_lt_one).and_eventually hlower).exists
    exact hpointLower.trans hpointOne
  have hliminf_nonneg : 0 ≤ Filter.liminf slope rightFilter :=
    le_liminf_of_le hslope_cobounded hslope_eventually_nonneg
  unfold pathRightDerivative
  change Filter.liminf slope rightFilter = 0
  exact le_antisymm hliminf_le hliminf_nonneg

omit [Nonempty ι] in
/-- A1, the clock-gap law, and finite chronological approximation imply the
literal A4 surface for the decoded weak-limit path. -/
theorem absorptionPathA4_chronologicalCadlagPath_of_tendsto
    {roots : ℕ → ℕ → ι → PMF Bool}
    (certificates : ∀ rank,
      QuittingFiniteRootSequenceAbsorption (roots rank))
    (law : ProbabilityMeasure (QuittingChronologicalEvent reward))
    (hlaw : Tendsto
      (fun rank ↦ (certificates rank).chronologicalLaw reward)
      atTop (nhds law))
    (hA1 : ∀ time ∈ Icc (0 : ℝ) 1,
      time ≤ pathTotal (chronologicalCadlagPath law) time)
    (hgap : MathUE.HasClockGap (chronologicalClockCDF law)) :
    ∀ time ∈ pathTimes (chronologicalCadlagPath law), time ≠ 1 →
      ∀ coalition,
        pathRightDerivative (chronologicalCadlagPath law) time coalition ≠ 0 →
          coalition.1.card = 1 := by
  intro time htime htime_ne_one coalition hderivative
  by_contra hcard
  exact hderivative <|
    pathRightDerivative_chronologicalCadlagPath_eq_zero_of_card_ne_one
      certificates law hlaw hA1 hgap htime htime_ne_one coalition hcard

end GameTheory.QuittingAbsorptionPath
