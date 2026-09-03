/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.AbsorptionPath.BoundaryCellProductRootOdds
import UniformEquilibrium.Quitting.AbsorptionPath.AKRSPartition
import UniformEquilibrium.Quitting.AbsorptionPath.ClockBoundarySourceApproximation
import UniformEquilibrium.Quitting.AbsorptionPath.RationalCoordinateCompactness

/-!
# Singleton derivative support under unit-bounded weak limits

The canonical weak-path, source-boundary, controlled-right, and boundary-cell
interfaces reduce the small-jump argument to its two quantitative limit
estimates and the literal singleton-support conclusion.
-/

noncomputable section

namespace GameTheory.QuittingAbsorptionPath

open Filter Set
open scoped Topology

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- At one later continuity point, the weak-limit nonsingleton increment is
bounded by the exact source-cell absorption odds times the total cell width. -/
theorem value_nonsingletonIncrement_le_absorptionOdds_mul_totalIncrement_of_weakLimit
    {paths : ℕ → AbsorptionPath (ι := ι)}
    {limit : CadlagPath (ι := ι)}
    (hclock : ∀ point ∈ Icc (0 : ℝ) 1, point ≤ pathTotal limit point)
    (hsourceBounded : ∀ index, HasUnitBoundedTotalMass (paths index))
    (hweak : WeaklyConvergesAbsorptionPathsToCadlag paths limit)
    {time later : ℝ} (htime : time ∈ pathTimes limit)
    (htimeOne : time ≠ 1)
    (hlater : later ∈ Icc (0 : ℝ) 1)
    (hlaterNotJump : later ∉ pathJumps limit)
    (htimeLater : time < later)
    (hlaterTotal : pathTotal limit later < 1)
    (hcellHalf :
      (pathTotal limit later - time) / (1 - time) < 1 / 2)
    (coalition : {S : Finset ι // S.Nonempty})
    (hcard : 2 ≤ coalition.1.card) :
    limit.value later coalition - limit.value time coalition ≤
      (((pathTotal limit later - time) / (1 - time)) /
          (1 - (pathTotal limit later - time) / (1 - time))) *
        (pathTotal limit later - time) := by
  let approximation := Classical.choice <|
    nonempty_cadlagLimitClockBoundarySourceApproximation hclock
      hsourceBounded hweak htime htimeOne
  let stopTimes := fun index ↦ pathTotal (paths index).1 later
  let cellAbsorption := fun index ↦
    pathCellAbsorption (paths index).1
      (approximation.sourceTimes index) (stopTimes index)
  let limitAbsorption :=
    (pathTotal limit later - time) / (1 - time)
  let player := coalition.2.choose
  have hplayer : player ∈ coalition.1 :=
    coalition.2.choose_spec
  have hlaterValues := hweak later hlater hlaterNotJump
  have hstopTimes : Tendsto stopTimes atTop
      (nhds (pathTotal limit later)) := by
    unfold stopTimes pathTotal
    exact tendsto_finsetSum Finset.univ fun other _ ↦
      tendsto_pi_nhds.mp hlaterValues other
  have hstopMem (index : ℕ) : stopTimes index ∈ Icc (0 : ℝ) 1 :=
    ⟨hlater.1.trans ((paths index).property.1 later hlater),
      hsourceBounded index later hlater⟩
  have hstopBoundary (index : ℕ) :
      stopTimes index ∈ partitionBoundaryTimes (paths index) :=
    pathTotal_mem_partitionBoundaryTimes (paths index)
      (hsourceBounded index) hlater
  have htimeTotal : time < pathTotal limit later :=
    htimeLater.trans_le (hclock later hlater)
  have hordered : ∀ᶠ index in atTop,
      approximation.sourceTimes index < stopTimes index :=
    approximation.times_tendsto.eventually_lt hstopTimes htimeTotal
  have hstopOne : ∀ᶠ index in atTop, stopTimes index < 1 :=
    hstopTimes.eventually (Iio_mem_nhds hlaterTotal)
  have hcellAbsorption : Tendsto cellAbsorption atTop
      (nhds limitAbsorption) := by
    have hquotient := (hstopTimes.sub approximation.times_tendsto).div
      (tendsto_const_nhds.sub approximation.times_tendsto)
        (sub_ne_zero.mpr htimeOne.symm)
    apply hquotient.congr'
    filter_upwards [] with index
    simp only [Pi.div_apply]
    unfold cellAbsorption pathCellAbsorption
    rw [pathLeftTotal_eq_of_mem_partitionBoundaryTimes (paths index)
        (approximation.source_boundary index),
      pathLeftTotal_eq_of_mem_partitionBoundaryTimes (paths index)
        (hstopBoundary index)]
  have hcellHalfEventually : ∀ᶠ index in atTop,
      cellAbsorption index ≤ 1 / 2 :=
    (hcellAbsorption.eventually_lt_const hcellHalf).mono fun _ hlt ↦ hlt.le
  have hlimitAbsorptionOne : limitAbsorption ≠ 1 := by
    exact ne_of_lt (hcellHalf.trans_le (by norm_num : (1 : ℝ) / 2 ≤ 1))
  have hodds : Tendsto (fun index ↦
      cellAbsorption index / (1 - cellAbsorption index)) atTop
      (nhds (limitAbsorption / (1 - limitAbsorption))) :=
    hcellAbsorption.div (tendsto_const_nhds.sub hcellAbsorption)
      (sub_ne_zero.mpr hlimitAbsorptionOne.symm)
  have hwidth : Tendsto (fun index ↦
      stopTimes index - approximation.sourceTimes index) atTop
      (nhds (pathTotal limit later - time)) :=
    hstopTimes.sub approximation.times_tendsto
  have hright : Tendsto (fun index ↦
      (cellAbsorption index / (1 - cellAbsorption index)) *
        (stopTimes index - approximation.sourceTimes index)) atTop
      (nhds ((limitAbsorption / (1 - limitAbsorption)) *
        (pathTotal limit later - time))) :=
    hodds.mul hwidth
  have hleft : Tendsto (fun index ↦
      (paths index).1.value later coalition -
        (paths index).1.leftValue
          (approximation.sourceTimes index) coalition) atTop
      (nhds (limit.value later coalition - limit.value time coalition)) :=
    (tendsto_pi_nhds.mp hlaterValues coalition).sub
      (approximation.leftValues_tendsto coalition)
  have hsource : ∀ᶠ index in atTop,
      (paths index).1.value later coalition -
          (paths index).1.leftValue
            (approximation.sourceTimes index) coalition ≤
        (cellAbsorption index / (1 - cellAbsorption index)) *
          (stopTimes index - approximation.sourceTimes index) := by
    filter_upwards [hordered, hstopOne, hcellHalfEventually]
      with index horder hnonterminal hhalf
    have hleftValue :=
      leftValue_incidentCoalitionIncrement_le_boundaryCellWidth_mul_odds
        (paths index) (hsourceBounded index)
        (approximation.source_boundary index) (hstopBoundary index)
        horder hnonterminal hhalf coalition.1 player hcard hplayer
    have hvalueLe : (paths index).1.value later coalition ≤
        (paths index).1.leftValue (stopTimes index) coalition :=
      value_le_leftValue_at_pathTotal_of_unitBounded (paths index)
        (hsourceBounded index) hlater coalition
    exact (sub_le_sub_right hvalueLe _).trans hleftValue
  exact le_of_tendsto_of_tendsto hleft hright hsource

/-- Every nonsingleton coordinate has zero lower right derivative at a
nonterminal clock time of a unit-bounded weak limit. -/
theorem pathRightDerivative_eq_zero_of_nonsingleton_of_unitBoundedWeakLimit
    {paths : ℕ → AbsorptionPath (ι := ι)}
    {limit : CadlagPath (ι := ι)}
    (hclock : ∀ point ∈ Icc (0 : ℝ) 1, point ≤ pathTotal limit point)
    (hbound : ∀ point ∈ Icc (0 : ℝ) 1, pathTotal limit point ≤ 1)
    (hgap : MathUE.HasClockGapOn (pathTotal limit) (Icc 0 1))
    (hsourceBounded : ∀ index, HasUnitBoundedTotalMass (paths index))
    (hweak : WeaklyConvergesAbsorptionPathsToCadlag paths limit)
    {time : ℝ} (htime : time ∈ pathTimes limit)
    (htimeOne : time ≠ 1)
    (coalition : {S : Finset ι // S.Nonempty})
    (hcard : coalition.1.card ≠ 1) :
    pathRightDerivative limit time coalition = 0 := by
  have htimeLtOne : time < 1 :=
    lt_of_le_of_ne htime.1.2 htimeOne
  let controlled := Classical.choice <|
    nonempty_cadlagPathTotalControlledRightSequence limit hclock hbound hgap
      htime htimeOne
  have hcardTwo : 2 ≤ coalition.1.card := by
    have hcardPos := coalition.2.card_pos
    omega
  let totalIncrement := fun rank ↦
    pathTotal limit (controlled.point rank) - time
  let cellAbsorption := fun rank ↦
    totalIncrement rank / (1 - time)
  let odds := fun rank ↦
    cellAbsorption rank / (1 - cellAbsorption rank)
  let slope := fun point : ℝ ↦
    (limit.value point coalition - limit.value time coalition) /
      (point - time)
  have hpointIcc (rank : ℕ) : controlled.point rank ∈ Icc (0 : ℝ) 1 :=
    ⟨htime.1.1.trans (controlled.point_mem rank).1.le,
      (controlled.point_mem rank).2.le⟩
  have htotalIncrementNonneg (rank : ℕ) : 0 ≤ totalIncrement rank := by
    unfold totalIncrement
    apply sub_nonneg.mpr
    calc
      time = pathTotal limit time := htime.2.symm
      _ ≤ pathTotal limit (controlled.point rank) :=
        monotoneOn_pathTotal limit htime.1 (hpointIcc rank)
          (controlled.point_mem rank).1.le
  have htotalIncrementUpper (rank : ℕ) :
      totalIncrement rank ≤ 2 * (controlled.point rank - time) := by
    unfold totalIncrement
    calc
      pathTotal limit (controlled.point rank) - time =
          pathTotal limit (controlled.point rank) - pathTotal limit time := by
        exact (congrArg
          (fun value : ℝ ↦ pathTotal limit (controlled.point rank) - value)
          htime.2).symm
      _ ≤ 2 * (controlled.point rank - time) :=
        controlled.pathTotal_sub_le_two_mul rank
  have hpointSub : Tendsto (fun rank ↦ controlled.point rank - time)
      atTop (nhds 0) := by
    have htimeConstant : Tendsto (fun _ : ℕ ↦ time) atTop (nhds time) :=
      tendsto_const_nhds
    simpa only [sub_self] using controlled.tendsto.sub htimeConstant
  have htotalIncrement : Tendsto totalIncrement atTop (nhds 0) := by
    have htwoConstant : Tendsto (fun _ : ℕ ↦ (2 : ℝ)) atTop (nhds 2) :=
      tendsto_const_nhds
    exact squeeze_zero htotalIncrementNonneg htotalIncrementUpper
      (by simpa using htwoConstant.mul hpointSub)
  have hcellAbsorption : Tendsto cellAbsorption atTop (nhds 0) := by
    simpa only [zero_div] using htotalIncrement.div_const (1 - time)
  have hcellAbsorptionHalf : ∀ᶠ rank in atTop,
      cellAbsorption rank < 1 / 2 :=
    hcellAbsorption.eventually_lt_const (by norm_num)
  have htotalPoint : Tendsto
      (fun rank ↦ pathTotal limit (controlled.point rank)) atTop
      (nhds time) := by
    have htimeConstant : Tendsto (fun _ : ℕ ↦ time) atTop (nhds time) :=
      tendsto_const_nhds
    have hadd := htotalIncrement.add htimeConstant
    convert hadd using 1
    · funext rank
      unfold totalIncrement
      ring_nf
    · ring_nf
  have htotalPointOne : ∀ᶠ rank in atTop,
      pathTotal limit (controlled.point rank) < 1 :=
    htotalPoint.eventually (Iio_mem_nhds htimeLtOne)
  have hodds : Tendsto odds atTop (nhds 0) := by
    have hratio := hcellAbsorption.div
      (tendsto_const_nhds.sub hcellAbsorption)
        (by norm_num : (1 : ℝ) - 0 ≠ 0)
    convert hratio using 1
    · funext rank
      simp only [odds, Pi.div_apply]
    · norm_num
  have hboundTendsto : Tendsto (fun rank ↦ 2 * odds rank) atTop
      (nhds 0) := by
    simpa using tendsto_const_nhds.mul hodds
  have hslopeNonneg (rank : ℕ) : 0 ≤ slope (controlled.point rank) := by
    unfold slope
    exact div_nonneg
      (sub_nonneg.mpr <| limit.monotone coalition htime.1
        (hpointIcc rank) (controlled.point_mem rank).1.le)
      (sub_nonneg.mpr (controlled.point_mem rank).1.le)
  have hslopeLe : ∀ᶠ rank in atTop,
      slope (controlled.point rank) ≤ 2 * odds rank := by
    filter_upwards [htotalPointOne, hcellAbsorptionHalf]
      with rank hpointOne hhalf
    have hcoordinate :=
      value_nonsingletonIncrement_le_absorptionOdds_mul_totalIncrement_of_weakLimit
        hclock hsourceBounded hweak htime htimeOne (hpointIcc rank)
        (controlled.point_not_jump rank) (controlled.point_mem rank).1
        hpointOne hhalf coalition hcardTwo
    have hcellNonneg : 0 ≤ cellAbsorption rank := by
      unfold cellAbsorption
      exact div_nonneg (htotalIncrementNonneg rank)
        (sub_nonneg.mpr htime.1.2)
    have hcellLtOne : cellAbsorption rank < 1 :=
      hhalf.trans (by norm_num)
    have hoddsNonneg : 0 ≤ odds rank := by
      unfold odds
      exact div_nonneg hcellNonneg (sub_nonneg.mpr hcellLtOne.le)
    have hdenominator : 0 < controlled.point rank - time :=
      sub_pos.mpr (controlled.point_mem rank).1
    unfold slope
    apply (div_le_iff₀ hdenominator).2
    change limit.value (controlled.point rank) coalition -
        limit.value time coalition ≤
      (2 * odds rank) * (controlled.point rank - time)
    exact hcoordinate.trans <|
      (mul_le_mul_of_nonneg_left (htotalIncrementUpper rank)
        hoddsNonneg).trans_eq (by ring)
  have hslopeTendsto : Tendsto
      (fun rank ↦ slope (controlled.point rank)) atTop (nhds 0) := by
    apply squeeze_zero'
    · exact Filter.Eventually.of_forall hslopeNonneg
    · exact hslopeLe
    · exact hboundTendsto
  let rightFilter := nhdsWithin time (Ioo time 1)
  letI : rightFilter.NeBot := left_nhdsWithin_Ioo_neBot htimeLtOne
  have hcontrolledRight : Tendsto controlled.point atTop rightFilter := by
    rw [tendsto_nhdsWithin_iff]
    exact ⟨controlled.tendsto,
      Filter.Eventually.of_forall controlled.point_mem⟩
  have hslopeEventuallyNonneg : ∀ᶠ point in rightFilter, 0 ≤ slope point := by
    filter_upwards [self_mem_nhdsWithin] with point hpoint
    have hpointMem : point ∈ Icc (0 : ℝ) 1 :=
      ⟨htime.1.1.trans hpoint.1.le, hpoint.2.le⟩
    unfold slope
    exact div_nonneg
      (sub_nonneg.mpr <| limit.monotone coalition htime.1 hpointMem
        hpoint.1.le)
      (sub_nonneg.mpr hpoint.1.le)
  have hslopeFrequentlyLe {tolerance : ℝ} (htolerance : 0 < tolerance) :
      ∃ᶠ point in rightFilter, slope point ≤ tolerance := by
    rw [Filter.frequently_iff]
    intro neighborhood hneighborhood
    have hpointNeighborhood : ∀ᶠ rank in atTop,
        controlled.point rank ∈ neighborhood :=
      hcontrolledRight hneighborhood
    have hslopeTolerance : ∀ᶠ rank in atTop,
        slope (controlled.point rank) ≤ tolerance :=
      (hslopeTendsto.eventually_lt_const htolerance).mono
        fun _ hlt ↦ hlt.le
    obtain ⟨rank, hrankNeighborhood, hrankSlope⟩ :=
      (hpointNeighborhood.and hslopeTolerance).exists
    exact ⟨controlled.point rank, hrankNeighborhood, hrankSlope⟩
  have hliminfLe : Filter.liminf slope rightFilter ≤ 0 := by
    refine le_of_forall_pos_le_add fun tolerance htolerance ↦ ?_
    simpa only [zero_add] using
      (liminf_le_of_frequently_le (hslopeFrequentlyLe htolerance)
        ⟨0, hslopeEventuallyNonneg⟩)
  have hslopeCobounded :
      rightFilter.IsCoboundedUnder (fun first second : ℝ ↦ first ≥ second)
        slope := by
    change (Filter.map slope rightFilter).IsCobounded
      (fun first second : ℝ ↦ first ≥ second)
    refine ⟨1, ?_⟩
    intro lower hlower
    change ∀ᶠ point in rightFilter, slope point ≥ lower at hlower
    obtain ⟨point, hpointOne, hpointLower⟩ :=
      ((hslopeFrequentlyLe zero_lt_one).and_eventually hlower).exists
    exact hpointLower.trans hpointOne
  have hliminfNonneg : 0 ≤ Filter.liminf slope rightFilter :=
    le_liminf_of_le hslopeCobounded hslopeEventuallyNonneg
  unfold pathRightDerivative
  change Filter.liminf slope rightFilter = 0
  exact le_antisymm hliminfLe hliminfNonneg

/-- Clock domination, unit boundedness, the clock-gap law, and weak source
approximation make every nonzero right derivative lie on a singleton. -/
theorem rightDerivative_supports_singletons_of_unitBoundedWeakLimit
    {paths : ℕ → AbsorptionPath (ι := ι)}
    {limit : CadlagPath (ι := ι)}
    (hclock : ∀ point ∈ Icc (0 : ℝ) 1, point ≤ pathTotal limit point)
    (hbound : ∀ point ∈ Icc (0 : ℝ) 1, pathTotal limit point ≤ 1)
    (hgap : MathUE.HasClockGapOn (pathTotal limit) (Icc 0 1))
    (hsourceBounded : ∀ index, HasUnitBoundedTotalMass (paths index))
    (hweak : WeaklyConvergesAbsorptionPathsToCadlag paths limit) :
    ∀ time ∈ pathTimes limit, time ≠ 1 → ∀ coalition,
      pathRightDerivative limit time coalition ≠ 0 →
        coalition.1.card = 1 := by
  intro time htime htimeOne coalition hderivative
  by_contra hcard
  exact hderivative <|
    pathRightDerivative_eq_zero_of_nonsingleton_of_unitBoundedWeakLimit
      hclock hbound hgap hsourceBounded hweak htime htimeOne coalition hcard

end GameTheory.QuittingAbsorptionPath
