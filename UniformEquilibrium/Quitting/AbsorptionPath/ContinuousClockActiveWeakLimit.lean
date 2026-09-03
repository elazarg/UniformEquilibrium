/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.AbsorptionPath.PositiveSingletonBoundaryCellEstimate
import UniformEquilibrium.Quitting.AbsorptionPath.ContinuousClockLowerBoundWeakLimit
import UniformEquilibrium.Quitting.AbsorptionPath.SequentialPerfectionWeakLimit

/-!
# Active continuous-clock perfection under bounded weak limits

This module transports the positive-singleton boundary-cell estimate through
weak convergence.  A fixed later continuity point generates the second source
boundary; the first source boundary is the literal total-mass boundary at the
limit clock time.
-/

noncomputable section

namespace GameTheory.QuittingAbsorptionPath

open Filter Set
open scoped Topology

variable {ι : Type} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] [DecidableEq ι] in
/-- A positive lower right derivative forces strict coordinate increase along
every sequence approaching through the open right neighborhood. -/
theorem CadlagPath.eventually_value_lt_of_pathRightDerivative_pos
    (path : CadlagPath (ι := ι))
    {time : ℝ} (htime : time ∈ Icc (0 : ℝ) 1)
    (coalition : {S : Finset ι // S.Nonempty})
    (hderivative : 0 < pathRightDerivative path time coalition)
    (points : ℕ → ℝ)
    (hpoints : Tendsto points atTop (nhdsWithin time (Ioo time 1))) :
    ∀ᶠ index in atTop,
      path.value time coalition < path.value (points index) coalition := by
  let rightFilter := nhdsWithin time (Ioo time 1)
  let quotient := fun point : ℝ ↦
    (path.value point coalition - path.value time coalition) /
      (point - time)
  have hnonnegative : ∀ᶠ point in rightFilter, 0 ≤ quotient point := by
    filter_upwards [self_mem_nhdsWithin] with point hpoint
    have hpointMem : point ∈ Icc (0 : ℝ) 1 :=
      ⟨htime.1.trans hpoint.1.le, hpoint.2.le⟩
    exact div_nonneg
      (sub_nonneg.mpr (path.monotone coalition htime hpointMem hpoint.1.le))
      (sub_nonneg.mpr hpoint.1.le)
  have hpositive : ∀ᶠ point in rightFilter, 0 < quotient point := by
    apply eventually_lt_of_lt_liminf
    · change 0 < Filter.liminf quotient rightFilter at hderivative
      exact hderivative
    · exact isBoundedUnder_of_eventually_ge hnonnegative
  have hpointMem : ∀ᶠ index in atTop, points index ∈ Ioo time 1 :=
    hpoints self_mem_nhdsWithin
  have hpointPositive : ∀ᶠ index in atTop, 0 < quotient (points index) :=
    hpoints hpositive
  filter_upwards [hpointMem, hpointPositive] with index hmem hquotient
  have hincrement : 0 <
      path.value (points index) coalition - path.value time coalition := by
    have hdenominator : 0 < points index - time := sub_pos.mpr hmem.1
    exact ((div_pos_iff.mp hquotient).resolve_right fun hnegative ↦
      (not_lt_of_ge hdenominator.le hnegative.2).elim).1
  linarith

/-- Payoffs immediately before the mixed source boundaries converge to the
payoff at the nonterminal limit clock time. -/
theorem LimitClockBoundarySourceApproximation.preBoundaryPayoff_tendsto
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    {paths : ℕ → AbsorptionPath (ι := ι)}
    {limit : AbsorptionPath (ι := ι)} {time : ℝ}
    (approximation : LimitClockBoundarySourceApproximation paths limit time)
    (hlimitBounded : HasUnitBoundedTotalMass limit)
    (hweak : WeaklyConvergesAbsorptionPaths paths limit)
    (htime : time ∈ pathTimes limit.1) (htimeOne : time ≠ 1)
    (player : ι) :
    Tendsto (fun index ↦ absorptionPathPreBoundaryPayoff reward
      (paths index) (approximation.sourceTimes index) player) atTop
      (nhds (absorptionPathPayoff reward limit time player)) := by
  have hnotJump : time ∉ pathJumps limit.1 := by
    intro hjump
    have hstrict := lt_pathTotal_of_mem_pathJumps limit hjump
    rw [htime.2] at hstrict
    exact (lt_irrefl time hstrict).elim
  have hleftEq (coalition : {S : Finset ι // S.Nonempty}) :
      limit.1.leftValue time coalition = limit.1.value time coalition := by
    have hjumpZero : pathJump limit.1 time coalition = 0 := by
      by_contra hnonzero
      exact hnotJump ⟨htime.1, coalition, hnonzero⟩
    unfold pathJump at hjumpZero
    linarith
  have hendpoint := hweak.tendsto_value_one hlimitBounded
  have hnumerator : Tendsto (fun index ↦
      ∑ coalition : {S : Finset ι // S.Nonempty},
        ((paths index).1.value 1 coalition -
          (paths index).1.leftValue
            (approximation.sourceTimes index) coalition) *
              reward coalition player) atTop
      (nhds (∑ coalition : {S : Finset ι // S.Nonempty},
        (limit.1.value 1 coalition - limit.1.value time coalition) *
          reward coalition player)) := by
    apply tendsto_finsetSum
    intro coalition _
    exact ((tendsto_pi_nhds.mp hendpoint coalition).sub
      (approximation.leftValues_tendsto coalition)).mul_const _
  have hdenominator : Tendsto
      (fun index ↦ 1 - approximation.sourceTimes index) atTop
      (nhds (1 - time)) :=
    tendsto_const_nhds.sub approximation.times_tendsto
  have hquotient := hnumerator.div hdenominator
    (sub_ne_zero.mpr htimeOne.symm)
  change Tendsto (fun index ↦ _ / (1 - approximation.sourceTimes index))
    atTop _ at hquotient
  have hpre : Tendsto (fun index ↦ absorptionPathPreBoundaryPayoff reward
      (paths index) (approximation.sourceTimes index) player) atTop
      (nhds (absorptionPathPreBoundaryPayoff reward limit time player)) := by
    simpa only [absorptionPathPreBoundaryPayoff, hleftEq]
      using hquotient
  rw [congrFun
    (absorptionPathPreBoundaryPayoff_eq_absorptionPathPayoff_of_pathTime_not_jump
      reward limit htime htimeOne hnotJump) player] at hpre
  exact hpre

/-- A later continuity point with a strict singleton increase yields the
corresponding active-clock upper estimate in the weak limit. -/
theorem absorptionPathPayoff_le_singletonReward_add_six_mul_boundaryRatio_of_weakLimit
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (errors : ℕ → ℝ) (paths : ℕ → AbsorptionPath (ι := ι))
    (limit : AbsorptionPath (ι := ι)) (player : ι)
    (hsourceBounded : ∀ index, HasUnitBoundedTotalMass (paths index))
    (hlimitBounded : HasUnitBoundedTotalMass limit)
    (herrors : Tendsto errors atTop (nhds 0))
    (hweak : WeaklyConvergesAbsorptionPaths paths limit)
    (hperfect : ∀ index,
      IsPlayerSequentiallyPerfectAbsorptionPath reward (paths index)
        player (errors index))
    {time later : ℝ} (htime : time ∈ pathTimes limit.1)
    (htimeOne : time ≠ 1) (hlater : later ∈ Icc (0 : ℝ) 1)
    (hlaterNotJump : later ∉ pathJumps limit.1)
    (htimeLater : time < later)
    (hlaterTotal : pathTotal limit.1 later < 1)
    (hincrement : limit.1.value time
        ⟨{player}, Finset.singleton_nonempty player⟩ <
      limit.1.value later
        ⟨{player}, Finset.singleton_nonempty player⟩) :
    absorptionPathPayoff reward limit time player ≤
      reward (quittingSingletonTerminal player) player +
        6 * quittingRewardBound reward *
          ((pathTotal limit.1 later - time) / (1 - time)) := by
  let approximation := Classical.choice
    (nonempty_limitClockBoundarySourceApproximation hsourceBounded hweak
      htime htimeOne)
  let stopTimes := fun index ↦ pathTotal (paths index).1 later
  have hlaterValues := hweak later hlater hlaterNotJump
  have hstopTimes : Tendsto stopTimes atTop
      (nhds (pathTotal limit.1 later)) := by
    unfold stopTimes pathTotal
    exact tendsto_finsetSum Finset.univ fun coalition _ ↦
      tendsto_pi_nhds.mp hlaterValues coalition
  have hstopMem (index : ℕ) : stopTimes index ∈ Icc (0 : ℝ) 1 :=
    ⟨hlater.1.trans ((paths index).property.1 later hlater),
      hsourceBounded index later hlater⟩
  have hstopBoundary (index : ℕ) :
      stopTimes index ∈ partitionBoundaryTimes (paths index) :=
    pathTotal_mem_partitionBoundaryTimes (paths index)
      (hsourceBounded index) hlater
  have htimeTotal : time < pathTotal limit.1 later :=
    htimeLater.trans_le (limit.property.1 later hlater)
  have hordered : ∀ᶠ index in atTop,
      approximation.sourceTimes index < stopTimes index :=
    approximation.times_tendsto.eventually_lt hstopTimes htimeTotal
  have hstopNonterminal : ∀ᶠ index in atTop, stopTimes index < 1 :=
    hstopTimes.eventually (Iio_mem_nhds hlaterTotal)
  let singleton : {S : Finset ι // S.Nonempty} :=
    ⟨{player}, Finset.singleton_nonempty player⟩
  have hlaterSingleton : Tendsto (fun index ↦
      (paths index).1.value later singleton) atTop
      (nhds (limit.1.value later singleton)) :=
    tendsto_pi_nhds.mp hlaterValues singleton
  have hsourceIncrease : ∀ᶠ index in atTop,
      (paths index).1.leftValue (approximation.sourceTimes index) singleton <
        (paths index).1.value later singleton :=
    (approximation.leftValues_tendsto singleton).eventually_lt
      hlaterSingleton hincrement
  have hboundaryIncrease : ∀ᶠ index in atTop,
      (paths index).1.leftValue (approximation.sourceTimes index) singleton <
        (paths index).1.leftValue (stopTimes index) singleton := by
    filter_upwards [hsourceIncrease] with index hstrict
    exact hstrict.trans_le
      (value_le_leftValue_at_pathTotal_of_unitBounded (paths index)
        (hsourceBounded index) hlater singleton)
  have hcellRatio : Tendsto (fun index ↦
      pathCellAbsorption (paths index).1
        (approximation.sourceTimes index) (stopTimes index)) atTop
      (nhds ((pathTotal limit.1 later - time) / (1 - time))) := by
    have hquotient := (hstopTimes.sub approximation.times_tendsto).div
      (tendsto_const_nhds.sub approximation.times_tendsto)
        (sub_ne_zero.mpr htimeOne.symm)
    apply hquotient.congr'
    filter_upwards [] with index
    simp only [Pi.div_apply]
    unfold pathCellAbsorption
    rw [pathLeftTotal_eq_of_mem_partitionBoundaryTimes (paths index)
        (approximation.source_boundary index),
      pathLeftTotal_eq_of_mem_partitionBoundaryTimes (paths index)
        (hstopBoundary index)]
  have hsourceBound : ∀ᶠ index in atTop,
      absorptionPathPreBoundaryPayoff reward (paths index)
          (approximation.sourceTimes index) player ≤
        reward (quittingSingletonTerminal player) player + errors index +
          6 * quittingRewardBound reward *
            pathCellAbsorption (paths index).1
              (approximation.sourceTimes index) (stopTimes index) := by
    filter_upwards [hordered, hstopNonterminal, hboundaryIncrease]
      with index horder hstopOne hpositive
    exact
      absorptionPathPreBoundaryPayoff_le_singletonReward_add_error_add_six_mul_cellAbsorption
        reward (paths index) (hsourceBounded index) player (errors index)
        (hperfect index) (approximation.source_boundary index)
        (hstopBoundary index) horder hstopOne hpositive
  have hpre := approximation.preBoundaryPayoff_tendsto reward
    hlimitBounded hweak htime htimeOne player
  have hright : Tendsto (fun index ↦
      reward (quittingSingletonTerminal player) player + errors index +
        6 * quittingRewardBound reward *
          pathCellAbsorption (paths index).1
            (approximation.sourceTimes index) (stopTimes index)) atTop
      (nhds (reward (quittingSingletonTerminal player) player +
        6 * quittingRewardBound reward *
          ((pathTotal limit.1 later - time) / (1 - time)))) := by
    simpa only [add_zero] using (tendsto_const_nhds.add herrors).add
      (tendsto_const_nhds.mul hcellRatio)
  exact le_of_tendsto_of_tendsto hpre hright hsourceBound

/-- The active upper continuous-clock sequential-perfection inequality is
closed under unit-bounded weak convergence. -/
theorem playerContinuousClockUpperBound_of_unitBoundedWeakLimit
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (errors : ℕ → ℝ) (paths : ℕ → AbsorptionPath (ι := ι))
    (limit : AbsorptionPath (ι := ι)) (player : ι)
    (hsourceBounded : ∀ index, HasUnitBoundedTotalMass (paths index))
    (hlimitBounded : HasUnitBoundedTotalMass limit)
    (herrors : Tendsto errors atTop (nhds 0))
    (hweak : WeaklyConvergesAbsorptionPaths paths limit)
    (hperfect : ∀ index,
      IsPlayerSequentiallyPerfectAbsorptionPath reward (paths index)
        player (errors index)) :
    ∀ time ∈ pathTimes limit.1, time ≠ 1 →
      pathRightDerivative limit.1 time
          ⟨{player}, Finset.singleton_nonempty player⟩ > 0 →
        absorptionPathPayoff reward limit time player ≤
          reward ⟨{player}, Finset.singleton_nonempty player⟩ player := by
  intro time htime htimeOne hderivative
  have htimeLtOne : time < 1 :=
    lt_of_le_of_ne htime.1.2 htimeOne
  have hdense : Dense ((pathJumps limit.1)ᶜ) :=
    (countable_pathJumps limit.1).dense_compl ℝ
  obtain ⟨approach, _hstrictAnti, happroachMem, happroachTendsto⟩ :=
    hdense.exists_seq_strictAnti_tendsto_of_lt (α := ℝ) htimeLtOne
  have happroachWithin : Tendsto approach atTop
      (nhdsWithin time (Ioo time 1)) :=
    tendsto_nhdsWithin_iff.2 ⟨happroachTendsto,
      Filter.Eventually.of_forall fun index ↦ (happroachMem index).1⟩
  let singleton : {S : Finset ι // S.Nonempty} :=
    ⟨{player}, Finset.singleton_nonempty player⟩
  have hincrement : ∀ᶠ index in atTop,
      limit.1.value time singleton <
        limit.1.value (approach index) singleton :=
    limit.1.eventually_value_lt_of_pathRightDerivative_pos htime.1
      singleton (by simpa only [singleton] using hderivative)
      approach happroachWithin
  have happroachIcc (index : ℕ) : approach index ∈ Icc (0 : ℝ) 1 :=
    ⟨htime.1.1.trans (happroachMem index).1.1.le,
      (happroachMem index).1.2.le⟩
  have happroachForRightContinuity : Tendsto approach atTop
      (nhdsWithin time (Icc time 1)) :=
    happroachWithin.mono_right
      (nhdsWithin_mono time Ioo_subset_Icc_self)
  have hcoordinateTendsto (coalition : {S : Finset ι // S.Nonempty}) :
      Tendsto (fun index ↦ limit.1.value (approach index) coalition) atTop
        (nhds (limit.1.value time coalition)) :=
    (limit.1.right_continuous coalition time htime.1).comp
      happroachForRightContinuity
  have htotalTendsto : Tendsto
      (fun index ↦ pathTotal limit.1 (approach index)) atTop
      (nhds time) := by
    rw [← htime.2]
    unfold pathTotal
    exact tendsto_finsetSum Finset.univ fun coalition _ ↦
      hcoordinateTendsto coalition
  have htotalLtOne : ∀ᶠ index in atTop,
      pathTotal limit.1 (approach index) < 1 :=
    htotalTendsto.eventually (Iio_mem_nhds htimeLtOne)
  have hbound : ∀ᶠ index in atTop,
      absorptionPathPayoff reward limit time player ≤
        reward (quittingSingletonTerminal player) player +
          6 * quittingRewardBound reward *
            ((pathTotal limit.1 (approach index) - time) /
              (1 - time)) := by
    filter_upwards [hincrement, htotalLtOne]
      with index hstrict htotal
    exact
      absorptionPathPayoff_le_singletonReward_add_six_mul_boundaryRatio_of_weakLimit
        reward errors paths limit player hsourceBounded hlimitBounded herrors
        hweak hperfect htime htimeOne (happroachIcc index)
        (happroachMem index).2 (happroachMem index).1.1 htotal hstrict
  have hratio : Tendsto (fun index ↦
      (pathTotal limit.1 (approach index) - time) / (1 - time)) atTop
      (nhds 0) := by
    simpa only [sub_self, zero_div] using
      (htotalTendsto.sub (tendsto_const_nhds :
        Tendsto (fun _ : ℕ ↦ time) atTop (nhds time))).div_const (1 - time)
  have hright : Tendsto (fun index ↦
      reward (quittingSingletonTerminal player) player +
        6 * quittingRewardBound reward *
          ((pathTotal limit.1 (approach index) - time) / (1 - time))) atTop
      (nhds (reward (quittingSingletonTerminal player) player)) := by
    simpa only [mul_zero, add_zero] using tendsto_const_nhds.add
      (tendsto_const_nhds.mul hratio)
  have hlimit := le_of_tendsto_of_tendsto tendsto_const_nhds hright hbound
  simpa [quittingSingletonTerminal] using hlimit

/-- Under a supplied literal source realization of every limit jump, all
three playerwise sequential-perfection clauses survive a unit-bounded weak
limit.  The two continuous-clock clauses require no extra localization data. -/
theorem playerSequentiallyPerfect_of_sourceApproximatedUnitBoundedWeakLimit
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (errors : ℕ → ℝ) (paths : ℕ → AbsorptionPath (ι := ι))
    (limit : AbsorptionPath (ι := ι)) (player : ι)
    (hsourceBounded : ∀ index, HasUnitBoundedTotalMass (paths index))
    (hlimitBounded : HasUnitBoundedTotalMass limit)
    (herrors : Tendsto errors atTop (nhds 0))
    (hweak : WeaklyConvergesAbsorptionPaths paths limit)
    (hjumps : HasSourceApproximationsForLimitJumps paths limit)
    (hperfect : ∀ index,
      IsPlayerSequentiallyPerfectAbsorptionPath reward (paths index)
        player (errors index)) :
    IsPlayerSequentiallyPerfectAbsorptionPath reward limit player 0 := by
  refine ⟨playerJumpRowsPerfect_of_sourceApproximatedWeakLimit reward errors
    paths limit player hlimitBounded herrors hweak hjumps hperfect, ?_⟩
  intro time htime htimeOne
  constructor
  · simpa using
      playerContinuousClockLowerBound_of_unitBoundedWeakLimit reward errors
        paths limit player hsourceBounded hlimitBounded herrors hweak hperfect
        time htime htimeOne
  · intro hderivative
    simpa using
      playerContinuousClockUpperBound_of_unitBoundedWeakLimit reward errors
        paths limit player hsourceBounded hlimitBounded herrors hweak hperfect
        time htime htimeOne hderivative

end GameTheory.QuittingAbsorptionPath
