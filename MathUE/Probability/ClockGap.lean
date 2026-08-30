/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Mathlib.MeasureTheory.Measure.Portmanteau
import Mathlib.Probability.CDF
import Mathlib.Topology.Algebra.Module.Cardinality
import Mathlib.Topology.Order.IsLUB

/-!
# Closed clock-gap laws

The clock-gap property says that a cumulative distribution function remains
constant until its current value is reached.  This file proves that the
property is closed under weak convergence of probability laws on the real
line.  The result is independent of game semantics.
-/

noncomputable section

namespace MathUE

open Filter MeasureTheory Set
open scoped Topology

/-- A cumulative clock remains constant strictly below its current value. -/
def HasClockGap (distribution : ℝ → ℝ) : Prop :=
  ∀ ⦃time later : ℝ⦄, time ≤ later → later < distribution time →
    distribution later = distribution time

/-- The clock-gap property restricted to a time domain. -/
def HasClockGapOn (distribution : ℝ → ℝ) (domain : Set ℝ) : Prop :=
  ∀ ⦃time later : ℝ⦄, time ∈ domain → later ∈ domain →
    time ≤ later → later < distribution time →
      distribution later = distribution time

namespace HasClockGap

/-- A sequence of continuity points approaching one clock time from the
right, with CDF overshoot controlled by twice the clock displacement. -/
structure ControlledRightSequence (distribution : ℝ → ℝ)
    (time ceiling : ℝ) where
  point : ℕ → ℝ
  point_mem : ∀ rank, point rank ∈ Ioo time ceiling
  continuousAt : ∀ rank, ContinuousAt distribution (point rank)
  tendsto : Tendsto point atTop (nhds time)
  distribution_sub_le_two_mul : ∀ rank,
    distribution (point rank) - distribution time ≤
      2 * (point rank - time)

/-- A monotone right-continuous clock is continuous at every fixed point
below a ceiling when it dominates the clock strictly below that ceiling. -/
theorem continuousAt_of_fixedPoint
    {distribution : ℝ → ℝ} {time ceiling : ℝ}
    (hmono : Monotone distribution)
    (hright : ∀ point,
      ContinuousWithinAt distribution (Ici point) point)
    (hdomination : ∀ point, point < ceiling → point ≤ distribution point)
    (htime : time < ceiling) (hfixed : distribution time = time) :
    ContinuousAt distribution time := by
  rw [continuousAt_iff_continuous_left'_right']
  constructor
  · apply hmono.continuousWithinAt_Iio_iff_leftLim_eq.mpr
    apply le_antisymm
    · exact hmono.leftLim_le le_rfl
    · by_contra hnot
      have hlt : Function.leftLim distribution time < time := by
        exact (lt_of_not_ge hnot).trans_eq hfixed
      let before := (Function.leftLim distribution time + time) / 2
      have hleftBefore : Function.leftLim distribution time < before := by
        dsimp only [before]
        linarith
      have hbeforeTime : before < time := by
        dsimp only [before]
        linarith
      have hbeforeDomination : before ≤ distribution before :=
        hdomination before (hbeforeTime.trans htime)
      have hbeforeLeft : distribution before ≤
          Function.leftLim distribution time :=
        hmono.le_leftLim hbeforeTime
      linarith
  · exact (hright time).mono Ioi_subset_Ici_self

/-- Clock gaps produce arbitrarily close right continuity points whose CDF
overshoot is at most twice their displacement from a fixed clock time. -/
theorem nonempty_controlledRightSequence
    {distribution : ℝ → ℝ} {time ceiling : ℝ}
    (hgap : HasClockGap distribution)
    (hmono : Monotone distribution)
    (hright : ∀ point,
      ContinuousWithinAt distribution (Ici point) point)
    (hdomination : ∀ point, point < ceiling → point ≤ distribution point)
    (hbounded : ∀ point, distribution point ≤ ceiling)
    (htime : time < ceiling) (hfixed : distribution time = time) :
    Nonempty (ControlledRightSequence distribution time ceiling) := by
  let scale := fun rank : ℕ ↦ (1 : ℝ) / ((rank : ℝ) + 1)
  let probe := fun rank : ℕ ↦
    time + (ceiling - time) / 2 * scale rank
  have hscale_pos (rank : ℕ) : 0 < scale rank := by
    dsimp only [scale]
    positivity
  have hscale_le_one (rank : ℕ) : scale rank ≤ 1 := by
    dsimp only [scale]
    rw [div_le_one (by positivity : (0 : ℝ) < (rank : ℝ) + 1)]
    norm_num
  have hprobe_mem (rank : ℕ) : probe rank ∈ Ioo time ceiling := by
    constructor <;> dsimp only [probe]
    · have := hscale_pos rank
      nlinarith
    · have := hscale_le_one rank
      nlinarith
  have hprobe_tendsto : Tendsto probe atTop (nhds time) := by
    have hscale_tendsto : Tendsto scale atTop (nhds 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    simpa only [probe, mul_zero, add_zero] using
      tendsto_const_nhds.add (tendsto_const_nhds.mul hscale_tendsto)
  have hprobe_within : Tendsto probe atTop (nhdsWithin time (Ici time)) := by
    rw [tendsto_nhdsWithin_iff]
    exact ⟨hprobe_tendsto,
      Filter.Eventually.of_forall fun rank ↦ (hprobe_mem rank).1.le⟩
  have hdistribution_probe : Tendsto (distribution ∘ probe) atTop
      (nhds time) := by
    rw [← hfixed]
    exact (hright time).tendsto.comp hprobe_within
  let discontinuities := {point : ℝ | ¬ContinuousAt distribution point}
  have hdense : Dense discontinuitiesᶜ :=
    hmono.countable_not_continuousAt.dense_compl ℝ
  have hexists (rank : ℕ) : ∃ point : ℝ,
      point ∈ Ioo time ceiling ∧
      ContinuousAt distribution point ∧
      probe rank ≤ point ∧ point ≤ distribution (probe rank) ∧
      distribution point - distribution time ≤ 2 * (point - time) := by
    by_cases heq : distribution (probe rank) = probe rank
    · refine ⟨probe rank, hprobe_mem rank,
        continuousAt_of_fixedPoint hmono hright hdomination
          (hprobe_mem rank).2 heq,
        le_rfl, heq.ge, ?_⟩
      rw [heq, hfixed]
      linarith [hprobe_mem rank |>.1]
    · have hprobe_lt : probe rank < distribution (probe rank) :=
        lt_of_le_of_ne
          (hdomination (probe rank) (hprobe_mem rank).2) (Ne.symm heq)
      let lower := max (probe rank)
        ((distribution (probe rank) + time) / 2)
      have hlower_lt : lower < distribution (probe rank) := by
        rw [max_lt_iff]
        constructor
        · exact hprobe_lt
        · linarith [hprobe_mem rank |>.1]
      obtain ⟨point, hpointContinuous, hpoint⟩ :=
        hdense.exists_mem_open isOpen_Ioo (nonempty_Ioo.mpr hlower_lt)
      have hcontinuous : ContinuousAt distribution point := by
        simpa only [discontinuities, mem_compl_iff, mem_setOf_eq, not_not] using
          hpointContinuous
      have hprobe_point : probe rank < point :=
        (le_max_left _ _).trans_lt hpoint.1
      have hpoint_time : time < point :=
        (hprobe_mem rank).1.trans hprobe_point
      have hpoint_ceiling : point < ceiling :=
        hpoint.2.trans_le (hbounded (probe rank))
      have hdistribution_point :
          distribution point = distribution (probe rank) :=
        hgap hprobe_point.le hpoint.2
      refine ⟨point, ⟨hpoint_time, hpoint_ceiling⟩, hcontinuous,
        hprobe_point.le, hpoint.2.le, ?_⟩
      rw [hdistribution_point, hfixed]
      have hmidpoint :
          (distribution (probe rank) + time) / 2 < point :=
        (le_max_right _ _).trans_lt hpoint.1
      linarith
  choose point hpoint using hexists
  refine ⟨{
    point := point
    point_mem := fun rank ↦ (hpoint rank).1
    continuousAt := fun rank ↦ (hpoint rank).2.1
    tendsto := ?_
    distribution_sub_le_two_mul := fun rank ↦ (hpoint rank).2.2.2.2
  }⟩
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le hprobe_tendsto
    hdistribution_probe
  · exact fun rank ↦ (hpoint rank).2.2.1
  · exact fun rank ↦ (hpoint rank).2.2.2.1

/-- A global clock-gap law restricts to every time domain. -/
theorem hasClockGapOn {distribution : ℝ → ℝ}
    (hgap : HasClockGap distribution) (domain : Set ℝ) :
    HasClockGapOn distribution domain := by
  intro time later _ _ htimeLater hlater
  exact hgap htimeLater hlater

/-- Weak convergence gives pointwise CDF convergence at every continuity
point of the limiting CDF. -/
theorem cdf_tendsto_of_tendsto_of_continuousAt
    {index : Type*} {limitFilter : Filter index}
    {laws : index → ProbabilityMeasure ℝ} {law : ProbabilityMeasure ℝ}
    (hlaw : Tendsto laws limitFilter (𝓝 law)) {time : ℝ}
    (hcontinuous : ContinuousAt
      (ProbabilityTheory.cdf (law : Measure ℝ)) time) :
    Tendsto (fun rank ↦ ProbabilityTheory.cdf (laws rank : Measure ℝ) time)
      limitFilter
      (𝓝 (ProbabilityTheory.cdf (law : Measure ℝ) time)) := by
  have hsingletonENNReal : (law : Measure ℝ) {time} = 0 := by
    rw [← ProbabilityTheory.measure_cdf (law : Measure ℝ),
      StieltjesFunction.measure_singleton,
      hcontinuous.continuousWithinAt.leftLim_eq, sub_self,
      ENNReal.ofReal_zero]
  have hfrontier : (law : Measure ℝ) (frontier (Iic time)) = 0 := by
    simpa only [frontier_Iic] using hsingletonENNReal
  have hmeasure :=
    ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto'
      hlaw hfrontier
  have hreal := (ENNReal.tendsto_toReal
    (measure_ne_top (law : Measure ℝ) (Iic time))).comp hmeasure
  change Tendsto (fun rank ↦
      ((laws rank : Measure ℝ) (Iic time)).toReal) limitFilter
    (𝓝 (((law : Measure ℝ) (Iic time)).toReal)) at hreal
  simpa only [ProbabilityTheory.cdf_eq_real, measureReal_def] using hreal

/-- The clock-gap property of real probability laws is closed under weak
convergence. -/
theorem cdf_of_tendsto
    {index : Type*} {limitFilter : Filter index} [limitFilter.NeBot]
    {laws : index → ProbabilityMeasure ℝ} {law : ProbabilityMeasure ℝ}
    (hlaw : Tendsto laws limitFilter (𝓝 law))
    (hsource : ∀ rank,
      HasClockGap (ProbabilityTheory.cdf (laws rank : Measure ℝ))) :
    HasClockGap (ProbabilityTheory.cdf (law : Measure ℝ)) := by
  intro time later htimeLater hlaterGap
  rcases htimeLater.eq_or_lt with rfl | htimeLater
  · rfl
  let distribution := ProbabilityTheory.cdf (law : Measure ℝ)
  let discontinuities := {point : ℝ | ¬ContinuousAt distribution point}
  have hdense : Dense discontinuitiesᶜ :=
    (ProbabilityTheory.monotone_cdf (law : Measure ℝ))
      |>.countable_not_continuousAt.dense_compl ℝ
  obtain ⟨upper, hupperContinuous, hupper⟩ :=
    hdense.exists_between hlaterGap
  have hupperContinuous' : ContinuousAt distribution upper := by
    simpa only [discontinuities, mem_compl_iff, mem_setOf_eq, not_not] using
      hupperContinuous
  have htimeUpper : time < upper := htimeLater.trans hupper.1
  obtain ⟨approach, _happroachStrictAnti, happroachMem,
      happroachTendsto⟩ :=
    hdense.exists_seq_strictAnti_tendsto_of_lt htimeUpper
  have heq (stage : ℕ) : distribution upper = distribution (approach stage) := by
    have happroachContinuous : ContinuousAt distribution (approach stage) := by
      simpa only [discontinuities, mem_compl_iff, mem_setOf_eq, not_not] using
        (happroachMem stage).2
    have hlower := cdf_tendsto_of_tendsto_of_continuousAt
      hlaw happroachContinuous
    have hupperLimit := cdf_tendsto_of_tendsto_of_continuousAt
      hlaw hupperContinuous'
    have hstrict : upper < distribution (approach stage) :=
      hupper.2.trans_le <|
        ProbabilityTheory.monotone_cdf (law : Measure ℝ)
          (happroachMem stage).1.1.le
    have heventually : ∀ᶠ rank in limitFilter,
        ProbabilityTheory.cdf (laws rank : Measure ℝ) upper =
          ProbabilityTheory.cdf (laws rank : Measure ℝ) (approach stage) := by
      filter_upwards [hlower.eventually_const_lt hstrict] with rank hrank
      exact hsource rank (happroachMem stage).1.2.le hrank
    have hupperToLower : Tendsto (fun rank ↦
        ProbabilityTheory.cdf (laws rank : Measure ℝ) upper) limitFilter
        (𝓝 (distribution (approach stage))) :=
      hlower.congr' <| heventually.mono fun _ hrank ↦ hrank.symm
    exact tendsto_nhds_unique hupperLimit hupperToLower
  have hright : Tendsto (fun stage ↦ distribution (approach stage)) atTop
      (𝓝 (distribution time)) := by
    have happroachWithin : Tendsto approach atTop (𝓝[Set.Ici time] time) :=
      tendsto_nhdsWithin_iff.mpr ⟨happroachTendsto,
        Filter.Eventually.of_forall fun stage ↦ (happroachMem stage).1.1.le⟩
    exact (ProbabilityTheory.cdf (law : Measure ℝ)).right_continuous time
      |>.tendsto.comp happroachWithin
  have hupperEq : distribution upper = distribution time := by
    have hconstant : Tendsto (fun _ : ℕ ↦ distribution upper) atTop
        (𝓝 (distribution upper)) := tendsto_const_nhds
    have hconstantLimit : Tendsto (fun _ : ℕ ↦ distribution upper) atTop
        (𝓝 (distribution time)) :=
      hright.congr' <| Filter.Eventually.of_forall fun stage ↦ (heq stage).symm
    exact tendsto_nhds_unique hconstant hconstantLimit
  apply le_antisymm
  · exact (ProbabilityTheory.monotone_cdf (law : Measure ℝ) hupper.1.le).trans_eq
      hupperEq
  · exact ProbabilityTheory.monotone_cdf (law : Measure ℝ) htimeLater.le

end HasClockGap

end MathUE
