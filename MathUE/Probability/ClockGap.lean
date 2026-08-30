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
