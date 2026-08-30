/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Mathlib.Topology.Algebra.Module.Cardinality
import UniformEquilibrium.Quitting.AbsorptionPath.ChronologicalMarkedRootSequenceJump
import UniformEquilibrium.Quitting.Root.SimplexCoalitionMass

/-!
# Null windows and jump limits for chronological marked laws

Every chronological probability law admits shrinking open clock windows about
one prescribed time whose boundary fibers are null.  Weak convergence then
gives literal convergence of the total and coalition-marked window masses.
The decoded path also has no jump at time one whenever it satisfies A1.

These are generic probability and path facts.  They do not select a finite
source stage or assert absorption-path axiom A3.
-/

noncomputable section

namespace GameTheory.QuittingAbsorptionPath

open Filter MeasureTheory Set
open scoped ENNReal Topology

variable {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]
variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}

/-- Shrinking open clock windows about one time, with both boundary clock
fibers null under the fixed chronological law. -/
structure QuittingChronologicalNullWindowSequence
    (law : ProbabilityMeasure (QuittingChronologicalEvent reward))
    (time : ℝ) where
  lower : ℕ → ℝ
  upper : ℕ → ℝ
  lower_mem : ∀ rank : ℕ,
    lower rank ∈ Ioo (time - 1 / ((rank : ℝ) + 1)) time
  upper_mem : ∀ rank : ℕ,
    upper rank ∈ Ioo time (time + 1 / ((rank : ℝ) + 1))
  lower_fiber_null : ∀ rank,
    (law : Measure (QuittingChronologicalEvent reward))
      {event | chronologicalEventClock event = lower rank} = 0
  upper_fiber_null : ∀ rank,
    (law : Measure (QuittingChronologicalEvent reward))
      {event | chronologicalEventClock event = upper rank} = 0

omit [DecidableEq ι] [Nonempty ι] in
/-- Null clock fibers are dense, so every chronological law has a shrinking
null-boundary window sequence about every real time. -/
theorem nonempty_chronologicalNullWindowSequence
    (law : ProbabilityMeasure (QuittingChronologicalEvent reward))
    (time : ℝ) :
    Nonempty (QuittingChronologicalNullWindowSequence law time) := by
  let atoms : Set ℝ := {point | 0 <
    (law : Measure (QuittingChronologicalEvent reward))
      {event | chronologicalEventClock event = point}}
  have hatoms : atoms.Countable := by
    exact Measure.countable_meas_level_set_pos
      continuous_chronologicalEventClock.measurable
  have hdense : Dense atomsᶜ := hatoms.dense_compl ℝ
  have hscale (rank : ℕ) : 0 < (1 : ℝ) / ((rank : ℝ) + 1) := by
    positivity
  have hlower (rank : ℕ) : ∃ point ∈ atomsᶜ,
      point ∈ Ioo (time - 1 / ((rank : ℝ) + 1)) time := by
    apply hdense.exists_mem_open isOpen_Ioo
    exact nonempty_Ioo.mpr (by linarith [hscale rank])
  have hupper (rank : ℕ) : ∃ point ∈ atomsᶜ,
      point ∈ Ioo time (time + 1 / ((rank : ℝ) + 1)) := by
    apply hdense.exists_mem_open isOpen_Ioo
    exact nonempty_Ioo.mpr (by linarith [hscale rank])
  choose lower hlowerAtom hlowerMem using hlower
  choose upper hupperAtom hupperMem using hupper
  refine ⟨{
    lower := lower
    upper := upper
    lower_mem := hlowerMem
    upper_mem := hupperMem
    lower_fiber_null := ?_
    upper_fiber_null := ?_
  }⟩
  · intro rank
    apply bot_unique
    exact not_lt.mp (hlowerAtom rank)
  · intro rank
    apply bot_unique
    exact not_lt.mp (hupperAtom rank)

namespace QuittingChronologicalNullWindowSequence

variable
    {law : ProbabilityMeasure (QuittingChronologicalEvent reward)}
    {time : ℝ}

omit [DecidableEq ι] [Nonempty ι] in
theorem lower_lt_time
    (windows : QuittingChronologicalNullWindowSequence law time)
    (rank : ℕ) : windows.lower rank < time :=
  (windows.lower_mem rank).2

omit [DecidableEq ι] [Nonempty ι] in
theorem time_lt_upper
    (windows : QuittingChronologicalNullWindowSequence law time)
    (rank : ℕ) : time < windows.upper rank :=
  (windows.upper_mem rank).1

omit [DecidableEq ι] [Nonempty ι] in
theorem lower_lt_upper
    (windows : QuittingChronologicalNullWindowSequence law time)
    (rank : ℕ) : windows.lower rank < windows.upper rank :=
  (windows.lower_lt_time rank).trans (windows.time_lt_upper rank)

omit [DecidableEq ι] [Nonempty ι] in
theorem lower_tendsto
    (windows : QuittingChronologicalNullWindowSequence law time) :
    Tendsto windows.lower atTop (nhds time) := by
  simpa only [sub_zero] using tendsto_of_tendsto_of_tendsto_of_le_of_le
    (tendsto_const_nhds.sub tendsto_one_div_add_atTop_nhds_zero_nat)
    tendsto_const_nhds
    (fun rank ↦ (windows.lower_mem rank).1.le)
    (fun rank ↦ by simpa using (windows.lower_mem rank).2.le)

omit [DecidableEq ι] [Nonempty ι] in
theorem upper_tendsto
    (windows : QuittingChronologicalNullWindowSequence law time) :
    Tendsto windows.upper atTop (nhds time) := by
  simpa only [add_zero] using tendsto_of_tendsto_of_tendsto_of_le_of_le
    tendsto_const_nhds
    (tendsto_const_nhds.add tendsto_one_div_add_atTop_nhds_zero_nat)
    (fun rank ↦ by simpa using (windows.upper_mem rank).1.le)
    (fun rank ↦ (windows.upper_mem rank).2.le)

omit [DecidableEq ι] [Nonempty ι] in
theorem width_tendsto_zero
    (windows : QuittingChronologicalNullWindowSequence law time) :
    Tendsto (fun rank ↦ windows.upper rank - windows.lower rank)
      atTop (nhds 0) := by
  simpa only [sub_self] using windows.upper_tendsto.sub windows.lower_tendsto

omit [DecidableEq ι] [Nonempty ι] in
/-- The mass in a shrinking null window for one coalition converges to the
mass of the exact clock--coalition fiber. -/
theorem openClockCoalitionWindow_real_tendsto_fiber_real
    (windows : QuittingChronologicalNullWindowSequence law time)
    (coalition : {S : Finset ι // S.Nonempty}) :
    Tendsto (fun rank ↦
      (law : Measure (QuittingChronologicalEvent reward)).real
        (chronologicalOpenClockCoalitionWindow
          (windows.lower rank) (windows.upper rank) coalition)) atTop
      (nhds ((law : Measure (QuittingChronologicalEvent reward)).real
        (chronologicalClockCoalitionFiber time coalition))) := by
  let coalitionEvent := chronologicalCoalitionEvent
    (reward := reward) coalition
  let clockMeasure : Measure ℝ := Measure.map chronologicalEventClock
    ((law : Measure (QuittingChronologicalEvent reward)).restrict coalitionEvent)
  let scale := fun rank : ℕ ↦ (1 : ℝ) / ((rank : ℝ) + 1)
  have hscale : Tendsto scale atTop (nhdsWithin 0 (Ici 0)) := by
    rw [tendsto_nhdsWithin_iff]
    exact ⟨tendsto_one_div_add_atTop_nhds_zero_nat,
      Filter.Eventually.of_forall fun rank ↦ by
        exact (div_nonneg zero_le_one (by positivity) : 0 ≤ scale rank)⟩
  have hclosed : Tendsto (fun rank ↦
      (clockMeasure (Icc (time - scale rank) (time + scale rank))).toReal)
      atTop (nhds ((clockMeasure ({time} : Set ℝ)).toReal)) := by
    exact (ENNReal.tendsto_toReal (measure_ne_top clockMeasure {time})).comp
      ((tendsto_measure_Icc_nhdsWithin_right clockMeasure time).comp hscale)
  have hfiber : clockMeasure ({time} : Set ℝ) =
      (law : Measure (QuittingChronologicalEvent reward))
        (chronologicalClockCoalitionFiber time coalition) := by
    unfold clockMeasure
    rw [Measure.map_apply continuous_chronologicalEventClock.measurable
      (measurableSet_singleton time), Measure.restrict_apply
      (continuous_chronologicalEventClock.measurable
        (measurableSet_singleton time))]
    congr 1
  rw [hfiber] at hclosed
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le
    tendsto_const_nhds hclosed
  · intro rank
    unfold Measure.real
    apply ENNReal.toReal_mono (measure_ne_top _ _)
    apply measure_mono
    intro event hevent
    refine ⟨⟨?_, ?_⟩, hevent.2⟩
    · rw [hevent.1]
      exact windows.lower_lt_time rank
    · rw [hevent.1]
      exact windows.time_lt_upper rank
  · intro rank
    unfold Measure.real
    apply ENNReal.toReal_mono (measure_ne_top _ _)
    unfold clockMeasure
    rw [Measure.map_apply continuous_chronologicalEventClock.measurable
      measurableSet_Icc, Measure.restrict_apply
      (continuous_chronologicalEventClock.measurable measurableSet_Icc)]
    apply measure_mono
    intro event hevent
    refine ⟨?_, hevent.2⟩
    constructor
    · exact (windows.lower_mem rank).1.le.trans hevent.1.1.le
    · exact hevent.1.2.le.trans (windows.upper_mem rank).2.le

omit [DecidableEq ι] [Nonempty ι] in
private theorem frontier_openClockWindow_null
    (windows : QuittingChronologicalNullWindowSequence law time)
    (rank : ℕ) :
    (law : Measure (QuittingChronologicalEvent reward))
      (frontier (chronologicalOpenClockWindow
      (reward := reward) (windows.lower rank) (windows.upper rank))) = 0 := by
  apply measure_mono_null
    (continuous_chronologicalEventClock.frontier_preimage_subset
      (Ioo (windows.lower rank) (windows.upper rank)))
  rw [frontier_Ioo (windows.lower_lt_upper rank)]
  change (law : Measure (QuittingChronologicalEvent reward))
    ({event | chronologicalEventClock event = windows.lower rank} ∪
      {event | chronologicalEventClock event = windows.upper rank}) = 0
  exact measure_union_null (windows.lower_fiber_null rank)
    (windows.upper_fiber_null rank)

omit [DecidableEq ι] [Nonempty ι] in
private theorem frontier_openClockCoalitionWindow_null
    (windows : QuittingChronologicalNullWindowSequence law time)
    (rank : ℕ) (coalition : {S : Finset ι // S.Nonempty}) :
    (law : Measure (QuittingChronologicalEvent reward))
      (frontier (chronologicalOpenClockCoalitionWindow
      (reward := reward) (windows.lower rank) (windows.upper rank)
        coalition)) = 0 := by
  let clockWindow := chronologicalOpenClockWindow
    (reward := reward) (windows.lower rank) (windows.upper rank)
  let coalitionEvent := chronologicalCoalitionEvent
    (reward := reward) coalition
  have hsubset : frontier (clockWindow ∩ coalitionEvent) ⊆
      frontier clockWindow ∪ frontier coalitionEvent := by
    intro event hevent
    rcases frontier_inter_subset clockWindow coalitionEvent hevent with
      hevent | hevent
    · exact Or.inl hevent.1
    · exact Or.inr hevent.2
  apply measure_mono_null hsubset
  apply measure_union_null
  · exact windows.frontier_openClockWindow_null rank
  · rw [(isClopen_chronologicalCoalitionEvent coalition).frontier_eq,
      measure_empty]

omit [DecidableEq ι] [Nonempty ι] in
/-- A fixed null-boundary total clock window has convergent mass under weak
convergence of chronological laws. -/
theorem tendsto_openClockWindow_real
    {laws : ℕ → ProbabilityMeasure (QuittingChronologicalEvent reward)}
    (windows : QuittingChronologicalNullWindowSequence law time)
    (hlaw : Tendsto laws atTop (nhds law)) (rank : ℕ) :
    Tendsto (fun sourceRank ↦
      (laws sourceRank : Measure (QuittingChronologicalEvent reward)).real
        (chronologicalOpenClockWindow
          (windows.lower rank) (windows.upper rank))) atTop
      (nhds ((law : Measure (QuittingChronologicalEvent reward)).real
        (chronologicalOpenClockWindow
          (windows.lower rank) (windows.upper rank)))) := by
  have hmeasure := ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto
    hlaw (by
      rw [← ENNReal.coe_eq_zero,
        ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure]
      exact windows.frontier_openClockWindow_null rank)
  exact NNReal.continuous_coe.continuousAt.tendsto.comp hmeasure

omit [DecidableEq ι] [Nonempty ι] in
/-- A fixed null-boundary coalition clock window has convergent mass under
weak convergence of chronological laws. -/
theorem tendsto_openClockCoalitionWindow_real
    {laws : ℕ → ProbabilityMeasure (QuittingChronologicalEvent reward)}
    (windows : QuittingChronologicalNullWindowSequence law time)
    (hlaw : Tendsto laws atTop (nhds law)) (rank : ℕ)
    (coalition : {S : Finset ι // S.Nonempty}) :
    Tendsto (fun sourceRank ↦
      (laws sourceRank : Measure (QuittingChronologicalEvent reward)).real
        (chronologicalOpenClockCoalitionWindow
          (windows.lower rank) (windows.upper rank) coalition)) atTop
      (nhds ((law : Measure (QuittingChronologicalEvent reward)).real
        (chronologicalOpenClockCoalitionWindow
          (windows.lower rank) (windows.upper rank) coalition))) := by
  have hmeasure := ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto
    hlaw (by
      rw [← ENNReal.coe_eq_zero,
        ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure]
      exact windows.frontier_openClockCoalitionWindow_null rank coalition)
  exact NNReal.continuous_coe.continuousAt.tendsto.comp hmeasure

end QuittingChronologicalNullWindowSequence

omit [Nonempty ι] in
/-- A chronological decoded path satisfying A1 has no coalition jump at the
terminal clock. -/
theorem pathJump_chronologicalCadlagPath_one_eq_zero_of_A1
    (law : ProbabilityMeasure (QuittingChronologicalEvent reward))
    (hA1 : ∀ time ∈ Icc (0 : ℝ) 1,
      time ≤ pathTotal (chronologicalCadlagPath law) time)
    (coalition : {S : Finset ι // S.Nonempty}) :
    pathJump (chronologicalCadlagPath law) 1 coalition = 0 := by
  let clockCDF := chronologicalClockCDF law
  have hmono : Monotone clockCDF :=
    ProbabilityTheory.monotone_cdf (chronologicalClockLaw law)
  have hleft_nonneg : 0 ≤ Function.leftLim clockCDF 1 := by
    exact (ProbabilityTheory.cdf_nonneg _ 0).trans
      (hmono.le_leftLim zero_lt_one)
  have hleft : Function.leftLim clockCDF 1 = 1 := by
    apply le_antisymm
    · exact (hmono.leftLim_le le_rfl).trans
        (ProbabilityTheory.cdf_le_one _ 1)
    · by_contra hnot
      have hlt : Function.leftLim clockCDF 1 < 1 := lt_of_not_ge hnot
      let earlier := (Function.leftLim clockCDF 1 + 1) / 2
      have hearlier_mem : earlier ∈ Icc (0 : ℝ) 1 := by
        constructor
        · dsimp [earlier]
          linarith
        · dsimp [earlier]
          linarith
      have hclock := hA1 earlier hearlier_mem
      rw [pathTotal_chronologicalCadlagPath_eq_chronologicalClockCDF
        law hearlier_mem.2] at hclock
      have hleLeft := hmono.le_leftLim (show earlier < 1 by
        dsimp [earlier]
        linarith)
      dsimp [earlier] at hclock
      linarith
  have hclockSingleton :
      (chronologicalClockLaw law : Measure ℝ) ({1} : Set ℝ) = 0 := by
    have hclockOne : clockCDF 1 = 1 := by
      apply le_antisymm (ProbabilityTheory.cdf_le_one _ 1)
      have h := hA1 1 (by simp)
      rw [pathTotal_chronologicalCadlagPath_eq_chronologicalClockCDF
        law le_rfl] at h
      exact h
    rw [← ProbabilityTheory.measure_cdf
      (chronologicalClockLaw law), StieltjesFunction.measure_singleton]
    change ENNReal.ofReal
      (clockCDF 1 - Function.leftLim clockCDF 1) = 0
    rw [hleft, hclockOne]
    simp
  have hclockFiber :
      (law : Measure (QuittingChronologicalEvent reward))
        {event | chronologicalEventClock event = 1} = 0 := by
    unfold chronologicalClockLaw at hclockSingleton
    change Measure.map chronologicalEventClock
      (law : Measure (QuittingChronologicalEvent reward)) {1} = 0 at hclockSingleton
    rw [Measure.map_apply continuous_chronologicalEventClock.measurable
      (measurableSet_singleton (1 : ℝ))] at hclockSingleton
    rw [show {event : QuittingChronologicalEvent reward |
        chronologicalEventClock event = 1} =
      chronologicalEventClock ⁻¹' ({1} : Set ℝ) by
        ext event
        simp]
    exact hclockSingleton
  rw [pathJump_chronologicalCadlagPath_eq_clockCoalitionFiber_real
    law 1 le_rfl coalition]
  unfold Measure.real
  rw [measure_mono_null (show chronologicalClockCoalitionFiber
    (reward := reward) 1 coalition ⊆
      {event | chronologicalEventClock event = 1} by
        intro event hevent
        exact hevent.1) hclockFiber]
  exact ENNReal.toReal_zero

end GameTheory.QuittingAbsorptionPath
