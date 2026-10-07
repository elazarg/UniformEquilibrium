import MathUE.Topology.CompactIntervalGap
import Mathlib.Topology.MetricSpace.Closeds
import Mathlib.Topology.Order.LeftRightNhds
import Mathlib.Topology.UnitInterval
import Mathlib.MeasureTheory.Constructions.BorelSpace.WithTop
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Measure.FiniteMeasurePi
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Measure.Typeclasses.NullSingletonClass

/-! # Compact marked-calendar clocks

Compact endpoint sets define clocks by collapsing each complementary interval
to its midpoint. A separate cutoff sends the remaining latent coordinates to
Never, represented by `⊤`. Finite replies at the cutoff remain finite.

This module defines the geometric clocks and their minimum-label kernels.
It does not construct quantile charts from original stopping laws, transport
complete response caps, or approximate arbitrary original profiles.
-/

noncomputable section

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology BigOperators

namespace MathUE.MarkedCalendar

/-- The compact endpoints of a latent unit-interval calendar and its finite
cutoff. The endpoint set need not be finite. -/
structure Calendar where
  endpoints : NonemptyCompacts ℝ
  cutoff : unitInterval
  endpoints_subset : (endpoints : Set ℝ) ⊆ Icc 0 1
  zero_mem : (0 : ℝ) ∈ endpoints
  one_mem : (1 : ℝ) ∈ endpoints
  cutoff_mem : (cutoff : ℝ) ∈ endpoints

namespace Calendar

variable (C : Calendar)

/-- Last endpoint weakly before the latent coordinate. -/
def lowerEndpoint (x : unitInterval) : ℝ := sSup ((C.endpoints : Set ℝ) ∩ Iic (x : ℝ))

/-- First endpoint weakly after the latent coordinate. -/
def upperEndpoint (x : unitInterval) : ℝ := sInf ((C.endpoints : Set ℝ) ∩ Ici (x : ℝ))

private theorem lower_nonempty (x : unitInterval) :
    ((C.endpoints : Set ℝ) ∩ Iic (x : ℝ)).Nonempty :=
  ⟨0, C.zero_mem, x.property.1⟩

private theorem upper_nonempty (x : unitInterval) :
    ((C.endpoints : Set ℝ) ∩ Ici (x : ℝ)).Nonempty :=
  ⟨1, C.one_mem, x.property.2⟩

private theorem lower_bddAbove (x : unitInterval) :
    BddAbove ((C.endpoints : Set ℝ) ∩ Iic (x : ℝ)) :=
  ⟨x, fun _ hx => hx.2⟩

private theorem upper_bddBelow (x : unitInterval) :
    BddBelow ((C.endpoints : Set ℝ) ∩ Ici (x : ℝ)) :=
  ⟨x, fun _ hx => hx.2⟩

theorem lowerEndpoint_le (x : unitInterval) : C.lowerEndpoint x ≤ (x : ℝ) :=
  csSup_le (C.lower_nonempty x) fun _ hx => hx.2

theorem le_upperEndpoint (x : unitInterval) : (x : ℝ) ≤ C.upperEndpoint x :=
  le_csInf (C.upper_nonempty x) fun _ hx => hx.2

theorem lowerEndpoint_mem (x : unitInterval) : C.lowerEndpoint x ∈ C.endpoints := by
  exact ((C.endpoints.isCompact.inter_right isClosed_Iic).isClosed.csSup_mem
    (C.lower_nonempty x) (C.lower_bddAbove x)).1

theorem upperEndpoint_mem (x : unitInterval) : C.upperEndpoint x ∈ C.endpoints := by
  exact ((C.endpoints.isCompact.inter_right isClosed_Ici).isClosed.csInf_mem
    (C.upper_nonempty x) (C.upper_bddBelow x)).1

theorem lowerEndpoint_eq_of_mem {x : unitInterval} (hx : (x : ℝ) ∈ C.endpoints) :
    C.lowerEndpoint x = (x : ℝ) := by
  exact (C.lowerEndpoint_le x).antisymm
    (le_csSup (C.lower_bddAbove x) ⟨hx, show (x : ℝ) ≤ x from le_rfl⟩)

theorem upperEndpoint_eq_of_mem {x : unitInterval} (hx : (x : ℝ) ∈ C.endpoints) :
    C.upperEndpoint x = (x : ℝ) := by
  exact (csInf_le (C.upper_bddBelow x)
    ⟨hx, show (x : ℝ) ≤ x from le_rfl⟩).antisymm (C.le_upperEndpoint x)

theorem monotone_lowerEndpoint : Monotone C.lowerEndpoint := by
  intro x y hxy
  exact csSup_le_csSup (C.lower_bddAbove y) (C.lower_nonempty x)
    (fun z hx => ⟨hx.1, (show z ≤ (x : ℝ) from hx.2).trans hxy⟩)

theorem monotone_upperEndpoint : Monotone C.upperEndpoint := by
  intro x y hxy
  exact csInf_le_csInf (C.upper_bddBelow x) (C.upper_nonempty y)
    (fun z hy => ⟨hy.1, (show (x : ℝ) ≤ y from hxy).trans hy.2⟩)

/-- The real midpoint of the two neighboring endpoints. -/
def midpointClock (x : unitInterval) : ℝ :=
  (C.lowerEndpoint x + C.upperEndpoint x) / 2

theorem monotone_midpointClock : Monotone C.midpointClock := by
  intro x y hxy
  exact div_le_div_of_nonneg_right
    (add_le_add (C.monotone_lowerEndpoint hxy) (C.monotone_upperEndpoint hxy))
    (by norm_num)

theorem measurable_midpointClock : Measurable C.midpointClock :=
  C.monotone_midpointClock.measurable

/-- Collapse finite intervals to their midpoints and retain Never as `⊤`. -/
def collapseClock (x : unitInterval) : WithTop ℝ :=
  if C.cutoff ≤ x then ⊤ else (C.midpointClock x : WithTop ℝ)

@[simp] theorem collapseClock_eq_top_iff (x : unitInterval) :
    C.collapseClock x = ⊤ ↔ C.cutoff ≤ x := by
  simp only [collapseClock]
  split_ifs <;> simp_all

theorem collapseClock_of_lt {x : unitInterval} (hx : x < C.cutoff) :
    C.collapseClock x = (C.midpointClock x : WithTop ℝ) := by
  exact ite_eq_right (not_le.mpr hx)

theorem measurable_collapseClock : Measurable C.collapseClock := by
  exact Measurable.ite (measurableSet_le measurable_const measurable_id)
    measurable_const C.measurable_midpointClock.withTop_coe

theorem endpoints_of_gap {a b : ℝ} (hgap : Math.Topology.IsGap C.endpoints a b)
    {x : unitInterval} (hax : a < (x : ℝ)) (hxb : (x : ℝ) < b) :
    C.lowerEndpoint x = a ∧ C.upperEndpoint x = b := by
  constructor
  · apply le_antisymm
    · apply csSup_le (C.lower_nonempty x)
      intro y hy
      rcases hgap.2.2.2 y hy.1 with hya | hby
      · exact hya
      · exact (not_le_of_gt hxb (hby.trans hy.2)).elim
    · exact le_csSup (C.lower_bddAbove x) ⟨hgap.1, hax.le⟩
  · apply le_antisymm
    · exact csInf_le (C.upper_bddBelow x) ⟨hgap.2.1, hxb.le⟩
    · apply le_csInf (C.upper_nonempty x)
      intro y hy
      rcases hgap.2.2.2 y hy.1 with hya | hby
      · exact (not_le_of_gt hax (hy.2.trans hya)).elim
      · exact hby

theorem midpointClock_of_gap {a b : ℝ} (hgap : Math.Topology.IsGap C.endpoints a b)
    {x : unitInterval} (hax : a < (x : ℝ)) (hxb : (x : ℝ) < b) :
    C.midpointClock x = (a + b) / 2 := by
  obtain ⟨hlower, hupper⟩ := C.endpoints_of_gap hgap hax hxb
  simp only [midpointClock, hlower, hupper]

/-- Compatibility with actual atom ties. This does not declare a mark to be
an available response or add it to any original tester set. -/
def AtomCompatible (t : ℝ) : Prop :=
  t ∈ Icc 0 (C.cutoff : ℝ) ∧
    ∀ a b, Math.Topology.IsGap C.endpoints a b → a < t → t < b → t = (a + b) / 2

/-- The countable endpoint exceptions where one neighboring endpoint can jump. -/
def exceptionalEndpoints : Set ℝ :=
  {x ∈ (C.endpoints : Set ℝ) | 𝓝[(C.endpoints : Set ℝ) ∩ Ioi x] x = ⊥} ∪
    {x ∈ (C.endpoints : Set ℝ) | 𝓝[(C.endpoints : Set ℝ) ∩ Iio x] x = ⊥}

theorem countable_exceptionalEndpoints : C.exceptionalEndpoints.Countable :=
  countable_setOfPred_isolated_right_within.union
    countable_setOfPred_isolated_left_within

theorem ae_notMem_exceptionalEndpoints (base : Measure unitInterval)
    [NullSingletonClass base] :
    ∀ᵐ x : unitInterval ∂base, (x : ℝ) ∉ C.exceptionalEndpoints :=
  (C.countable_exceptionalEndpoints.preimage
    (f := fun x : unitInterval => (x : ℝ)) Subtype.val_injective).ae_notMem base

private theorem mem_closure_left {x : unitInterval}
    (hx : (x : ℝ) ∉ C.exceptionalEndpoints) (hmem : (x : ℝ) ∈ C.endpoints) :
    (x : ℝ) ∈ closure ((C.endpoints : Set ℝ) ∩ Iio (x : ℝ)) := by
  by_contra h
  exact hx (Or.inr ⟨hmem, notMem_closure_iff_nhdsWithin_eq_bot.mp h⟩)

private theorem mem_closure_right {x : unitInterval}
    (hx : (x : ℝ) ∉ C.exceptionalEndpoints) (hmem : (x : ℝ) ∈ C.endpoints) :
    (x : ℝ) ∈ closure ((C.endpoints : Set ℝ) ∩ Ioi (x : ℝ)) := by
  by_contra h
  exact hx (Or.inl ⟨hmem, notMem_closure_iff_nhdsWithin_eq_bot.mp h⟩)

private theorem eventually_hit_open {calendars : ℕ → Calendar} {limit : Calendar}
    (hE : Tendsto (fun k => (calendars k).endpoints) atTop (𝓝 limit.endpoints))
    {U : Set ℝ} (hU : IsOpen U) (hhit : ((limit.endpoints : Set ℝ) ∩ U).Nonempty) :
    ∀ᶠ k in atTop, (((calendars k).endpoints : Set ℝ) ∩ U).Nonempty :=
  hE.eventually ((NonemptyCompacts.isOpen_inter_nonempty_of_isOpen hU).mem_nhds hhit)

private theorem eventually_avoid_closed {calendars : ℕ → Calendar} {limit : Calendar}
    (hE : Tendsto (fun k => (calendars k).endpoints) atTop (𝓝 limit.endpoints))
    {F : Set ℝ} (hF : IsClosed F) (havoid : ∀ z ∈ limit.endpoints, z ∉ F) :
    ∀ᶠ k in atTop, ∀ z ∈ (calendars k).endpoints, z ∉ F :=
  hE.eventually ((NonemptyCompacts.isOpen_subsets_of_isOpen hF.isOpen_compl).mem_nhds
    havoid)

/-- Actual neighboring endpoints converge away from the countable endpoint exceptions. -/
theorem tendsto_lowerEndpoint {calendars : ℕ → Calendar} {limit : Calendar}
    (hE : Tendsto (fun k => (calendars k).endpoints) atTop (𝓝 limit.endpoints))
    {x : unitInterval} (hx : (x : ℝ) ∉ limit.exceptionalEndpoints) :
    Tendsto (fun k => (calendars k).lowerEndpoint x) atTop (𝓝 (limit.lowerEndpoint x)) := by
  apply tendsto_order.mpr
  constructor
  · intro a ha
    have hhit : ((limit.endpoints : Set ℝ) ∩ Ioo a (x : ℝ)).Nonempty := by
      rcases (limit.lowerEndpoint_le x).lt_or_eq with hlt | heq
      · exact ⟨limit.lowerEndpoint x, limit.lowerEndpoint_mem x, ha, hlt⟩
      · have hmem : (x : ℝ) ∈ limit.endpoints := heq ▸ limit.lowerEndpoint_mem x
        obtain ⟨z, haz, hzE, hzx⟩ := mem_closure_iff.mp
          (limit.mem_closure_left hx hmem) (Ioi a) isOpen_Ioi (heq ▸ ha)
        exact ⟨z, hzE, haz, hzx⟩
    filter_upwards [eventually_hit_open hE isOpen_Ioo hhit] with k hk
    obtain ⟨z, hzE, haz, hzx⟩ := hk
    exact haz.trans_le (le_csSup ((calendars k).lower_bddAbove x) ⟨hzE, hzx.le⟩)
  · intro b hb
    by_cases hxb : (x : ℝ) < b
    · exact Eventually.of_forall fun k => ((calendars k).lowerEndpoint_le x).trans_lt hxb
    · have havoid : ∀ z ∈ limit.endpoints, z ∉ Icc b (x : ℝ) := by
        intro z hzE hz
        have hzlower := le_csSup (limit.lower_bddAbove x) ⟨hzE, hz.2⟩
        exact (not_le_of_gt hb) (hz.1.trans hzlower)
      filter_upwards [eventually_avoid_closed hE isClosed_Icc havoid] with k hk
      apply lt_of_not_ge
      intro hbkl
      exact hk _ ((calendars k).lowerEndpoint_mem x)
        ⟨hbkl, (calendars k).lowerEndpoint_le x⟩

theorem tendsto_upperEndpoint {calendars : ℕ → Calendar} {limit : Calendar}
    (hE : Tendsto (fun k => (calendars k).endpoints) atTop (𝓝 limit.endpoints))
    {x : unitInterval} (hx : (x : ℝ) ∉ limit.exceptionalEndpoints) :
    Tendsto (fun k => (calendars k).upperEndpoint x) atTop (𝓝 (limit.upperEndpoint x)) := by
  apply tendsto_order.mpr
  constructor
  · intro a ha
    by_cases hax : a < (x : ℝ)
    · exact Eventually.of_forall fun k => hax.trans_le ((calendars k).le_upperEndpoint x)
    · have havoid : ∀ z ∈ limit.endpoints, z ∉ Icc (x : ℝ) a := by
        intro z hzE hz
        have hupperz := csInf_le (limit.upper_bddBelow x) ⟨hzE, hz.1⟩
        exact (not_le_of_gt ha) (hupperz.trans hz.2)
      filter_upwards [eventually_avoid_closed hE isClosed_Icc havoid] with k hk
      apply lt_of_not_ge
      intro hkua
      exact hk _ ((calendars k).upperEndpoint_mem x)
        ⟨(calendars k).le_upperEndpoint x, hkua⟩
  · intro b hb
    have hhit : ((limit.endpoints : Set ℝ) ∩ Ioo (x : ℝ) b).Nonempty := by
      rcases (limit.le_upperEndpoint x).lt_or_eq with hlt | heq
      · exact ⟨limit.upperEndpoint x, limit.upperEndpoint_mem x, hlt, hb⟩
      · have hmem : (x : ℝ) ∈ limit.endpoints := heq.symm ▸ limit.upperEndpoint_mem x
        obtain ⟨z, hzb, hzE, hxz⟩ := mem_closure_iff.mp
          (limit.mem_closure_right hx hmem) (Iio b) isOpen_Iio (heq.symm ▸ hb)
        exact ⟨z, hzE, hxz, hzb⟩
    filter_upwards [eventually_hit_open hE isOpen_Ioo hhit] with k hk
    obtain ⟨z, hzE, hxz, hzb⟩ := hk
    exact (csInf_le ((calendars k).upper_bddBelow x) ⟨hzE, hxz.le⟩).trans_lt hzb

theorem tendsto_midpointClock {calendars : ℕ → Calendar} {limit : Calendar}
    (hE : Tendsto (fun k => (calendars k).endpoints) atTop (𝓝 limit.endpoints))
    {x : unitInterval} (hx : (x : ℝ) ∉ limit.exceptionalEndpoints) :
    Tendsto (fun k => (calendars k).midpointClock x) atTop (𝓝 (limit.midpointClock x)) :=
  ((tendsto_lowerEndpoint hE hx).add (tendsto_upperEndpoint hE hx)).div_const 2

theorem midpointClock_lt_of_endpoint_between {x y : unitInterval}
    {z : ℝ} (hzE : z ∈ C.endpoints) (hxz : (x : ℝ) < z) (hzy : z < (y : ℝ)) :
    C.midpointClock x < C.midpointClock y := by
  have hupper := csInf_le (C.upper_bddBelow x) ⟨hzE, hxz.le⟩
  have hlower := le_csSup (C.lower_bddAbove y) ⟨hzE, hzy.le⟩
  change C.upperEndpoint x ≤ z at hupper
  change z ≤ C.lowerEndpoint y at hlower
  have hx := C.lowerEndpoint_le x
  have hy := C.le_upperEndpoint y
  unfold midpointClock
  linarith

theorem midpointClock_eq_of_avoid_closed {x y : unitInterval} (hxy : x ≤ y)
    (havoid : ∀ z ∈ C.endpoints, z ∉ Icc (x : ℝ) (y : ℝ)) :
    C.midpointClock x = C.midpointClock y := by
  have hlower : (C.endpoints : Set ℝ) ∩ Iic (x : ℝ) =
      (C.endpoints : Set ℝ) ∩ Iic (y : ℝ) := by
    ext z
    constructor
    · rintro ⟨hzE, hzx⟩
      exact ⟨hzE, (show z ≤ (x : ℝ) from hzx).trans hxy⟩
    · rintro ⟨hzE, hzy⟩
      exact ⟨hzE, le_of_not_gt fun hxz => havoid z hzE ⟨hxz.le, hzy⟩⟩
  have hupper : (C.endpoints : Set ℝ) ∩ Ici (x : ℝ) =
      (C.endpoints : Set ℝ) ∩ Ici (y : ℝ) := by
    ext z
    constructor
    · rintro ⟨hzE, hxz⟩
      exact ⟨hzE, le_of_not_gt fun hzy => havoid z hzE ⟨hxz, hzy.le⟩⟩
    · rintro ⟨hzE, hyz⟩
      exact ⟨hzE, (show (x : ℝ) ≤ y from hxy).trans hyz⟩
  simp only [midpointClock, lowerEndpoint, upperEndpoint, hlower, hupper]

end Calendar

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Labels at the earliest finite clock. The empty set means all Never. -/
def minimumLabels (clock : ι → WithTop ℝ) : Finset ι :=
  Finset.univ.filter fun i => clock i ≠ ⊤ ∧ ∀ j, clock i ≤ clock j

/-- First finite labels in the actual collapsed latent sample. -/
def firstLabels (C : Calendar) (sample : ι → unitInterval) : Finset ι :=
  minimumLabels fun i => C.collapseClock (sample i)

/-- Actual indicator of a first-label event; the empty event records Never. -/
def coalitionKernel (C : Calendar) (coalition : Finset ι)
    (sample : ι → unitInterval) : ℝ :=
  if firstLabels C sample = coalition then 1 else 0

/-- A finite outcome observable applied to the actual first-label event. -/
def payoffKernel (C : Calendar) (reward : Finset ι → ℝ)
    (sample : ι → unitInterval) : ℝ := reward (firstLabels C sample)

omit [DecidableEq ι] in
theorem measurable_firstLabels (C : Calendar) : Measurable (firstLabels C (ι := ι)) := by
  apply measurable_finset_iff.mpr
  intro i
  simp only [firstLabels, minimumLabels, Finset.mem_filter, Finset.mem_univ, true_and]
  have hclock (j : ι) : Measurable fun sample : ι → unitInterval =>
      C.collapseClock (sample j) := C.measurable_collapseClock.comp (measurable_pi_apply j)
  exact ((hclock i).eq_const ⊤).not.and
    (Measurable.forall fun j => (hclock i).le' (hclock j))

theorem measurable_coalitionKernel (C : Calendar) (coalition : Finset ι) :
    Measurable (coalitionKernel C coalition) :=
  Measurable.ite ((measurable_firstLabels C).eq_const coalition).setOf
    measurable_const measurable_const

omit [DecidableEq ι] in
theorem measurable_payoffKernel (C : Calendar) (reward : Finset ι → ℝ) :
    Measurable (payoffKernel C reward) :=
  (measurable_of_countable reward).comp (measurable_firstLabels C)

theorem coalitionKernel_nonneg (C : Calendar) (coalition : Finset ι)
    (sample : ι → unitInterval) : 0 ≤ coalitionKernel C coalition sample := by
  unfold coalitionKernel
  split_ifs <;> norm_num

theorem coalitionKernel_le_one (C : Calendar) (coalition : Finset ι)
    (sample : ι → unitInterval) : coalitionKernel C coalition sample ≤ 1 := by
  unfold coalitionKernel
  split_ifs <;> norm_num

end MathUE.MarkedCalendar
