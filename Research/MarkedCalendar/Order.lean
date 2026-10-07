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

Endpoint and cutoff convergence give actual almost-everywhere stabilization
and L¹ convergence of first-label kernels under an atomless independent base.
Compatible moving finite replies preserve positive-mass interval ties; Never
is handled separately. Compatibility does not assert legal-menu membership.

This module does not construct quantile charts from original stopping laws,
transport complete response caps, or approximate arbitrary original profiles.
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

/-- The finite cutoff has no latent preimage, even before any measure is chosen. -/
theorem collapseClock_ne_cutoff (x : unitInterval) :
    C.collapseClock x ≠ ((C.cutoff : ℝ) : WithTop ℝ) := by
  by_cases hx : C.cutoff ≤ x
  · rw [collapseClock, ite_eq_left hx]
    exact WithTop.top_ne_coe
  · have hxc : x < C.cutoff := lt_of_not_ge hx
    have hupper : C.upperEndpoint x ≤ (C.cutoff : ℝ) :=
      (C.monotone_upperEndpoint hxc.le).trans_eq (C.upperEndpoint_eq_of_mem C.cutoff_mem)
    have hlower := C.lowerEndpoint_le x
    have hreal : (x : ℝ) < (C.cutoff : ℝ) := hxc
    have hmid : C.midpointClock x < (C.cutoff : ℝ) := by
      unfold midpointClock
      linarith
    rw [C.collapseClock_of_lt hxc]
    exact fun heq => hmid.ne (WithTop.coe_injective heq)

theorem preimage_collapseClock_cutoff :
    C.collapseClock ⁻¹' {((C.cutoff : ℝ) : WithTop ℝ)} = ∅ := by
  ext x
  exact iff_of_false (C.collapseClock_ne_cutoff x) (Set.notMem_empty x)

theorem measurable_collapseClock : Measurable C.collapseClock := by
  exact Measurable.ite (measurableSet_le measurable_const measurable_id)
    measurable_const C.measurable_midpointClock.withTop_coe

/-- Any latent measure, including an atomic one, gives the finite cutoff zero collapsed mass. -/
theorem map_collapseClock_cutoff (μ : Measure unitInterval) :
    μ.map C.collapseClock {((C.cutoff : ℝ) : WithTop ℝ)} = 0 := by
  rw [Measure.map_apply C.measurable_collapseClock (measurableSet_singleton _),
    C.preimage_collapseClock_cutoff, measure_empty]

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

private theorem avoid_closed_of_no_open_hit {x y : unitInterval} (hxy : x < y)
    (hx : (x : ℝ) ∉ C.exceptionalEndpoints) (hy : (y : ℝ) ∉ C.exceptionalEndpoints)
    (havoid : ∀ z ∈ C.endpoints, z ∉ Ioo (x : ℝ) (y : ℝ)) :
    ∀ z ∈ C.endpoints, z ∉ Icc (x : ℝ) (y : ℝ) := by
  intro z hzE hz
  by_cases hzx : z = (x : ℝ)
  · have hxE : (x : ℝ) ∈ C.endpoints := hzx ▸ hzE
    obtain ⟨w, hwy, hwE, hxw⟩ := mem_closure_iff.mp
      (C.mem_closure_right hx hxE) (Iio (y : ℝ)) isOpen_Iio hxy
    exact havoid w hwE ⟨hxw, hwy⟩
  · by_cases hzy : z = (y : ℝ)
    · have hyE : (y : ℝ) ∈ C.endpoints := hzy ▸ hzE
      obtain ⟨w, hxw, hwE, hwy⟩ := mem_closure_iff.mp
        (C.mem_closure_left hy hyE) (Ioi (x : ℝ)) isOpen_Ioi hxy
      exact havoid w hwE ⟨hxw, hwy⟩
    · exact havoid z hzE ⟨lt_of_le_of_ne hz.1 (Ne.symm hzx), lt_of_le_of_ne hz.2 hzy⟩

private theorem eventually_midpointClock_eq_of_eq_of_lt
    {calendars : ℕ → Calendar} {limit : Calendar}
    (hE : Tendsto (fun k => (calendars k).endpoints) atTop (𝓝 limit.endpoints))
    {x y : unitInterval} (hxy : x < y)
    (hx : (x : ℝ) ∉ limit.exceptionalEndpoints)
    (hy : (y : ℝ) ∉ limit.exceptionalEndpoints)
    (heq : limit.midpointClock x = limit.midpointClock y) :
    ∀ᶠ k in atTop, (calendars k).midpointClock x = (calendars k).midpointClock y := by
  have havoid : ∀ z ∈ limit.endpoints, z ∉ Ioo (x : ℝ) (y : ℝ) := by
    intro z hzE hz
    exact (ne_of_lt (limit.midpointClock_lt_of_endpoint_between hzE hz.1 hz.2)) heq
  filter_upwards [eventually_avoid_closed hE isClosed_Icc
    (limit.avoid_closed_of_no_open_hit hxy hx hy havoid)] with k hk
  exact (calendars k).midpointClock_eq_of_avoid_closed hxy.le hk

/-- Positive-mass collapsed ties persist exactly, not merely in the limit. -/
theorem eventually_midpointClock_eq_of_eq {calendars : ℕ → Calendar} {limit : Calendar}
    (hE : Tendsto (fun k => (calendars k).endpoints) atTop (𝓝 limit.endpoints))
    {x y : unitInterval} (hx : (x : ℝ) ∉ limit.exceptionalEndpoints)
    (hy : (y : ℝ) ∉ limit.exceptionalEndpoints)
    (heq : limit.midpointClock x = limit.midpointClock y) :
    ∀ᶠ k in atTop, (calendars k).midpointClock x = (calendars k).midpointClock y := by
  rcases lt_trichotomy x y with hxy | hxy | hyx
  · exact eventually_midpointClock_eq_of_eq_of_lt hE hxy hx hy heq
  · subst y
    exact Eventually.of_forall fun _ => rfl
  · exact (eventually_midpointClock_eq_of_eq_of_lt hE hyx hy hx heq.symm).mono
      fun _ hk => hk.symm

theorem eventually_midpointClock_le_iff {calendars : ℕ → Calendar} {limit : Calendar}
    (hE : Tendsto (fun k => (calendars k).endpoints) atTop (𝓝 limit.endpoints))
    {x y : unitInterval} (hx : (x : ℝ) ∉ limit.exceptionalEndpoints)
    (hy : (y : ℝ) ∉ limit.exceptionalEndpoints) :
    ∀ᶠ k in atTop, (calendars k).midpointClock x ≤ (calendars k).midpointClock y ↔
      limit.midpointClock x ≤ limit.midpointClock y := by
  rcases lt_trichotomy (limit.midpointClock x) (limit.midpointClock y) with h | h | h
  · filter_upwards [(tendsto_midpointClock hE hx).eventually_lt
      (tendsto_midpointClock hE hy) h] with k hk
    exact iff_of_true hk.le h.le
  · filter_upwards [eventually_midpointClock_eq_of_eq hE hx hy h] with k hk
    exact iff_of_true hk.le h.le
  · filter_upwards [(tendsto_midpointClock hE hy).eventually_lt
      (tendsto_midpointClock hE hx) h] with k hk
    exact iff_of_false (not_le_of_gt hk) (not_le_of_gt h)

theorem eventually_cutoff_le_iff {calendars : ℕ → Calendar} {limit : Calendar}
    (hc : Tendsto (fun k => (calendars k).cutoff) atTop (𝓝 limit.cutoff))
    {x : unitInterval} (hx : x ≠ limit.cutoff) :
    ∀ᶠ k in atTop, (calendars k).cutoff ≤ x ↔ limit.cutoff ≤ x := by
  rcases hx.lt_or_gt with h | h
  · filter_upwards [tendsto_const_nhds.eventually_lt hc h] with k hk
    exact iff_of_false (not_le_of_gt hk) (not_le_of_gt h)
  · filter_upwards [hc.eventually_lt tendsto_const_nhds h] with k hk
    exact iff_of_true hk.le h.le

theorem eventually_collapseClock_le_iff {calendars : ℕ → Calendar} {limit : Calendar}
    (hE : Tendsto (fun k => (calendars k).endpoints) atTop (𝓝 limit.endpoints))
    (hc : Tendsto (fun k => (calendars k).cutoff) atTop (𝓝 limit.cutoff))
    {x y : unitInterval} (hx : (x : ℝ) ∉ limit.exceptionalEndpoints)
    (hy : (y : ℝ) ∉ limit.exceptionalEndpoints)
    (hxc : x ≠ limit.cutoff) (hyc : y ≠ limit.cutoff) :
    ∀ᶠ k in atTop, (calendars k).collapseClock x ≤ (calendars k).collapseClock y ↔
      limit.collapseClock x ≤ limit.collapseClock y := by
  filter_upwards [eventually_cutoff_le_iff hc hxc, eventually_cutoff_le_iff hc hyc,
    eventually_midpointClock_le_iff hE hx hy] with k hxk hyk horder
  simp only [collapseClock]
  by_cases hxcut : limit.cutoff ≤ x <;> by_cases hycut : limit.cutoff ≤ y <;>
    simp_all only [ite_true, ite_false, le_top, WithTop.top_le_iff,
      WithTop.coe_ne_top, WithTop.coe_le_coe]

theorem midpointClock_eq_of_mem {x : unitInterval} (hx : (x : ℝ) ∈ C.endpoints) :
    C.midpointClock x = (x : ℝ) := by
  rw [midpointClock, C.lowerEndpoint_eq_of_mem hx, C.upperEndpoint_eq_of_mem hx]
  ring

theorem gap_of_not_mem {x : unitInterval} (hx : (x : ℝ) ∉ C.endpoints) :
    Math.Topology.IsGap C.endpoints (C.lowerEndpoint x) (C.upperEndpoint x) ∧
      C.lowerEndpoint x < (x : ℝ) ∧ (x : ℝ) < C.upperEndpoint x := by
  obtain ⟨a, b, hgap, hax, hxb⟩ := Math.Topology.exists_gap_of_mem_interval_not_mem
    (C.endpoints : Set ℝ) C.endpoints.isCompact C.zero_mem C.one_mem x.property hx
  obtain ⟨hlower, hupper⟩ := C.endpoints_of_gap hgap hax hxb
  simpa only [hlower, hupper] using And.intro hgap (And.intro hax hxb)

/-- A compatible moving mark preserves an actual interval tie exactly. Only
the latent equality `x = t`, not equality of collapsed clocks, is excluded. -/
theorem eventually_tester_eq_midpointClock {calendars : ℕ → Calendar} {limit : Calendar}
    (hE : Tendsto (fun k => (calendars k).endpoints) atTop (𝓝 limit.endpoints))
    {tester : ℕ → ℝ} {t : ℝ} (ht : Tendsto tester atTop (𝓝 t))
    (hcompatible : ∀ k, (calendars k).AtomCompatible (tester k))
    {x : unitInterval} (hx : (x : ℝ) ∉ limit.exceptionalEndpoints)
    (hxt : (x : ℝ) ≠ t) (heq : t = limit.midpointClock x) :
    ∀ᶠ k in atTop, tester k = (calendars k).midpointClock x := by
  have hxE : (x : ℝ) ∉ limit.endpoints := by
    intro hmem
    exact hxt (heq.trans (limit.midpointClock_eq_of_mem hmem)).symm
  obtain ⟨_, hleft, hright⟩ := limit.gap_of_not_mem hxE
  have hlt : limit.lowerEndpoint x < t := by
    rw [heq, midpointClock]
    linarith
  have htu : t < limit.upperEndpoint x := by
    rw [heq, midpointClock]
    linarith
  have hnotMem : ∀ᶠ k in atTop, (x : ℝ) ∉ (calendars k).endpoints := by
    filter_upwards [eventually_avoid_closed hE isClosed_singleton
      (show ∀ z ∈ limit.endpoints, z ∉ ({(x : ℝ)} : Set ℝ) from
        fun z hzE hzx => hxE (mem_singleton_iff.mp hzx ▸ hzE))] with k hk
    exact fun hxk => hk _ hxk (mem_singleton (x : ℝ))
  filter_upwards [hnotMem, (tendsto_lowerEndpoint hE hx).eventually_lt ht hlt,
    ht.eventually_lt (tendsto_upperEndpoint hE hx) htu] with k hxk hlk huk
  exact (hcompatible k).2 _ _ ((calendars k).gap_of_not_mem hxk).1 hlk huk

theorem eventually_tester_midpointClock_order
    {calendars : ℕ → Calendar} {limit : Calendar}
    (hE : Tendsto (fun k => (calendars k).endpoints) atTop (𝓝 limit.endpoints))
    {tester : ℕ → ℝ} {t : ℝ} (ht : Tendsto tester atTop (𝓝 t))
    (hcompatible : ∀ k, (calendars k).AtomCompatible (tester k))
    {x : unitInterval} (hx : (x : ℝ) ∉ limit.exceptionalEndpoints)
    (hxt : (x : ℝ) ≠ t) :
    ∀ᶠ k in atTop,
      (tester k ≤ (calendars k).midpointClock x ↔ t ≤ limit.midpointClock x) ∧
      ((calendars k).midpointClock x ≤ tester k ↔ limit.midpointClock x ≤ t) := by
  rcases lt_trichotomy t (limit.midpointClock x) with h | h | h
  · filter_upwards [ht.eventually_lt (tendsto_midpointClock hE hx) h] with k hk
    exact ⟨iff_of_true hk.le h.le, iff_of_false (not_le_of_gt hk) (not_le_of_gt h)⟩
  · filter_upwards [eventually_tester_eq_midpointClock hE ht hcompatible hx hxt h] with k hk
    exact ⟨iff_of_true hk.le h.le, iff_of_true hk.symm.le h.symm.le⟩
  · filter_upwards [(tendsto_midpointClock hE hx).eventually_lt ht h] with k hk
    exact ⟨iff_of_false (not_le_of_gt hk) (not_le_of_gt h), iff_of_true hk.le h.le⟩

theorem eventually_tester_collapseClock_order
    {calendars : ℕ → Calendar} {limit : Calendar}
    (hE : Tendsto (fun k => (calendars k).endpoints) atTop (𝓝 limit.endpoints))
    (hc : Tendsto (fun k => (calendars k).cutoff) atTop (𝓝 limit.cutoff))
    {tester : ℕ → ℝ} {t : ℝ} (ht : Tendsto tester atTop (𝓝 t))
    (hcompatible : ∀ k, (calendars k).AtomCompatible (tester k))
    {x : unitInterval} (hx : (x : ℝ) ∉ limit.exceptionalEndpoints)
    (hxc : x ≠ limit.cutoff) (hxt : (x : ℝ) ≠ t) :
    ∀ᶠ k in atTop,
      ((tester k : WithTop ℝ) ≤ (calendars k).collapseClock x ↔
        (t : WithTop ℝ) ≤ limit.collapseClock x) ∧
      ((calendars k).collapseClock x ≤ (tester k : WithTop ℝ) ↔
        limit.collapseClock x ≤ (t : WithTop ℝ)) := by
  filter_upwards [eventually_cutoff_le_iff hc hxc,
    eventually_tester_midpointClock_order hE ht hcompatible hx hxt] with k hk horder
  simp only [collapseClock]
  by_cases hcut : limit.cutoff ≤ x <;>
    simp_all only [ite_true, ite_false, le_top, WithTop.top_le_iff,
      WithTop.coe_ne_top, WithTop.coe_le_coe, and_self]

end Calendar

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Labels at the earliest finite clock. The empty set means all Never. -/
def minimumLabels (clock : ι → WithTop ℝ) : Finset ι :=
  Finset.univ.filter fun i => clock i ≠ ⊤ ∧ ∀ j, clock i ≤ clock j

omit [DecidableEq ι] in
theorem minimumLabels_eq_of_order_and_top {first second : ι → WithTop ℝ}
    (htop : ∀ i, first i = ⊤ ↔ second i = ⊤)
    (horder : ∀ i j, first i ≤ first j ↔ second i ≤ second j) :
    minimumLabels first = minimumLabels second := by
  ext i
  simp only [minimumLabels, Finset.mem_filter, Finset.mem_univ, true_and]
  exact and_congr (not_congr (htop i)) (forall_congr' (horder i))

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

/-- Insert one literal response clock into the actual opponent clocks. -/
def responseClock (C : Calendar) (who : ι) (reply : WithTop ℝ)
    (sample : {j : ι // j ≠ who} → unitInterval) (j : ι) : WithTop ℝ :=
  if h : j = who then reply else C.collapseClock (sample ⟨j, h⟩)

/-- Response outcomes keep finite marks, including the cutoff, distinct from Never. -/
def responseLabels (C : Calendar) (who : ι) (reply : WithTop ℝ)
    (sample : {j : ι // j ≠ who} → unitInterval) : Finset ι :=
  minimumLabels (responseClock C who reply sample)

def responsePayoffKernel (C : Calendar) (who : ι) (reply : WithTop ℝ)
    (reward : Finset ι → ℝ) (sample : {j : ι // j ≠ who} → unitInterval) : ℝ :=
  reward (responseLabels C who reply sample)

def responseCoalitionKernel (C : Calendar) (who : ι) (reply : WithTop ℝ)
    (coalition : Finset ι) (sample : {j : ι // j ≠ who} → unitInterval) : ℝ :=
  responsePayoffKernel C who reply (fun outcome => if outcome = coalition then 1 else 0) sample

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

theorem measurable_responseLabels (C : Calendar) (who : ι) (reply : WithTop ℝ) :
    Measurable (responseLabels C who reply) := by
  apply measurable_finset_iff.mpr
  intro i
  simp only [responseLabels, minimumLabels, Finset.mem_filter, Finset.mem_univ, true_and]
  have hclock (j : ι) : Measurable fun sample : {j : ι // j ≠ who} → unitInterval =>
      responseClock C who reply sample j := by
    by_cases hj : j = who
    · simpa only [responseClock, dite_eq_left hj] using
        (measurable_const : Measurable fun _ : {j : ι // j ≠ who} → unitInterval => reply)
    · simpa only [responseClock, dite_eq_right hj, Function.comp_def] using
        C.measurable_collapseClock.comp
          (measurable_pi_apply (⟨j, hj⟩ : {j : ι // j ≠ who}))
  exact ((hclock i).eq_const ⊤).not.and
    (Measurable.forall fun j => (hclock i).le' (hclock j))

theorem measurable_responsePayoffKernel (C : Calendar) (who : ι) (reply : WithTop ℝ)
    (reward : Finset ι → ℝ) : Measurable (responsePayoffKernel C who reply reward) :=
  (measurable_of_countable reward).comp (measurable_responseLabels C who reply)

private theorem eventually_responseLabels_eq_of_comparisons
    {calendars : ℕ → Calendar} {limit : Calendar}
    (hE : Tendsto (fun k => (calendars k).endpoints) atTop (𝓝 limit.endpoints))
    (hc : Tendsto (fun k => (calendars k).cutoff) atTop (𝓝 limit.cutoff))
    (who : ι) (reply : ℕ → WithTop ℝ) (limitReply : WithTop ℝ)
    (sample : {j : ι // j ≠ who} → unitInterval)
    (hregular : ∀ j, (sample j : ℝ) ∉ limit.exceptionalEndpoints)
    (hcutoff : ∀ j, sample j ≠ limit.cutoff)
    (hreplyTop : ∀ᶠ k in atTop, reply k = ⊤ ↔ limitReply = ⊤)
    (hcross : ∀ j, ∀ᶠ k in atTop,
      (reply k ≤ (calendars k).collapseClock (sample j) ↔
        limitReply ≤ limit.collapseClock (sample j)) ∧
      ((calendars k).collapseClock (sample j) ≤ reply k ↔
        limit.collapseClock (sample j) ≤ limitReply)) :
    ∀ᶠ k in atTop, responseLabels (calendars k) who (reply k) sample =
      responseLabels limit who limitReply sample := by
  have htop (i : ι) : ∀ᶠ k in atTop,
      responseClock (calendars k) who (reply k) sample i = ⊤ ↔
        responseClock limit who limitReply sample i = ⊤ := by
    by_cases hi : i = who
    · simpa only [responseClock, dite_eq_left hi] using hreplyTop
    · simpa only [responseClock, dite_eq_right hi, Calendar.collapseClock_eq_top_iff] using
        Calendar.eventually_cutoff_le_iff hc (hcutoff ⟨i, hi⟩)
  have horder (i j : ι) : ∀ᶠ k in atTop,
      responseClock (calendars k) who (reply k) sample i ≤
          responseClock (calendars k) who (reply k) sample j ↔
        responseClock limit who limitReply sample i ≤
          responseClock limit who limitReply sample j := by
    by_cases hi : i = who <;> by_cases hj : j = who
    · exact Eventually.of_forall fun _ => by simp [responseClock, hi, hj]
    · simpa only [responseClock, dite_eq_left hi, dite_eq_right hj] using
        (hcross ⟨j, hj⟩).mono (fun _ hk => hk.1)
    · simpa only [responseClock, dite_eq_right hi, dite_eq_left hj] using
        (hcross ⟨i, hi⟩).mono (fun _ hk => hk.2)
    · simpa only [responseClock, dite_eq_right hi, dite_eq_right hj] using
        Calendar.eventually_collapseClock_le_iff hE hc (hregular ⟨i, hi⟩)
          (hregular ⟨j, hj⟩) (hcutoff ⟨i, hi⟩) (hcutoff ⟨j, hj⟩)
  filter_upwards [eventually_all.mpr htop,
    eventually_all.mpr fun i => eventually_all.mpr (horder i)] with k hkTop hkOrder
  exact minimumLabels_eq_of_order_and_top hkTop hkOrder

/-- Compatibility is used only to preserve actual atom ties, not to assert
that the moving marks belong to an original response menu. -/
theorem eventually_responseLabels_eq {calendars : ℕ → Calendar} {limit : Calendar}
    (hE : Tendsto (fun k => (calendars k).endpoints) atTop (𝓝 limit.endpoints))
    (hc : Tendsto (fun k => (calendars k).cutoff) atTop (𝓝 limit.cutoff))
    {tester : ℕ → ℝ} {t : ℝ} (ht : Tendsto tester atTop (𝓝 t))
    (hcompatible : ∀ k, (calendars k).AtomCompatible (tester k))
    (who : ι) (sample : {j : ι // j ≠ who} → unitInterval)
    (hregular : ∀ j, (sample j : ℝ) ∉ limit.exceptionalEndpoints)
    (hcutoff : ∀ j, sample j ≠ limit.cutoff) (htester : ∀ j, (sample j : ℝ) ≠ t) :
    ∀ᶠ k in atTop, responseLabels (calendars k) who (tester k : WithTop ℝ) sample =
      responseLabels limit who (t : WithTop ℝ) sample := by
  apply eventually_responseLabels_eq_of_comparisons hE hc who
    (fun k => (tester k : WithTop ℝ)) (t : WithTop ℝ) sample hregular hcutoff
  · exact Eventually.of_forall fun _ => by simp only [WithTop.coe_ne_top]
  · intro j
    exact Calendar.eventually_tester_collapseClock_order hE hc ht hcompatible
      (hregular j) (hcutoff j) (htester j)

theorem eventually_never_responseLabels_eq {calendars : ℕ → Calendar} {limit : Calendar}
    (hE : Tendsto (fun k => (calendars k).endpoints) atTop (𝓝 limit.endpoints))
    (hc : Tendsto (fun k => (calendars k).cutoff) atTop (𝓝 limit.cutoff))
    (who : ι) (sample : {j : ι // j ≠ who} → unitInterval)
    (hregular : ∀ j, (sample j : ℝ) ∉ limit.exceptionalEndpoints)
    (hcutoff : ∀ j, sample j ≠ limit.cutoff) :
    ∀ᶠ k in atTop, responseLabels (calendars k) who ⊤ sample =
      responseLabels limit who ⊤ sample := by
  apply eventually_responseLabels_eq_of_comparisons hE hc who (fun _ => ⊤) ⊤
    sample hregular hcutoff (Eventually.of_forall fun _ => Iff.rfl)
  intro j
  filter_upwards [Calendar.eventually_cutoff_le_iff hc (hcutoff j)] with k hk
  simpa only [WithTop.top_le_iff, Calendar.collapseClock_eq_top_iff, le_top, iff_self,
    and_true] using hk

theorem coalitionKernel_nonneg (C : Calendar) (coalition : Finset ι)
    (sample : ι → unitInterval) : 0 ≤ coalitionKernel C coalition sample := by
  unfold coalitionKernel
  split_ifs <;> norm_num

theorem coalitionKernel_le_one (C : Calendar) (coalition : Finset ι)
    (sample : ι → unitInterval) : coalitionKernel C coalition sample ≤ 1 := by
  unfold coalitionKernel
  split_ifs <;> norm_num

omit [DecidableEq ι] in
/-- Endpoint and cutoff convergence determine the actual eventual finite outcome. -/
theorem eventually_firstLabels_eq {calendars : ℕ → Calendar} {limit : Calendar}
    (hE : Tendsto (fun k => (calendars k).endpoints) atTop (𝓝 limit.endpoints))
    (hc : Tendsto (fun k => (calendars k).cutoff) atTop (𝓝 limit.cutoff))
    (sample : ι → unitInterval)
    (hregular : ∀ i, (sample i : ℝ) ∉ limit.exceptionalEndpoints)
    (hcutoff : ∀ i, sample i ≠ limit.cutoff) :
    ∀ᶠ k in atTop, firstLabels (calendars k) sample = firstLabels limit sample := by
  have htop (i : ι) := Calendar.eventually_cutoff_le_iff hc (hcutoff i)
  have horder (i j : ι) := Calendar.eventually_collapseClock_le_iff hE hc
    (hregular i) (hregular j) (hcutoff i) (hcutoff j)
  filter_upwards [eventually_all.mpr htop,
    eventually_all.mpr fun i => eventually_all.mpr (horder i)] with k hkTop hkOrder
  apply minimumLabels_eq_of_order_and_top
  · intro i
    simpa only [Calendar.collapseClock_eq_top_iff] using hkTop i
  · exact hkOrder

omit [DecidableEq ι] in
/-- The exceptional coordinates are proved null under the actual independent base law. -/
theorem ae_eventually_firstLabels_eq (base : ProbabilityMeasure unitInterval)
    [NullSingletonClass (base : Measure unitInterval)]
    {calendars : ℕ → Calendar} {limit : Calendar}
    (hE : Tendsto (fun k => (calendars k).endpoints) atTop (𝓝 limit.endpoints))
    (hc : Tendsto (fun k => (calendars k).cutoff) atTop (𝓝 limit.cutoff)) :
    ∀ᵐ sample : ι → unitInterval
        ∂(ProbabilityMeasure.pi (fun _ : ι => base) : Measure (ι → unitInterval)),
      ∀ᶠ k in atTop, firstLabels (calendars k) sample = firstLabels limit sample := by
  have hgood : ∀ᵐ x : unitInterval ∂(base : Measure unitInterval),
      (x : ℝ) ∉ limit.exceptionalEndpoints ∧ x ≠ limit.cutoff :=
    (limit.ae_notMem_exceptionalEndpoints (base : Measure unitInterval)).and
      ((base : Measure unitInterval).ae_ne limit.cutoff)
  have hcoords (i : ι) : ∀ᵐ sample : ι → unitInterval
      ∂(ProbabilityMeasure.pi (fun _ : ι => base) : Measure (ι → unitInterval)),
      (sample i : ℝ) ∉ limit.exceptionalEndpoints ∧ sample i ≠ limit.cutoff := by
    have hEval := measurePreserving_eval (fun _ : ι => (base : Measure unitInterval)) i
    exact hEval.quasiMeasurePreserving.ae hgood
  filter_upwards [eventually_all.mpr hcoords] with sample hsample
  exact eventually_firstLabels_eq hE hc sample (fun i => (hsample i).1)
    (fun i => (hsample i).2)

omit [DecidableEq ι] in
theorem norm_payoffKernel_le (C : Calendar) (reward : Finset ι → ℝ)
    (sample : ι → unitInterval) :
    ‖payoffKernel C reward sample‖ ≤ ∑ coalition : Finset ι, ‖reward coalition‖ := by
  exact Finset.single_le_sum (fun coalition _ => norm_nonneg (reward coalition))
    (Finset.mem_univ (firstLabels C sample))

omit [DecidableEq ι] in
theorem integrable_payoffKernel (C : Calendar) (reward : Finset ι → ℝ)
    (μ : Measure (ι → unitInterval)) [IsFiniteMeasure μ] :
    Integrable (payoffKernel C reward) μ :=
  Integrable.of_bound (measurable_payoffKernel C reward).aestronglyMeasurable
    (∑ coalition : Finset ι, ‖reward coalition‖)
    (Eventually.of_forall (norm_payoffKernel_le C reward))

omit [DecidableEq ι] in
/-- Actual payoff kernels converge in L¹; no kernel-convergence premise is supplied. -/
theorem tendsto_integral_norm_payoffKernel_sub (base : ProbabilityMeasure unitInterval)
    [NullSingletonClass (base : Measure unitInterval)]
    {calendars : ℕ → Calendar} {limit : Calendar}
    (hE : Tendsto (fun k => (calendars k).endpoints) atTop (𝓝 limit.endpoints))
    (hc : Tendsto (fun k => (calendars k).cutoff) atTop (𝓝 limit.cutoff))
    (reward : Finset ι → ℝ) :
    Tendsto (fun k => ∫ sample, ‖payoffKernel (calendars k) reward sample -
      payoffKernel limit reward sample‖
      ∂(ProbabilityMeasure.pi (fun _ : ι => base) : Measure (ι → unitInterval)))
      atTop (𝓝 0) := by
  have hdom := tendsto_integral_of_dominated_convergence
    (μ := (ProbabilityMeasure.pi (fun _ : ι => base) : Measure (ι → unitInterval)))
    (F := fun k sample => ‖payoffKernel (calendars k) reward sample -
      payoffKernel limit reward sample‖) (f := fun _ => (0 : ℝ))
    (fun _ => 2 * ∑ coalition : Finset ι, ‖reward coalition‖)
    (fun k => ((measurable_payoffKernel (calendars k) reward).sub
      (measurable_payoffKernel limit reward)).norm.aestronglyMeasurable)
    (integrable_const _) ?_ ?_
  · simpa only [integral_zero] using hdom
  · intro k
    apply Eventually.of_forall
    intro sample
    rw [norm_norm]
    have hfirst := norm_payoffKernel_le (calendars k) reward sample
    have hlast := norm_payoffKernel_le limit reward sample
    exact (norm_sub_le _ _).trans (by linarith)
  · filter_upwards [ae_eventually_firstLabels_eq (ι := ι) base hE hc] with sample hs
    apply tendsto_const_nhds.congr'
    filter_upwards [hs] with k hk
    simp only [payoffKernel, hk, sub_self, norm_zero]

/-- The coalition-event version includes the empty, all-Never outcome. -/
theorem tendsto_integral_norm_coalitionKernel_sub (base : ProbabilityMeasure unitInterval)
    [NullSingletonClass (base : Measure unitInterval)]
    {calendars : ℕ → Calendar} {limit : Calendar}
    (hE : Tendsto (fun k => (calendars k).endpoints) atTop (𝓝 limit.endpoints))
    (hc : Tendsto (fun k => (calendars k).cutoff) atTop (𝓝 limit.cutoff))
    (coalition : Finset ι) :
    Tendsto (fun k => ∫ sample, ‖coalitionKernel (calendars k) coalition sample -
      coalitionKernel limit coalition sample‖
      ∂(ProbabilityMeasure.pi (fun _ : ι => base) : Measure (ι → unitInterval)))
      atTop (𝓝 0) :=
  tendsto_integral_norm_payoffKernel_sub base hE hc
    (fun outcome => if outcome = coalition then 1 else 0)

/-- The only additional response exception is equality with the raw latent
coordinate. Positive-mass equality of collapsed clocks is retained. -/
theorem ae_eventually_responseLabels_eq (base : ProbabilityMeasure unitInterval)
    [NullSingletonClass (base : Measure unitInterval)]
    {calendars : ℕ → Calendar} {limit : Calendar}
    (hE : Tendsto (fun k => (calendars k).endpoints) atTop (𝓝 limit.endpoints))
    (hc : Tendsto (fun k => (calendars k).cutoff) atTop (𝓝 limit.cutoff))
    {tester : ℕ → ℝ} {t : ℝ} (ht : Tendsto tester atTop (𝓝 t))
    (hcompatible : ∀ k, (calendars k).AtomCompatible (tester k)) (who : ι) :
    ∀ᵐ sample : {j : ι // j ≠ who} → unitInterval
        ∂(ProbabilityMeasure.pi (fun _ : {j : ι // j ≠ who} => base) :
          Measure ({j : ι // j ≠ who} → unitInterval)),
      ∀ᶠ k in atTop, responseLabels (calendars k) who (tester k : WithTop ℝ) sample =
        responseLabels limit who (t : WithTop ℝ) sample := by
  have hne : ∀ᵐ x : unitInterval ∂(base : Measure unitInterval), (x : ℝ) ≠ t := by
    simpa only [mem_preimage, mem_singleton_iff] using
      ((countable_singleton t).preimage (f := fun x : unitInterval => (x : ℝ))
        Subtype.val_injective).ae_notMem (base : Measure unitInterval)
  have hgood : ∀ᵐ x : unitInterval ∂(base : Measure unitInterval),
      (x : ℝ) ∉ limit.exceptionalEndpoints ∧ x ≠ limit.cutoff ∧ (x : ℝ) ≠ t :=
    (limit.ae_notMem_exceptionalEndpoints (base : Measure unitInterval)).and
      (((base : Measure unitInterval).ae_ne limit.cutoff).and hne)
  have hcoords (j : {j : ι // j ≠ who}) :
      ∀ᵐ sample : {j : ι // j ≠ who} → unitInterval
          ∂(ProbabilityMeasure.pi (fun _ : {j : ι // j ≠ who} => base) :
            Measure ({j : ι // j ≠ who} → unitInterval)),
        (sample j : ℝ) ∉ limit.exceptionalEndpoints ∧ sample j ≠ limit.cutoff ∧
          (sample j : ℝ) ≠ t := by
    have hEval := measurePreserving_eval
      (fun _ : {j : ι // j ≠ who} => (base : Measure unitInterval)) j
    exact hEval.quasiMeasurePreserving.ae hgood
  filter_upwards [eventually_all.mpr hcoords] with sample hs
  exact eventually_responseLabels_eq hE hc ht hcompatible who sample
    (fun j => (hs j).1) (fun j => (hs j).2.1) (fun j => (hs j).2.2)

theorem ae_eventually_never_responseLabels_eq (base : ProbabilityMeasure unitInterval)
    [NullSingletonClass (base : Measure unitInterval)]
    {calendars : ℕ → Calendar} {limit : Calendar}
    (hE : Tendsto (fun k => (calendars k).endpoints) atTop (𝓝 limit.endpoints))
    (hc : Tendsto (fun k => (calendars k).cutoff) atTop (𝓝 limit.cutoff)) (who : ι) :
    ∀ᵐ sample : {j : ι // j ≠ who} → unitInterval
        ∂(ProbabilityMeasure.pi (fun _ : {j : ι // j ≠ who} => base) :
          Measure ({j : ι // j ≠ who} → unitInterval)),
      ∀ᶠ k in atTop, responseLabels (calendars k) who ⊤ sample =
        responseLabels limit who ⊤ sample := by
  have hgood : ∀ᵐ x : unitInterval ∂(base : Measure unitInterval),
      (x : ℝ) ∉ limit.exceptionalEndpoints ∧ x ≠ limit.cutoff :=
    (limit.ae_notMem_exceptionalEndpoints (base : Measure unitInterval)).and
      ((base : Measure unitInterval).ae_ne limit.cutoff)
  have hcoords (j : {j : ι // j ≠ who}) :
      ∀ᵐ sample : {j : ι // j ≠ who} → unitInterval
          ∂(ProbabilityMeasure.pi (fun _ : {j : ι // j ≠ who} => base) :
            Measure ({j : ι // j ≠ who} → unitInterval)),
        (sample j : ℝ) ∉ limit.exceptionalEndpoints ∧ sample j ≠ limit.cutoff := by
    have hEval := measurePreserving_eval
      (fun _ : {j : ι // j ≠ who} => (base : Measure unitInterval)) j
    exact hEval.quasiMeasurePreserving.ae hgood
  filter_upwards [eventually_all.mpr hcoords] with sample hs
  exact eventually_never_responseLabels_eq hE hc who sample
    (fun j => (hs j).1) (fun j => (hs j).2)

theorem norm_responsePayoffKernel_le (C : Calendar) (who : ι) (reply : WithTop ℝ)
    (reward : Finset ι → ℝ) (sample : {j : ι // j ≠ who} → unitInterval) :
    ‖responsePayoffKernel C who reply reward sample‖ ≤
      ∑ coalition : Finset ι, ‖reward coalition‖ := by
  exact Finset.single_le_sum (fun coalition _ => norm_nonneg (reward coalition))
    (Finset.mem_univ (responseLabels C who reply sample))

theorem integrable_responsePayoffKernel (C : Calendar) (who : ι) (reply : WithTop ℝ)
    (reward : Finset ι → ℝ) (μ : Measure ({j : ι // j ≠ who} → unitInterval))
    [IsFiniteMeasure μ] : Integrable (responsePayoffKernel C who reply reward) μ :=
  Integrable.of_bound (measurable_responsePayoffKernel C who reply reward).aestronglyMeasurable
    (∑ coalition : Finset ι, ‖reward coalition‖)
    (Eventually.of_forall (norm_responsePayoffKernel_le C who reply reward))

theorem integrable_responseCoalitionKernel (C : Calendar) (who : ι) (reply : WithTop ℝ)
    (coalition : Finset ι) (μ : Measure ({j : ι // j ≠ who} → unitInterval))
    [IsFiniteMeasure μ] : Integrable (responseCoalitionKernel C who reply coalition) μ :=
  integrable_responsePayoffKernel C who reply
    (fun outcome => if outcome = coalition then 1 else 0) μ

private theorem responsePayoffKernel_L1_of_ae_labels
    (base : ProbabilityMeasure unitInterval) (calendars : ℕ → Calendar) (limit : Calendar)
    (who : ι) (reply : ℕ → WithTop ℝ) (limitReply : WithTop ℝ)
    (hlabels : ∀ᵐ sample : {j : ι // j ≠ who} → unitInterval
        ∂(ProbabilityMeasure.pi (fun _ : {j : ι // j ≠ who} => base) :
          Measure ({j : ι // j ≠ who} → unitInterval)),
      ∀ᶠ k in atTop, responseLabels (calendars k) who (reply k) sample =
        responseLabels limit who limitReply sample) (reward : Finset ι → ℝ) :
    Tendsto (fun k => ∫ sample,
      ‖responsePayoffKernel (calendars k) who (reply k) reward sample -
        responsePayoffKernel limit who limitReply reward sample‖
      ∂(ProbabilityMeasure.pi (fun _ : {j : ι // j ≠ who} => base) :
        Measure ({j : ι // j ≠ who} → unitInterval))) atTop (𝓝 0) := by
  have hdom := tendsto_integral_of_dominated_convergence
    (μ := (ProbabilityMeasure.pi (fun _ : {j : ι // j ≠ who} => base) :
      Measure ({j : ι // j ≠ who} → unitInterval)))
    (F := fun k sample =>
      ‖responsePayoffKernel (calendars k) who (reply k) reward sample -
        responsePayoffKernel limit who limitReply reward sample‖) (f := fun _ => (0 : ℝ))
    (fun _ => 2 * ∑ coalition : Finset ι, ‖reward coalition‖)
    (fun k => ((measurable_responsePayoffKernel (calendars k) who (reply k) reward).sub
      (measurable_responsePayoffKernel limit who limitReply reward)).norm.aestronglyMeasurable)
    (integrable_const _) ?_ ?_
  · simpa only [integral_zero] using hdom
  · intro k
    apply Eventually.of_forall
    intro sample
    rw [norm_norm]
    have hfirst := norm_responsePayoffKernel_le (calendars k) who (reply k) reward sample
    have hlast := norm_responsePayoffKernel_le limit who limitReply reward sample
    exact (norm_sub_le _ _).trans (by linarith)
  · filter_upwards [hlabels] with sample hs
    apply tendsto_const_nhds.congr'
    filter_upwards [hs] with k hk
    simp only [responsePayoffKernel, hk, sub_self, norm_zero]

/-- Actual moving finite-response kernels converge in L¹ under the geometric inputs. -/
theorem tendsto_integral_norm_responsePayoffKernel_sub
    (base : ProbabilityMeasure unitInterval) [NullSingletonClass (base : Measure unitInterval)]
    {calendars : ℕ → Calendar} {limit : Calendar}
    (hE : Tendsto (fun k => (calendars k).endpoints) atTop (𝓝 limit.endpoints))
    (hc : Tendsto (fun k => (calendars k).cutoff) atTop (𝓝 limit.cutoff))
    {tester : ℕ → ℝ} {t : ℝ} (ht : Tendsto tester atTop (𝓝 t))
    (hcompatible : ∀ k, (calendars k).AtomCompatible (tester k)) (who : ι)
    (reward : Finset ι → ℝ) :
    Tendsto (fun k => ∫ sample,
      ‖responsePayoffKernel (calendars k) who (tester k : WithTop ℝ) reward sample -
        responsePayoffKernel limit who (t : WithTop ℝ) reward sample‖
      ∂(ProbabilityMeasure.pi (fun _ : {j : ι // j ≠ who} => base) :
        Measure ({j : ι // j ≠ who} → unitInterval))) atTop (𝓝 0) :=
  responsePayoffKernel_L1_of_ae_labels base calendars limit who
    (fun k => (tester k : WithTop ℝ)) (t : WithTop ℝ)
    (ae_eventually_responseLabels_eq base hE hc ht hcompatible who) reward

theorem tendsto_integral_norm_never_responsePayoffKernel_sub
    (base : ProbabilityMeasure unitInterval) [NullSingletonClass (base : Measure unitInterval)]
    {calendars : ℕ → Calendar} {limit : Calendar}
    (hE : Tendsto (fun k => (calendars k).endpoints) atTop (𝓝 limit.endpoints))
    (hc : Tendsto (fun k => (calendars k).cutoff) atTop (𝓝 limit.cutoff)) (who : ι)
    (reward : Finset ι → ℝ) :
    Tendsto (fun k => ∫ sample,
      ‖responsePayoffKernel (calendars k) who ⊤ reward sample -
        responsePayoffKernel limit who ⊤ reward sample‖
      ∂(ProbabilityMeasure.pi (fun _ : {j : ι // j ≠ who} => base) :
        Measure ({j : ι // j ≠ who} → unitInterval))) atTop (𝓝 0) :=
  responsePayoffKernel_L1_of_ae_labels base calendars limit who (fun _ => ⊤) ⊤
    (ae_eventually_never_responseLabels_eq base hE hc who) reward

theorem tendsto_integral_norm_responseCoalitionKernel_sub
    (base : ProbabilityMeasure unitInterval) [NullSingletonClass (base : Measure unitInterval)]
    {calendars : ℕ → Calendar} {limit : Calendar}
    (hE : Tendsto (fun k => (calendars k).endpoints) atTop (𝓝 limit.endpoints))
    (hc : Tendsto (fun k => (calendars k).cutoff) atTop (𝓝 limit.cutoff))
    {tester : ℕ → ℝ} {t : ℝ} (ht : Tendsto tester atTop (𝓝 t))
    (hcompatible : ∀ k, (calendars k).AtomCompatible (tester k)) (who : ι)
    (coalition : Finset ι) :
    Tendsto (fun k => ∫ sample,
      ‖responseCoalitionKernel (calendars k) who (tester k : WithTop ℝ) coalition sample -
        responseCoalitionKernel limit who (t : WithTop ℝ) coalition sample‖
      ∂(ProbabilityMeasure.pi (fun _ : {j : ι // j ≠ who} => base) :
        Measure ({j : ι // j ≠ who} → unitInterval))) atTop (𝓝 0) :=
  tendsto_integral_norm_responsePayoffKernel_sub base hE hc ht hcompatible who
    (fun outcome => if outcome = coalition then 1 else 0)

theorem tendsto_integral_norm_never_responseCoalitionKernel_sub
    (base : ProbabilityMeasure unitInterval) [NullSingletonClass (base : Measure unitInterval)]
    {calendars : ℕ → Calendar} {limit : Calendar}
    (hE : Tendsto (fun k => (calendars k).endpoints) atTop (𝓝 limit.endpoints))
    (hc : Tendsto (fun k => (calendars k).cutoff) atTop (𝓝 limit.cutoff)) (who : ι)
    (coalition : Finset ι) :
    Tendsto (fun k => ∫ sample,
      ‖responseCoalitionKernel (calendars k) who ⊤ coalition sample -
        responseCoalitionKernel limit who ⊤ coalition sample‖
      ∂(ProbabilityMeasure.pi (fun _ : {j : ι // j ≠ who} => base) :
        Measure ({j : ι // j ≠ who} → unitInterval))) atTop (𝓝 0) :=
  tendsto_integral_norm_never_responsePayoffKernel_sub base hE hc who
    (fun outcome => if outcome = coalition then 1 else 0)

end MathUE.MarkedCalendar
