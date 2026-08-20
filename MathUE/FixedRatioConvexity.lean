import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Module
import Mathlib.Topology.Order.Monotone

/-!
# Closed fixed-ratio sets are convex

A closed subset of a real normed space that contains one fixed nontrivial
affine combination of each ordered pair of its points is convex.  The proof
uses the gap between the last point before, and the first point after, a
missing point on a chord.
-/

namespace MathUE

open Set

/-- A closed set stable under one fixed affine ratio is convex. -/
theorem convex_of_isClosed_of_fixedRatio
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {s : Set E} (hs : IsClosed s) {c : ℝ} (hc0 : 0 < c) (hc1 : c < 1)
    (hcombo : ∀ x ∈ s, ∀ y ∈ s, c • x + (1 - c) • y ∈ s) :
    Convex ℝ s := by
  intro x hx y hy a b ha hb hab
  have hb_eq : b = 1 - a := by linarith
  subst b
  let chord : ℝ → E := fun t ↦ t • x + (1 - t) • y
  let times : Set ℝ := chord ⁻¹' s
  have hchord : Continuous chord := by
    fun_prop
  have htimesClosed : IsClosed times := hs.preimage hchord
  have hzero : 0 ∈ times := by
    change chord 0 ∈ s
    simpa [chord] using hy
  have hone : 1 ∈ times := by
    change chord 1 ∈ s
    simpa [chord] using hx
  have htimesCombo {u v : ℝ} (hu : u ∈ times) (hv : v ∈ times) :
      c * u + (1 - c) * v ∈ times := by
    change chord (c * u + (1 - c) * v) ∈ s
    have h := hcombo (chord u) hu (chord v) hv
    convert h using 1
    simp only [chord, smul_add]
    module
  have hall : Icc (0 : ℝ) 1 ⊆ times := by
    intro t ht
    by_contra htTimes
    let before : Set ℝ := times ∩ Iic t
    let after : Set ℝ := times ∩ Ici t
    have hbeforeClosed : IsClosed before := htimesClosed.inter isClosed_Iic
    have hafterClosed : IsClosed after := htimesClosed.inter isClosed_Ici
    have hbeforeNonempty : before.Nonempty := ⟨0, hzero, ht.1⟩
    have hafterNonempty : after.Nonempty := ⟨1, hone, ht.2⟩
    have hbeforeBounded : BddAbove before := ⟨t, fun _ hz ↦ hz.2⟩
    have hafterBounded : BddBelow after := ⟨t, fun _ hz ↦ hz.2⟩
    let u := sSup before
    let v := sInf after
    have huBefore : u ∈ before :=
      hbeforeClosed.csSup_mem hbeforeNonempty hbeforeBounded
    have hvAfter : v ∈ after :=
      hafterClosed.csInf_mem hafterNonempty hafterBounded
    have huTimes : u ∈ times := huBefore.1
    have hvTimes : v ∈ times := hvAfter.1
    have hu_le_t : u ≤ t := huBefore.2
    have ht_le_v : t ≤ v := hvAfter.2
    have hu_lt_t : u < t := by
      apply lt_of_le_of_ne hu_le_t
      intro hut
      apply htTimes
      rwa [← hut]
    have ht_lt_v : t < v := by
      apply lt_of_le_of_ne ht_le_v
      intro htv
      apply htTimes
      rwa [htv]
    have huv : u < v := hu_lt_t.trans ht_lt_v
    have hgap : ∀ z ∈ Ioo u v, z ∉ times := by
      intro z hz hzTimes
      by_cases hzt : z ≤ t
      · have hzBefore : z ∈ before := ⟨hzTimes, hzt⟩
        have hzu : z ≤ u := le_csSup hbeforeBounded hzBefore
        exact (not_lt_of_ge hzu) hz.1
      · have htz : t ≤ z := (lt_of_not_ge hzt).le
        have hzAfter : z ∈ after := ⟨hzTimes, htz⟩
        have hvz : v ≤ z := csInf_le hafterBounded hzAfter
        exact (not_lt_of_ge hvz) hz.2
    let z := c * u + (1 - c) * v
    have hc' : 0 < 1 - c := sub_pos.mpr hc1
    have hzu : u < z := by
      dsimp only [z]
      nlinarith [mul_pos hc' (sub_pos.mpr huv)]
    have hzv : z < v := by
      dsimp only [z]
      nlinarith [mul_pos hc0 (sub_pos.mpr huv)]
    exact hgap z ⟨hzu, hzv⟩ (htimesCombo huTimes hvTimes)
  have ha1 : a ≤ 1 := by linarith
  exact hall ⟨ha, ha1⟩

end MathUE
