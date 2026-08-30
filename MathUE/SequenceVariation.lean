/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Data.Finset.Interval
import Mathlib.Tactic

/-!
# Finite variation bounds for real sequences

Generic accounting lemmas controlling total variation from one-sided
increment bounds.
-/

open scoped BigOperators

namespace Math

/-- A finite sum of successive drops telescopes. -/
theorem sum_range_sub_succ (sequence : ℕ → ℝ) (horizon : ℕ) :
    ∑ index ∈ Finset.range horizon,
        (sequence index - sequence (index + 1)) =
      sequence 0 - sequence horizon := by
  induction horizon with
  | zero => simp
  | succ horizon ih =>
      rw [Finset.sum_range_succ, ih]
      ring

/-! ## Marked positive-part drain -/

/-- A marked-to-endpoint positive drop is bounded by the sum of the
positive one-row drops between them. -/
theorem positivePart_sub_le_sum_positivePart_succDrops
    (sequence : ℕ → ℝ) (mark length : ℕ) :
    max (sequence mark - sequence (mark + length)) 0 ≤
      ∑ offset ∈ Finset.range length,
        max (sequence (mark + offset) -
          sequence (mark + offset + 1)) 0 := by
  apply max_le
  · calc
      sequence mark - sequence (mark + length) =
          ∑ offset ∈ Finset.range length,
            (sequence (mark + offset) -
              sequence (mark + offset + 1)) := by
        simpa [Nat.add_assoc] using
          (sum_range_sub_succ (fun offset => sequence (mark + offset)) length).symm
      _ ≤ ∑ offset ∈ Finset.range length,
          max (sequence (mark + offset) -
            sequence (mark + offset + 1)) 0 := by
        exact Finset.sum_le_sum fun offset _ => le_max_left _ _
  · exact Finset.sum_nonneg fun offset _ => le_max_right _ _

/-- Finite-prefix marked-drain account.  No sign assumptions are required:
marked drift and endpoint compatibility are the exact scalar hypotheses. -/
theorem sum_positivePart_markedDrain_ge
    (entrance marked endpoint exposure residual seam : ℕ → ℝ)
    (rate : ℝ)
    (hdrift : ∀ index,
      rate * exposure index - residual index ≤
        marked index - entrance index)
    (hseam : ∀ index,
      -seam index ≤ entrance (index + 1) - endpoint index)
    (horizon : ℕ) :
    rate * (∑ index ∈ Finset.range horizon, exposure index) -
          (∑ index ∈ Finset.range horizon, residual index) +
        entrance 0 - entrance horizon -
          (∑ index ∈ Finset.range horizon, seam index) ≤
      ∑ index ∈ Finset.range horizon,
        max (marked index - endpoint index) 0 := by
  have htelescope :
      (∑ index ∈ Finset.range horizon,
          (entrance index - entrance (index + 1))) =
        entrance 0 - entrance horizon :=
    sum_range_sub_succ entrance horizon
  have htelescope' :
      (∑ index ∈ Finset.range horizon, entrance index) -
          (∑ index ∈ Finset.range horizon, entrance (index + 1)) =
        entrance 0 - entrance horizon := by
    rw [← Finset.sum_sub_distrib]
    exact htelescope
  calc
    rate * (∑ index ∈ Finset.range horizon, exposure index) -
          (∑ index ∈ Finset.range horizon, residual index) +
        entrance 0 - entrance horizon -
          (∑ index ∈ Finset.range horizon, seam index) =
      ∑ index ∈ Finset.range horizon,
        (rate * exposure index - residual index +
          entrance index - entrance (index + 1) - seam index) := by
      rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib,
        Finset.sum_add_distrib, Finset.sum_sub_distrib,
        ← Finset.mul_sum]
      linear_combination -htelescope'
    _ ≤ ∑ index ∈ Finset.range horizon,
        max (marked index - endpoint index) 0 := by
      apply Finset.sum_le_sum
      intro index _
      have hpositive : marked index - endpoint index ≤
          max (marked index - endpoint index) 0 := le_max_left _ _
      linarith [hdrift index, hseam index]

/-- If every entrance lies in `[0, bound]`, the finite-prefix boundary term
in the marked-drain account costs at most `bound`. -/
theorem sum_positivePart_markedDrain_ge_of_bounded
    (entrance marked endpoint exposure residual seam : ℕ → ℝ)
    (rate bound : ℝ)
    (hdrift : ∀ index,
      rate * exposure index - residual index ≤
        marked index - entrance index)
    (hseam : ∀ index,
      -seam index ≤ entrance (index + 1) - endpoint index)
    (hentrance : ∀ index, 0 ≤ entrance index ∧ entrance index ≤ bound)
    (horizon : ℕ) :
    rate * (∑ index ∈ Finset.range horizon, exposure index) -
          (∑ index ∈ Finset.range horizon, residual index) - bound -
          (∑ index ∈ Finset.range horizon, seam index) ≤
      ∑ index ∈ Finset.range horizon,
        max (marked index - endpoint index) 0 := by
  have haccount := sum_positivePart_markedDrain_ge
    entrance marked endpoint exposure residual seam rate hdrift hseam horizon
  linarith [(hentrance 0).1, (hentrance horizon).2]

/-- Divergent nonnegative exposure and summable nonnegative errors force the
marked positive-part drain itself to be nonsummable. -/
theorem not_summable_positivePart_markedDrain
    (entrance marked endpoint exposure residual seam : ℕ → ℝ)
    (rate bound : ℝ) (hrate : 0 < rate)
    (hdrift : ∀ index,
      rate * exposure index - residual index ≤
        marked index - entrance index)
    (hseam : ∀ index,
      -seam index ≤ entrance (index + 1) - endpoint index)
    (hentrance : ∀ index, 0 ≤ entrance index ∧ entrance index ≤ bound)
    (hexposure : ∀ index, 0 ≤ exposure index)
    (hexposureDiverges : ¬Summable exposure)
    (hresidual : ∀ index, 0 ≤ residual index)
    (hresidualSummable : Summable residual)
    (hseamNonneg : ∀ index, 0 ≤ seam index)
    (hseamSummable : Summable seam) :
    ¬Summable (fun index => max (marked index - endpoint index) 0) := by
  intro hdrainSummable
  let ceiling :=
    (∑' index, max (marked index - endpoint index) 0) +
      (∑' index, residual index) + bound + ∑' index, seam index
  have hexposureTop : Filter.Tendsto (fun horizon =>
      ∑ index ∈ Finset.range horizon, exposure index)
      Filter.atTop Filter.atTop :=
    (not_summable_iff_tendsto_nat_atTop_of_nonneg hexposure).1
      hexposureDiverges
  obtain ⟨horizon, hlarge⟩ :=
    (hexposureTop.eventually
      (Filter.eventually_gt_atTop (ceiling / rate))).exists
  have hrateLarge : ceiling < rate *
      (∑ index ∈ Finset.range horizon, exposure index) :=
    by simpa [mul_comm] using (div_lt_iff₀ hrate).mp hlarge
  have haccount := sum_positivePart_markedDrain_ge_of_bounded
    entrance marked endpoint exposure residual seam rate bound hdrift hseam
      hentrance horizon
  have hdrainLe :
      (∑ index ∈ Finset.range horizon,
          max (marked index - endpoint index) 0) ≤
        ∑' index, max (marked index - endpoint index) 0 :=
    hdrainSummable.sum_le_tsum _ fun index _ => le_max_right _ _
  have hresidualLe :
      (∑ index ∈ Finset.range horizon, residual index) ≤
        ∑' index, residual index :=
    hresidualSummable.sum_le_tsum _ fun index _ => hresidual index
  have hseamLe :
      (∑ index ∈ Finset.range horizon, seam index) ≤
        ∑' index, seam index :=
    hseamSummable.sum_le_tsum _ fun index _ => hseamNonneg index
  dsimp only [ceiling] at hrateLarge
  linarith

/-- For every positive loss in slope, the marked drain reaches the remaining
slope infinitely often. -/
theorem frequently_positivePart_markedDrain_ge
    (entrance marked endpoint exposure residual seam : ℕ → ℝ)
    (rate bound : ℝ)
    (hdrift : ∀ index,
      rate * exposure index - residual index ≤
        marked index - entrance index)
    (hseam : ∀ index,
      -seam index ≤ entrance (index + 1) - endpoint index)
    (hentrance : ∀ index, 0 ≤ entrance index ∧ entrance index ≤ bound)
    (hexposure : ∀ index, 0 ≤ exposure index)
    (hexposureDiverges : ¬Summable exposure)
    (hresidual : ∀ index, 0 ≤ residual index)
    (hresidualSummable : Summable residual)
    (hseamNonneg : ∀ index, 0 ≤ seam index)
    (hseamSummable : Summable seam)
    (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    Filter.Frequently (fun index =>
      (rate - epsilon) * exposure index ≤
        max (marked index - endpoint index) 0) Filter.atTop := by
  by_contra hfrequent
  rw [Filter.not_frequently] at hfrequent
  obtain ⟨start, htail⟩ := Filter.eventually_atTop.mp hfrequent
  have hexposureShift :
      ¬Summable (fun offset => exposure (start + offset)) := by
    intro hsummable
    have hshift : Summable (fun offset => exposure (offset + start)) := by
      simpa [Nat.add_comm] using hsummable
    exact hexposureDiverges ((summable_nat_add_iff start).1 hshift)
  have hexposureShiftTop : Filter.Tendsto (fun horizon =>
      ∑ offset ∈ Finset.range horizon, exposure (start + offset))
      Filter.atTop Filter.atTop :=
    (not_summable_iff_tendsto_nat_atTop_of_nonneg
      (fun offset => hexposure (start + offset))).1 hexposureShift
  let ceiling := (∑' index, residual index) + bound + ∑' index, seam index
  obtain ⟨horizon, hlarge⟩ :=
    (hexposureShiftTop.eventually
      (Filter.eventually_gt_atTop (ceiling / epsilon))).exists
  have hepsilonLarge : ceiling < epsilon *
      (∑ offset ∈ Finset.range horizon,
        exposure (start + offset)) :=
    by simpa [mul_comm] using (div_lt_iff₀ hepsilon).mp hlarge
  have haccount := sum_positivePart_markedDrain_ge_of_bounded
    (fun offset => entrance (start + offset))
    (fun offset => marked (start + offset))
    (fun offset => endpoint (start + offset))
    (fun offset => exposure (start + offset))
    (fun offset => residual (start + offset))
    (fun offset => seam (start + offset)) rate bound
    (fun offset => hdrift (start + offset))
    (fun offset => by simpa [Nat.add_assoc] using hseam (start + offset))
    (fun offset => hentrance (start + offset)) horizon
  have hupper :
      (∑ offset ∈ Finset.range horizon,
          max (marked (start + offset) - endpoint (start + offset)) 0) ≤
        (rate - epsilon) *
          ∑ offset ∈ Finset.range horizon,
            exposure (start + offset) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro offset _
    exact le_of_not_ge (htail (start + offset) (by omega))
  have hresidualLe :
      (∑ offset ∈ Finset.range horizon, residual (start + offset)) ≤
        ∑' index, residual index := by
    have hsuffix : Summable (fun offset => residual (start + offset)) := by
      simpa [Nat.add_comm] using
        (summable_nat_add_iff start).2 hresidualSummable
    have hfinite := hsuffix.sum_le_tsum
      (Finset.range horizon) (fun offset _ => hresidual (start + offset))
    have hsplit := hresidualSummable.sum_add_tsum_nat_add start
    have hprefix : 0 ≤
        ∑ index ∈ Finset.range start, residual index :=
      Finset.sum_nonneg fun index _ => hresidual index
    have hsplit' :
        (∑ index ∈ Finset.range start, residual index) +
            (∑' offset, residual (start + offset)) =
          ∑' index, residual index := by
      simpa [Nat.add_comm] using hsplit
    have htailLe : (∑' offset, residual (start + offset)) ≤
        ∑' index, residual index := by linarith
    exact hfinite.trans htailLe
  have hseamLe :
      (∑ offset ∈ Finset.range horizon, seam (start + offset)) ≤
        ∑' index, seam index := by
    have hsuffix : Summable (fun offset => seam (start + offset)) := by
      simpa [Nat.add_comm] using
        (summable_nat_add_iff start).2 hseamSummable
    have hfinite := hsuffix.sum_le_tsum
      (Finset.range horizon) (fun offset _ => hseamNonneg (start + offset))
    have hsplit := hseamSummable.sum_add_tsum_nat_add start
    have hprefix : 0 ≤ ∑ index ∈ Finset.range start, seam index :=
      Finset.sum_nonneg fun index _ => hseamNonneg index
    have hsplit' :
        (∑ index ∈ Finset.range start, seam index) +
            (∑' offset, seam (start + offset)) =
          ∑' index, seam index := by
      simpa [Nat.add_comm] using hsplit
    have htailLe : (∑' offset, seam (start + offset)) ≤
        ∑' index, seam index := by linarith
    exact hfinite.trans htailLe
  dsimp only [ceiling] at hepsilonLarge
  linarith

/-- A bounded real sequence whose positive increments are charged to a
nonnegative clock has controlled finite total variation. -/
theorem sum_abs_succ_sub_le_of_bounded_of_increase_le_clock
    (value charge : ℕ → ℝ) (bound : ℝ)
    (hbound : ∀ time, |value time| ≤ bound)
    (hcharge : ∀ time, 0 ≤ charge time)
    (hincrease : ∀ time,
      value (time + 1) - value time ≤ 2 * bound * charge time)
    (horizon : ℕ) :
    (∑ time ∈ Finset.range horizon,
        |value (time + 1) - value time|) ≤
      2 * bound + 4 * bound *
        (∑ time ∈ Finset.range horizon, charge time) := by
  have hM : 0 ≤ bound := (abs_nonneg (value 0)).trans (hbound 0)
  have hpositive : ∀ time,
      max (value (time + 1) - value time) 0 ≤
        2 * bound * charge time := by
    intro time
    exact max_le (hincrease time)
      (mul_nonneg (mul_nonneg (by norm_num) hM) (hcharge time))
  have hsumPositive :
      (∑ time ∈ Finset.range horizon,
          max (value (time + 1) - value time) 0) ≤
        2 * bound * (∑ time ∈ Finset.range horizon, charge time) := by
    calc
      (∑ time ∈ Finset.range horizon,
          max (value (time + 1) - value time) 0) ≤
          ∑ time ∈ Finset.range horizon, 2 * bound * charge time :=
        Finset.sum_le_sum fun time _ => hpositive time
      _ = 2 * bound * (∑ time ∈ Finset.range horizon, charge time) := by
        rw [Finset.mul_sum]
  have habsIdentity : ∀ x : ℝ, |x| = 2 * max x 0 - x := by
    intro x
    by_cases hx : 0 ≤ x
    · rw [abs_of_nonneg hx, max_eq_left hx]
      ring
    · have hx' : x ≤ 0 := le_of_not_ge hx
      rw [abs_of_nonpos hx', max_eq_right hx']
      ring
  have htelescope :
      (∑ time ∈ Finset.range horizon,
          (value (time + 1) - value time)) =
        value horizon - value 0 :=
    Finset.sum_range_sub value horizon
  have hspan : value 0 - value horizon ≤ 2 * bound := by
    have h0 := (abs_le.mp (hbound 0)).2
    have hN := (abs_le.mp (hbound horizon)).1
    linarith
  rw [Finset.sum_congr rfl (fun time _ => habsIdentity _),
    Finset.sum_sub_distrib, ← Finset.mul_sum, htelescope]
  linarith

end Math
