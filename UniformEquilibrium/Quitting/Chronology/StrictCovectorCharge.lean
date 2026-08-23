/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.RewardBound
import MathUE.Topology.TailSupConvergence

/-!
# Strict covector accounting for quitting absorption charge

A single covector which makes every late value increment pay a fixed positive
multiple of one-row absorption controls arbitrary varying horizons.  The
result is purely chronological: it does not assume a fixed active face or a
periodic word.
-/

noncomputable section

namespace GameTheory

open Filter

variable {ι : Type} [Fintype ι]

/-- Pairing of a payoff vector with a finite-player covector. -/
def quittingCovectorPairing (covector value : Payoff ι) : ℝ :=
  ∑ who, covector who * value who

theorem quittingCovectorPairing_sub
    (covector first second : Payoff ι) :
    quittingCovectorPairing covector (first - second) =
      quittingCovectorPairing covector first -
        quittingCovectorPairing covector second := by
  simp only [quittingCovectorPairing, Pi.sub_apply, mul_sub,
    Finset.sum_sub_distrib]

/-- An `ℓ¹` covector norm controls its pairing with a coordinatewise bounded
error vector. -/
theorem abs_quittingCovectorPairing_le
    (covector error : Payoff ι) {bound : ℝ}
    (hbound : ∀ who, |error who| ≤ bound) :
    |quittingCovectorPairing covector error| ≤
      (∑ who, |covector who|) * bound := by
  calc
    |quittingCovectorPairing covector error| ≤
        ∑ who, |covector who * error who| := by
      exact Finset.abs_sum_le_sum_abs _ _
    _ = ∑ who, |covector who| * |error who| := by
      apply Finset.sum_congr rfl
      intro who _
      exact abs_mul _ _
    _ ≤ ∑ who, |covector who| * bound := by
      exact Finset.sum_le_sum fun who _ ↦
        mul_le_mul_of_nonneg_left (hbound who) (abs_nonneg _)
    _ = (∑ who, |covector who|) * bound := by
      rw [Finset.sum_mul]

/-- Arbitrary-horizon telescope of a common strict covector inequality. -/
theorem strictCovector_mul_sum_le_pairing_sub
    (value : ℕ → Payoff ι) (charge : ℕ → ℝ)
    (covector : Payoff ι) (slope : ℝ) (cutoff start finish : ℕ)
    (hcutoff : cutoff ≤ start) (hfinish : start ≤ finish)
    (hstep : ∀ time, cutoff ≤ time →
      slope * charge time ≤
        quittingCovectorPairing covector
          (value (time + 1) - value time)) :
    slope * (∑ time ∈ Finset.Ico start finish, charge time) ≤
      quittingCovectorPairing covector (value finish - value start) := by
  rw [Finset.mul_sum]
  calc
    (∑ time ∈ Finset.Ico start finish, slope * charge time) ≤
        ∑ time ∈ Finset.Ico start finish,
          quittingCovectorPairing covector
            (value (time + 1) - value time) := by
      apply Finset.sum_le_sum
      intro time htime
      exact hstep time (hcutoff.trans (Finset.mem_Ico.1 htime).1)
    _ = ∑ time ∈ Finset.Ico start finish,
        (quittingCovectorPairing covector (value (time + 1)) -
          quittingCovectorPairing covector (value time)) := by
      apply Finset.sum_congr rfl
      intro time _
      rw [← quittingCovectorPairing_sub]
    _ = quittingCovectorPairing covector (value finish) -
        quittingCovectorPairing covector (value start) := by
      let scalar : ℕ → ℝ := fun time ↦
        quittingCovectorPairing covector (value time)
      have htelescope : ∀ length,
          (∑ time ∈ Finset.range length,
              (scalar (time + 1) - scalar time)) =
            scalar length - scalar 0 := by
        intro length
        induction length with
        | zero => simp
        | succ length ih =>
            rw [Finset.sum_range_succ, ih]
            ring
      rw [Finset.sum_Ico_eq_sub _ hfinish, htelescope finish,
        htelescope start]
      dsimp only [scalar]
      ring
    _ = quittingCovectorPairing covector (value finish - value start) := by
      rw [quittingCovectorPairing_sub]

/-- A positive common covector slope and a uniform upper bound on its total
motion force finite tail charge. -/
theorem summable_charge_natAdd_of_strictCovector
    (value : ℕ → Payoff ι) (charge : ℕ → ℝ)
    (covector : Payoff ι) {slope bound : ℝ} (cutoff : ℕ)
    (hslope : 0 < slope) (hcharge : ∀ time, 0 ≤ charge time)
    (hstep : ∀ time, cutoff ≤ time →
      slope * charge time ≤
        quittingCovectorPairing covector
          (value (time + 1) - value time))
    (hbound : ∀ finish, cutoff ≤ finish →
      quittingCovectorPairing covector (value finish - value cutoff) ≤ bound) :
    Summable (fun offset ↦ charge (cutoff + offset)) := by
  apply summable_of_sum_range_le
  · intro offset
    exact hcharge (cutoff + offset)
  · intro length
    have htelescope := strictCovector_mul_sum_le_pairing_sub
      value charge covector slope cutoff cutoff (cutoff + length)
        le_rfl (Nat.le_add_right cutoff length) hstep
    have hsum :
        (∑ time ∈ Finset.Ico cutoff (cutoff + length), charge time) =
          ∑ offset ∈ Finset.range length, charge (cutoff + offset) := by
      rw [Finset.sum_Ico_eq_sum_range]
      simp
    rw [hsum] at htelescope
    have hupper := hbound (cutoff + length) (Nat.le_add_right cutoff length)
    have hscaled : ∑ offset ∈ Finset.range length,
        charge (cutoff + offset) ≤ bound / slope := by
      rw [le_div_iff₀ hslope]
      simpa [mul_comm] using htelescope.trans hupper
    exact hscaled

/-- Convergence of the value path supplies the bounded covector motion needed
by the strict-covector summability criterion. -/
theorem summable_charge_natAdd_of_tendsto_strictCovector
    (value : ℕ → Payoff ι) (boundary : Payoff ι) (charge : ℕ → ℝ)
    (covector : Payoff ι) {slope : ℝ} (cutoff : ℕ)
    (hslope : 0 < slope) (hcharge : ∀ time, 0 ≤ charge time)
    (hvalue : ∀ who,
      Filter.Tendsto (fun time ↦ value time who) Filter.atTop
        (nhds (boundary who)))
    (hstep : ∀ time, cutoff ≤ time →
      slope * charge time ≤
        quittingCovectorPairing covector
          (value (time + 1) - value time)) :
    Summable (fun offset ↦ charge (cutoff + offset)) := by
  have hpair : Filter.Tendsto
      (fun finish ↦ quittingCovectorPairing covector
        (value finish - value cutoff)) Filter.atTop
      (nhds (quittingCovectorPairing covector
        (boundary - value cutoff))) := by
    unfold quittingCovectorPairing
    apply tendsto_finsetSum
    intro who _
    exact ((hvalue who).sub_const (value cutoff who)).const_mul
      (covector who)
  rcases hpair.bddAbove_range with ⟨bound, hbound⟩
  apply summable_charge_natAdd_of_strictCovector value charge covector
    cutoff hslope hcharge hstep
  intro finish _
  exact hbound ⟨finish, rfl⟩

/-- The strict finite-horizon telescope passes to the exact infinite tail
charge at every date beyond the common cutoff. -/
theorem strictCovector_mul_tsum_le_pairing_limit
    (value : ℕ → Payoff ι) (boundary : Payoff ι) (charge : ℕ → ℝ)
    (covector : Payoff ι) {slope : ℝ} (cutoff start : ℕ)
    (hcutoff : cutoff ≤ start) (hslope : 0 < slope)
    (hcharge : ∀ time, 0 ≤ charge time)
    (hvalue : ∀ who,
      Filter.Tendsto (fun time ↦ value time who) Filter.atTop
        (nhds (boundary who)))
    (hstep : ∀ time, cutoff ≤ time →
      slope * charge time ≤
        quittingCovectorPairing covector
          (value (time + 1) - value time)) :
    slope * (∑' offset, charge (start + offset)) ≤
      quittingCovectorPairing covector (boundary - value start) := by
  have hsummable : Summable (fun offset ↦ charge (start + offset)) := by
    have hbase := summable_charge_natAdd_of_tendsto_strictCovector
      value boundary charge covector cutoff hslope hcharge hvalue hstep
    have hshift := hbase.comp_injective
      (show Function.Injective (fun offset : ℕ ↦ (start - cutoff) + offset) by
        intro first second heq
        exact Nat.add_left_cancel heq)
    have hfun : ((fun offset ↦ charge (cutoff + offset)) ∘
        (fun offset ↦ start - cutoff + offset)) =
        (fun offset ↦ charge (start + offset)) := by
      funext offset
      simp only [Function.comp_apply]
      rw [← Nat.add_assoc, Nat.add_sub_of_le hcutoff]
    rw [hfun] at hshift
    exact hshift
  have hpartial : ∀ length,
      slope * (∑ offset ∈ Finset.range length, charge (start + offset)) ≤
        quittingCovectorPairing covector
          (value (start + length) - value start) := by
    intro length
    have h := strictCovector_mul_sum_le_pairing_sub value charge covector
      slope cutoff start (start + length) hcutoff
        (Nat.le_add_right start length) hstep
    rw [Finset.sum_Ico_eq_sum_range] at h
    simpa only [Nat.add_sub_cancel_left] using h
  have hleft : Filter.Tendsto (fun length ↦
      slope * (∑ offset ∈ Finset.range length, charge (start + offset)))
      Filter.atTop (nhds (slope * ∑' offset, charge (start + offset))) :=
    hsummable.hasSum.tendsto_sum_nat.const_mul slope
  have hright : Filter.Tendsto (fun length ↦
      quittingCovectorPairing covector
        (value (start + length) - value start)) Filter.atTop
      (nhds (quittingCovectorPairing covector
        (boundary - value start))) := by
    unfold quittingCovectorPairing
    apply tendsto_finsetSum Finset.univ
    intro who _
    have hshift := (hvalue who).comp (tendsto_add_atTop_nat start)
    simpa [Function.comp_def, Nat.add_comm, Pi.sub_apply] using
      ((hshift.sub_const (value start who)).const_mul (covector who))
  exact le_of_tendsto_of_tendsto' hleft hright hpartial

end GameTheory
