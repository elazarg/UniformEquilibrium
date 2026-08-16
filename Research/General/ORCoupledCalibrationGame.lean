/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Research.Quitting.ORRankReduction
import Research.General.CalibrationSliceCompactness

/-!
# A coupled two-button calibrator for OR compression

One player's regret cannot pin that player's own interior mixing probability:
its pure endpoint values do not depend on its prescribed mixture.  Two
opposed binary coordinates can.  This file gives an exact matching-pennies
calibrator whose total endpoint debt vanishes at one prescribed interior
pair and nowhere else on the unit square.

The compact calibration-slice principle then turns positivity of a protected
audit at that single pair into a uniform positive audit-plus-calibration gap.
This is the finite-root `2 protected + 2 calibration` architecture suggested
by OR rank reduction.

The construction is an algebraic normal-form gadget.  A quitting-game
compiler must still realize the two endpoint-value tables without admitting
additional timing-based zero-debt profiles.
-/

noncomputable section

namespace Research.ORCoupledCalibrationGame

open Set
open QuittingORRankReduction

/-- Host endpoint values.  Quit becomes better as the clock's Quit marginal
crosses its target. -/
def hostCalibrationValue (targetClock clock : ℝ) : Bool → ℝ
  | false => 0
  | true => clock - targetClock

/-- Clock endpoint values with the opposite orientation.  Quit becomes
better as the host's Quit marginal falls below its target. -/
def clockCalibrationValue (targetHost host : ℝ) : Bool → ℝ
  | false => 0
  | true => targetHost - host

/-- Sum of the two literal binary endpoint debts. -/
def coupledCalibrationDebt
    (targetHost targetClock host clock : ℝ) : ℝ :=
  binaryDebt host (hostCalibrationValue targetClock clock) +
    binaryDebt clock (clockCalibrationValue targetHost host)

theorem binaryDebt_hostCalibrationValue
    (targetClock host clock : ℝ) :
    binaryDebt host (hostCalibrationValue targetClock clock) =
      max 0 (clock - targetClock) - host * (clock - targetClock) := by
  simp [binaryDebt, bestBinaryValue, prescribedBinaryValue,
    hostCalibrationValue]

theorem binaryDebt_clockCalibrationValue
    (targetHost host clock : ℝ) :
    binaryDebt clock (clockCalibrationValue targetHost host) =
      max 0 (targetHost - host) - clock * (targetHost - host) := by
  simp [binaryDebt, bestBinaryValue, prescribedBinaryValue,
    clockCalibrationValue]

theorem coupledCalibrationDebt_eq
    (targetHost targetClock host clock : ℝ) :
    coupledCalibrationDebt targetHost targetClock host clock =
      (max 0 (clock - targetClock) - host * (clock - targetClock)) +
      (max 0 (targetHost - host) - clock * (targetHost - host)) := by
  rw [coupledCalibrationDebt, binaryDebt_hostCalibrationValue,
    binaryDebt_clockCalibrationValue]

/-- Each binary debt is nonnegative on the unit interval. -/
theorem binaryDebt_nonneg_on_unit
    (quit : ℝ) (value : Bool → ℝ) (hquit0 : 0 ≤ quit)
    (hquit1 : quit ≤ 1) :
    0 ≤ binaryDebt quit value := by
  unfold binaryDebt bestBinaryValue prescribedBinaryValue
  by_cases hvalue : value false ≤ value true
  · rw [max_eq_right hvalue]
    nlinarith
  · have hvalue' : value true ≤ value false := le_of_not_ge hvalue
    rw [max_eq_left hvalue']
    nlinarith

theorem coupledCalibrationDebt_nonneg
    (targetHost targetClock host clock : ℝ)
    (hhost0 : 0 ≤ host) (hhost1 : host ≤ 1)
    (hclock0 : 0 ≤ clock) (hclock1 : clock ≤ 1) :
    0 ≤ coupledCalibrationDebt targetHost targetClock host clock := by
  exact add_nonneg
    (binaryDebt_nonneg_on_unit host _ hhost0 hhost1)
    (binaryDebt_nonneg_on_unit clock _ hclock0 hclock1)

theorem hostDebt_eq_of_clock_le
    (targetClock host clock : ℝ) (hclock : clock ≤ targetClock) :
    binaryDebt host (hostCalibrationValue targetClock clock) =
      host * (targetClock - clock) := by
  rw [binaryDebt_hostCalibrationValue, max_eq_left]
  · ring
  · linarith

theorem hostDebt_eq_of_targetClock_le
    (targetClock host clock : ℝ) (hclock : targetClock ≤ clock) :
    binaryDebt host (hostCalibrationValue targetClock clock) =
      (1 - host) * (clock - targetClock) := by
  rw [binaryDebt_hostCalibrationValue, max_eq_right]
  · ring
  · linarith

theorem clockDebt_eq_of_host_le
    (targetHost host clock : ℝ) (hhost : host ≤ targetHost) :
    binaryDebt clock (clockCalibrationValue targetHost host) =
      (1 - clock) * (targetHost - host) := by
  rw [binaryDebt_clockCalibrationValue, max_eq_right]
  · ring
  · linarith

theorem clockDebt_eq_of_targetHost_le
    (targetHost host clock : ℝ) (hhost : targetHost ≤ host) :
    binaryDebt clock (clockCalibrationValue targetHost host) =
      clock * (host - targetHost) := by
  rw [binaryDebt_clockCalibrationValue, max_eq_left]
  · ring
  · linarith

/-- The coupled calibrator has one and only one zero-debt point in the unit
square when both targets are interior. -/
theorem coupledCalibrationDebt_eq_zero_iff
    (targetHost targetClock host clock : ℝ)
    (htargetHost0 : 0 < targetHost) (htargetHost1 : targetHost < 1)
    (htargetClock0 : 0 < targetClock) (htargetClock1 : targetClock < 1)
    (hhost0 : 0 ≤ host) (hhost1 : host ≤ 1)
    (hclock0 : 0 ≤ clock) (hclock1 : clock ≤ 1) :
    coupledCalibrationDebt targetHost targetClock host clock = 0 ↔
      host = targetHost ∧ clock = targetClock := by
  constructor
  · intro hzero
    have hhostDebtNonneg :=
      binaryDebt_nonneg_on_unit host
        (hostCalibrationValue targetClock clock) hhost0 hhost1
    have hclockDebtNonneg :=
      binaryDebt_nonneg_on_unit clock
        (clockCalibrationValue targetHost host) hclock0 hclock1
    have hhostDebtZero :
        binaryDebt host (hostCalibrationValue targetClock clock) = 0 := by
      unfold coupledCalibrationDebt at hzero
      linarith
    have hclockDebtZero :
        binaryDebt clock (clockCalibrationValue targetHost host) = 0 := by
      unfold coupledCalibrationDebt at hzero
      linarith
    rcases lt_trichotomy clock targetClock with hclockLt | hclockEq | hclockGt
    · have hhostFormula := hostDebt_eq_of_clock_le targetClock host clock hclockLt.le
      have hhostZero : host = 0 := by
        rw [hhostDebtZero] at hhostFormula
        have : 0 < targetClock - clock := sub_pos.mpr hclockLt
        nlinarith
      have hclockFormula := clockDebt_eq_of_host_le targetHost host clock
        (by rw [hhostZero]; exact htargetHost0.le)
      rw [hclockDebtZero, hhostZero] at hclockFormula
      have honeMinusClock : 0 < 1 - clock := by linarith
      nlinarith
    · subst clock
      rcases lt_trichotomy host targetHost with hhostLt | hhostEq | hhostGt
      · have hclockFormula := clockDebt_eq_of_host_le targetHost host targetClock
          hhostLt.le
        rw [hclockDebtZero] at hclockFormula
        have honeMinusClock : 0 < 1 - targetClock := by linarith
        nlinarith
      · exact ⟨hhostEq, rfl⟩
      · have hclockFormula := clockDebt_eq_of_targetHost_le targetHost host
          targetClock hhostGt.le
        rw [hclockDebtZero] at hclockFormula
        nlinarith
    · have hhostFormula := hostDebt_eq_of_targetClock_le targetClock host clock
        hclockGt.le
      have hhostOne : host = 1 := by
        rw [hhostDebtZero] at hhostFormula
        have : 0 < clock - targetClock := sub_pos.mpr hclockGt
        nlinarith
      have hclockFormula := clockDebt_eq_of_targetHost_le targetHost host clock
        (by rw [hhostOne]; exact htargetHost1.le)
      rw [hclockDebtZero, hhostOne] at hclockFormula
      nlinarith
  · rintro ⟨rfl, rfl⟩
    simp [coupledCalibrationDebt_eq]

/-- The calibration debt is continuous in the two displayed marginals. -/
theorem continuous_coupledCalibrationDebt
    (targetHost targetClock : ℝ) :
    Continuous fun point : ℝ × ℝ =>
      coupledCalibrationDebt targetHost targetClock point.1 point.2 := by
  simp_rw [coupledCalibrationDebt_eq]
  fun_prop

/-- Compact profile square for the two calibration marginals. -/
abbrev CalibrationSquare := Set.Icc (0 : ℝ) 1 × Set.Icc (0 : ℝ) 1

/-- **Finite-root calibrated gap.**  A continuous nonnegative protected audit
need only be positive at the one desired hidden-law point.  Adding the two
calibration debts produces a uniform positive gap on the whole square. -/
theorem exists_uniformGap_of_positive_at_calibrationPoint
    (targetHost targetClock : ℝ)
    (htargetHost0 : 0 < targetHost) (htargetHost1 : targetHost < 1)
    (htargetClock0 : 0 < targetClock) (htargetClock1 : targetClock < 1)
    (audit : CalibrationSquare → ℝ)
    (hauditContinuous : Continuous audit)
    (hauditNonneg : ∀ profile, 0 ≤ audit profile)
    (hauditAtTarget : 0 < audit
      (⟨targetHost, htargetHost0.le, htargetHost1.le⟩,
        ⟨targetClock, htargetClock0.le, htargetClock1.le⟩)) :
    ∃ gap : ℝ, 0 < gap ∧
      ∀ profile,
        gap ≤ audit profile +
          coupledCalibrationDebt targetHost targetClock profile.1.1
            profile.2.1 := by
  let calibration : CalibrationSquare → ℝ := fun profile =>
    coupledCalibrationDebt targetHost targetClock profile.1.1 profile.2.1
  have hcalibrationContinuous : Continuous calibration := by
    exact (continuous_coupledCalibrationDebt targetHost targetClock).comp
      ((continuous_subtype_val.comp continuous_fst).prodMk
        (continuous_subtype_val.comp continuous_snd))
  have hcalibrationNonneg : ∀ profile, 0 ≤ calibration profile := by
    intro profile
    exact coupledCalibrationDebt_nonneg targetHost targetClock _ _
      profile.1.2.1 profile.1.2.2 profile.2.2.1 profile.2.2.2
  have hzeroSlice : ∀ profile, calibration profile = 0 →
      0 < audit profile := by
    intro profile hzero
    have heq := (coupledCalibrationDebt_eq_zero_iff targetHost targetClock
      profile.1.1 profile.2.1 htargetHost0 htargetHost1 htargetClock0
      htargetClock1 profile.1.2.1 profile.1.2.2 profile.2.2.1
      profile.2.2.2).1 hzero
    have hprofile : profile =
        (⟨targetHost, htargetHost0.le, htargetHost1.le⟩,
          ⟨targetClock, htargetClock0.le, htargetClock1.le⟩) := by
      apply Prod.ext <;> apply Subtype.ext
      · exact heq.1
      · exact heq.2
    simpa [hprofile] using hauditAtTarget
  simpa only [calibration] using
    CalibrationSliceCompactness.exists_uniformGap_of_positive_on_zeroSlice
      audit calibration hauditContinuous hcalibrationContinuous hauditNonneg
      hcalibrationNonneg hzeroSlice

end Research.ORCoupledCalibrationGame
