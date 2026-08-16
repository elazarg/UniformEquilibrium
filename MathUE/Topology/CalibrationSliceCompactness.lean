/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Order.Compact

/-!
# Positive gaps from compact zero slices

Let `audit` and `calibration` be continuous nonnegative functions on a compact
space. If `audit` is positive wherever `calibration` vanishes, then their sum
has a uniform positive lower bound. The same conclusion holds for a finite
family of nonnegative calibration channels.

No nonemptiness assumption on the compact space is needed: on an empty space,
any positive number is a uniform lower bound.
-/

noncomputable section

namespace Math
namespace Topology
namespace CalibrationSliceCompactness

open Set

/-- Positivity on the zero slice of a nonnegative calibration function gives
a uniform positive lower bound for the sum on a compact space. -/
theorem exists_uniformGap_of_positive_on_zeroSlice
    {Profile : Type*} [TopologicalSpace Profile] [CompactSpace Profile]
    (audit calibration : Profile → ℝ)
    (hauditContinuous : Continuous audit)
    (hcalibrationContinuous : Continuous calibration)
    (hauditNonneg : ∀ profile, 0 ≤ audit profile)
    (hcalibrationNonneg : ∀ profile, 0 ≤ calibration profile)
    (hzeroSlice : ∀ profile, calibration profile = 0 → 0 < audit profile) :
    ∃ gap : ℝ, 0 < gap ∧
      ∀ profile, gap ≤ audit profile + calibration profile := by
  cases isEmpty_or_nonempty Profile with
  | inl hProfile =>
      letI : IsEmpty Profile := hProfile
      exact ⟨1, zero_lt_one, fun profile ↦ isEmptyElim profile⟩
  | inr hProfile =>
      letI : Nonempty Profile := hProfile
      let total : Profile → ℝ := fun profile ↦
        audit profile + calibration profile
      have htotalContinuous : Continuous total :=
        hauditContinuous.add hcalibrationContinuous
      obtain ⟨minimizer, _hmem, hminimal⟩ :=
        (isCompact_univ : IsCompact (Set.univ : Set Profile)).exists_isMinOn
          Set.univ_nonempty htotalContinuous.continuousOn
      have htotalPos : 0 < total minimizer := by
        by_cases hcalibrationZero : calibration minimizer = 0
        · dsimp only [total]
          rw [hcalibrationZero, add_zero]
          exact hzeroSlice minimizer hcalibrationZero
        · have hcalibrationPos : 0 < calibration minimizer :=
            lt_of_le_of_ne (hcalibrationNonneg minimizer)
              (Ne.symm hcalibrationZero)
          dsimp only [total]
          linarith [hauditNonneg minimizer]
      refine ⟨total minimizer, htotalPos, ?_⟩
      intro profile
      exact hminimal (Set.mem_univ profile)

/-- Positivity on the joint zero slice of finitely many nonnegative
calibration functions gives a uniform positive lower bound for their sum with
the audit function. -/
theorem exists_uniformGap_of_positive_on_jointZeroSlice
    {Profile Channel : Type*} [TopologicalSpace Profile]
    [CompactSpace Profile] [Fintype Channel]
    (audit : Profile → ℝ) (calibration : Channel → Profile → ℝ)
    (hauditContinuous : Continuous audit)
    (hcalibrationContinuous : ∀ channel, Continuous (calibration channel))
    (hauditNonneg : ∀ profile, 0 ≤ audit profile)
    (hcalibrationNonneg : ∀ channel profile, 0 ≤ calibration channel profile)
    (hzeroSlice : ∀ profile,
      (∀ channel, calibration channel profile = 0) → 0 < audit profile) :
    ∃ gap : ℝ, 0 < gap ∧
      ∀ profile, gap ≤ audit profile + ∑ channel, calibration channel profile := by
  let totalCalibration : Profile → ℝ := fun profile ↦
    ∑ channel, calibration channel profile
  have htotalCalibrationContinuous : Continuous totalCalibration :=
    continuous_finsetSum Finset.univ fun channel _ ↦
      hcalibrationContinuous channel
  have htotalCalibrationNonneg : ∀ profile, 0 ≤ totalCalibration profile := by
    intro profile
    exact Finset.sum_nonneg fun channel _ ↦
      hcalibrationNonneg channel profile
  have htotalZero : ∀ profile, totalCalibration profile = 0 →
      0 < audit profile := by
    intro profile hsum
    apply hzeroSlice profile
    intro channel
    have hterm :=
      (Finset.sum_eq_zero_iff_of_nonneg (fun other _ ↦
        hcalibrationNonneg other profile)).mp hsum
    exact hterm channel (Finset.mem_univ channel)
  simpa only [totalCalibration] using
    exists_uniformGap_of_positive_on_zeroSlice audit totalCalibration
      hauditContinuous htotalCalibrationContinuous hauditNonneg
      htotalCalibrationNonneg htotalZero

end CalibrationSliceCompactness
end Topology
end Math
