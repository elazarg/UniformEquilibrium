/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Mathlib

/-!
# Compact calibration slices turn local audit into a global gap

A fixed-table rank reduction need not reproduce the source audit on every
target profile.  It is enough to reproduce it on the closed locus where a
calibration defect vanishes, provided the calibration defect is nonnegative
everywhere.

On a compact profile carrier, if

* `protected` is nonnegative and strictly positive on `calibration = 0`, and
* `calibration` is nonnegative,

then `protected + calibration` has a uniform positive lower bound on the
whole carrier.  This is the exact topological interface suggested by OR
compression: preserve three protected coordinates on the fixed hidden-law
slice and use the exceptional host/auditor geometry to exclude profiles off
that slice.

The theorem does not construct the quitting-game calibration defect.  In
particular, ordinary best-response debt of a passive auditor need not work:
the auditor may simply switch to its preferred endpoint.  A downstream
producer needs a coupled host--auditor gadget whose joint zero-debt set is the
desired hidden-law locus and whose payoff component does not cancel the
protected audit.
-/

noncomputable section

namespace Experiments
namespace CalibrationSliceCompactness

open Set

/-- **Compact calibration-slice principle.**  Positivity only on the exact
calibration slice becomes a uniform global positive gap after adding the
nonnegative calibration defect. -/
theorem exists_uniformGap_of_positive_on_zeroSlice
    {Profile : Type*} [TopologicalSpace Profile] [CompactSpace Profile]
    [Nonempty Profile]
    (audit calibration : Profile → ℝ)
    (hauditContinuous : Continuous audit)
    (hcalibrationContinuous : Continuous calibration)
    (hauditNonneg : ∀ profile, 0 ≤ audit profile)
    (hcalibrationNonneg : ∀ profile, 0 ≤ calibration profile)
    (hzeroSlice : ∀ profile, calibration profile = 0 →
      0 < audit profile) :
    ∃ gap : ℝ, 0 < gap ∧
      ∀ profile, gap ≤ audit profile + calibration profile := by
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

/-- Several nonnegative calibration channels can be summed first.  Their
joint zero set is the intersection of their individual zero sets. -/
theorem exists_uniformGap_of_positive_on_jointZeroSlice
    {Profile Channel : Type*} [TopologicalSpace Profile]
    [CompactSpace Profile] [Nonempty Profile] [Fintype Channel]
    (audit : Profile → ℝ) (calibration : Channel → Profile → ℝ)
    (hauditContinuous : Continuous audit)
    (hcalibrationContinuous : ∀ channel, Continuous (calibration channel))
    (hauditNonneg : ∀ profile, 0 ≤ audit profile)
    (hcalibrationNonneg : ∀ channel profile,
      0 ≤ calibration channel profile)
    (hzeroSlice : ∀ profile,
      (∀ channel, calibration channel profile = 0) →
        0 < audit profile) :
    ∃ gap : ℝ, 0 < gap ∧
      ∀ profile,
        gap ≤ audit profile + ∑ channel, calibration channel profile := by
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
end Experiments
