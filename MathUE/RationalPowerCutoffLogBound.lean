import MathUE.RationalCalendarSearch
import MathUE.PowerCutoffLogBound

/-! # Logarithmic bounds for the exact rational power search

The executable rational search is unchanged. Its minimality compares it with
the real scalar cutoff; logarithmic calendar estimates delegate to the real
fixed-input theorem.
-/

namespace Math

theorem rationalPowerCutoff_zero (tolerance : ℚ) (htolerance : 0 < tolerance) :
    rationalPowerCutoff 0 tolerance (by norm_num) (by norm_num) htolerance = 1 := by
  apply le_antisymm
  · apply rationalPowerCutoff_min
    · exact Nat.zero_lt_one
    · simpa using htolerance.le
  · exact rationalPowerCutoff_pos _ _ _ _ _

/-- Exact rational minimality bounds the search by the real comparison cutoff. -/
theorem rationalPowerCutoff_le_powerLogCutoff {ρ tolerance : ℚ}
    (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) (htolerance : 0 < tolerance)
    (htolerance1 : tolerance ≤ 1) :
    rationalPowerCutoff ρ tolerance hρ0 hρ1 htolerance ≤
      powerLogCutoff (ρ : ℝ) (tolerance : ℝ) := by
  have hspec := powerLogCutoff_spec_and_bound
    (show (0 : ℝ) ≤ ρ by exact_mod_cast hρ0)
    (show (ρ : ℝ) < 1 by exact_mod_cast hρ1)
    (show (0 : ℝ) < tolerance by exact_mod_cast htolerance)
    (show (tolerance : ℝ) ≤ 1 by exact_mod_cast htolerance1)
  apply rationalPowerCutoff_min ρ tolerance hρ0 hρ1 htolerance hspec.1
  exact_mod_cast hspec.2.1

/-- The first exact rational cutoff is at most one plus the real logarithmic ratio. -/
theorem rationalPowerCutoff_le_log_bound {ρ tolerance : ℚ}
    (hρ : 0 < ρ) (hρ1 : ρ < 1) (htolerance : 0 < tolerance)
    (htolerance1 : tolerance ≤ 1) :
    (rationalPowerCutoff ρ tolerance hρ.le hρ1 htolerance : ℝ) ≤
      1 + Real.log (1 / (tolerance : ℝ)) / (-Real.log (ρ : ℝ)) := by
  have hρreal : (0 : ℝ) < ρ := by exact_mod_cast hρ
  have hcomparison :
      (rationalPowerCutoff ρ tolerance hρ.le hρ1 htolerance : ℝ) ≤
        (powerLogCutoff (ρ : ℝ) (tolerance : ℝ) : ℝ) := by
    exact_mod_cast rationalPowerCutoff_le_powerLogCutoff hρ.le hρ1 htolerance htolerance1
  have hspec := powerLogCutoff_spec_and_bound hρreal.le
    (show (ρ : ℝ) < 1 by exact_mod_cast hρ1)
    (show (0 : ℝ) < tolerance by exact_mod_cast htolerance)
    (show (tolerance : ℝ) ≤ 1 by exact_mod_cast htolerance1)
  have hbound := hcomparison.trans hspec.2.2
  simpa [survivalLogScale, hρreal.ne', div_eq_mul_inv, mul_comm] using hbound

/-- The real fixed logarithmic scale viewed on a rational survival rate. -/
noncomputable def rationalSurvivalLogScale (ρ : ℚ) : ℝ :=
  survivalLogScale (ρ : ℝ)

theorem rationalSurvivalLogScale_nonneg {ρ : ℚ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) :
    0 ≤ rationalSurvivalLogScale ρ :=
  survivalLogScale_nonneg
    (show (0 : ℝ) ≤ ρ by exact_mod_cast hρ0)
    (show (ρ : ℝ) < 1 by exact_mod_cast hρ1)

/-- The packet's tolerance bounds the exact rational search, including zero survival. -/
theorem rationalPowerCutoff_accuracy_le_log {ρ M η : ℚ}
    (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) (hη : 0 < η) (hηM : η ≤ M) :
    (rationalPowerCutoff ρ (η / (6 * M)) hρ0 hρ1
        (div_pos hη (mul_pos (by norm_num) (hη.trans_le hηM))) : ℝ) ≤
      1 + rationalSurvivalLogScale ρ * Real.log (6 * (M : ℝ) / (η : ℝ)) := by
  have hM : 0 < M := hη.trans_le hηM
  have htolerance : 0 < η / (6 * M) := div_pos hη (by positivity)
  have htolerance1 : η / (6 * M) ≤ 1 := by
    apply (div_le_one (by positivity : 0 < 6 * M)).mpr
    linarith
  have hcomparison :
      (rationalPowerCutoff ρ (η / (6 * M)) hρ0 hρ1 htolerance : ℝ) ≤
        (powerLogCutoff (ρ : ℝ) ((η / (6 * M) : ℚ) : ℝ) : ℝ) := by
    exact_mod_cast rationalPowerCutoff_le_powerLogCutoff hρ0 hρ1 htolerance htolerance1
  have htoleranceCast : ((η / (6 * M) : ℚ) : ℝ) =
      (η : ℝ) / (6 * (M : ℝ)) := by push_cast; rfl
  rw [htoleranceCast] at hcomparison
  have hbound := powerLogCutoff_accuracy_le_log
    (show (0 : ℝ) ≤ ρ by exact_mod_cast hρ0)
    (show (ρ : ℝ) < 1 by exact_mod_cast hρ1)
    (show (0 : ℝ) < η by exact_mod_cast hη)
    (show (η : ℝ) ≤ M by exact_mod_cast hηM)
  exact hcomparison.trans hbound

/-- Fixed-input calendar bounds for the exact rational search follow from the
real comparison theorem and rational minimality, without another log proof. -/
theorem exists_rationalPowerCutoff_calendar_log_bound
    {ρ M : ℚ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) (hM : 0 < M)
    {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) :
    ∃ constant : ℝ, 0 < constant ∧
      ∃ threshold : ℝ, 0 < threshold ∧
        ∀ (η : ℚ) (hη : 0 < η) (hηM : η ≤ M), (η : ℝ) ≤ threshold →
          (rationalPowerCutoff ρ (η / (6 * M)) hρ0 hρ1
              (div_pos hη (mul_pos (by norm_num) (hη.trans_le hηM))) : ℝ) *
              (A + B / (η : ℝ)) ≤
            constant * ((η : ℝ)⁻¹ * Real.log ((η : ℝ)⁻¹)) := by
  obtain ⟨constant, hconstant, threshold, hthreshold, hbound⟩ :=
    exists_powerCutoff_calendar_log_bound
      (show (0 : ℝ) ≤ ρ by exact_mod_cast hρ0)
      (show (ρ : ℝ) < 1 by exact_mod_cast hρ1)
      (show (0 : ℝ) < M by exact_mod_cast hM) hA hB
  refine ⟨constant, hconstant, threshold, hthreshold, ?_⟩
  intro η hη hηM hsmall
  have htolerance : 0 < η / (6 * M) := div_pos hη (by positivity)
  have htolerance1 : η / (6 * M) ≤ 1 := by
    apply (div_le_one (by positivity : 0 < 6 * M)).mpr
    linarith
  have hcomparison :
      (rationalPowerCutoff ρ (η / (6 * M)) hρ0 hρ1 htolerance : ℝ) ≤
        (powerLogCutoff (ρ : ℝ) ((η / (6 * M) : ℚ) : ℝ) : ℝ) := by
    exact_mod_cast rationalPowerCutoff_le_powerLogCutoff hρ0 hρ1 htolerance htolerance1
  have htoleranceCast : ((η / (6 * M) : ℚ) : ℝ) =
      (η : ℝ) / (6 * (M : ℝ)) := by push_cast; rfl
  rw [htoleranceCast] at hcomparison
  have hηreal : (0 : ℝ) < η := by exact_mod_cast hη
  exact (mul_le_mul_of_nonneg_right hcomparison (by positivity)).trans
    (hbound (η : ℝ) hηreal (by exact_mod_cast hηM) hsmall)

end Math
