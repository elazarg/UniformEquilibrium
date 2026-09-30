import MathUE.RationalCalendarSearch
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-! # Logarithmic bounds for the exact rational power search

The cutoff remains the executable rational search. Real logarithms and ceilings
are used only to bound its returned index. The eventual calendar bound fixes
the survival rate, reward scale and mesh coefficients before the accuracy.
-/

namespace Math

theorem rationalPowerCutoff_zero (tolerance : ℚ) (htolerance : 0 < tolerance) :
    rationalPowerCutoff 0 tolerance (by norm_num) (by norm_num) htolerance = 1 := by
  apply le_antisymm
  · apply rationalPowerCutoff_min
    · exact Nat.zero_lt_one
    · simpa using htolerance.le
  · exact rationalPowerCutoff_pos _ _ _ _ _

/-- The first exact rational cutoff is at most one plus the real logarithmic ratio. -/
theorem rationalPowerCutoff_le_log_bound {ρ tolerance : ℚ}
    (hρ : 0 < ρ) (hρ1 : ρ < 1) (htolerance : 0 < tolerance)
    (htolerance1 : tolerance ≤ 1) :
    (rationalPowerCutoff ρ tolerance hρ.le hρ1 htolerance : ℝ) ≤
      1 + Real.log (1 / (tolerance : ℝ)) / (-Real.log (ρ : ℝ)) := by
  have hρreal : (0 : ℝ) < ρ := by exact_mod_cast hρ
  have hρreal1 : (ρ : ℝ) < 1 := by exact_mod_cast hρ1
  have htoleranceReal : (0 : ℝ) < tolerance := by exact_mod_cast htolerance
  have htoleranceReal1 : (tolerance : ℝ) ≤ 1 := by exact_mod_cast htolerance1
  have hlogρ : Real.log (ρ : ℝ) < 0 := Real.log_neg hρreal hρreal1
  let index := Real.log (tolerance : ℝ) / Real.log (ρ : ℝ)
  have hindex : 0 ≤ index :=
    div_nonneg_of_nonpos (Real.log_nonpos htoleranceReal.le htoleranceReal1) hlogρ.le
  let turns := max 1 (Nat.ceil index)
  have hturns : 0 < turns := lt_of_lt_of_le Nat.zero_lt_one (le_max_left _ _)
  have hlower : index ≤ (turns : ℝ) := by
    apply (Nat.le_ceil index).trans
    exact_mod_cast (show Nat.ceil index ≤ turns from le_max_right _ _)
  have hupper : (turns : ℝ) ≤ 1 + index := by
    dsimp only [turns]
    rw [Nat.cast_max, Nat.cast_one]
    apply max_le
    · linarith
    · linarith [Nat.ceil_lt_add_one hindex]
  have hcutReal : (ρ : ℝ) ^ turns ≤ (tolerance : ℝ) := by
    apply (Real.log_le_log_iff (pow_pos hρreal _) htoleranceReal).mp
    rw [Real.log_pow]
    have hmul := mul_le_mul_of_nonpos_right hlower hlogρ.le
    dsimp only [index] at hmul
    rw [div_mul_cancel₀ _ hlogρ.ne] at hmul
    exact hmul
  have hcut : ρ ^ turns ≤ tolerance := by exact_mod_cast hcutReal
  have hmin := rationalPowerCutoff_min ρ tolerance hρ.le hρ1 htolerance hturns hcut
  have hbound : (rationalPowerCutoff ρ tolerance hρ.le hρ1 htolerance : ℝ) ≤
      1 + index := (by exact_mod_cast hmin :
        (rationalPowerCutoff ρ tolerance hρ.le hρ1 htolerance : ℝ) ≤ (turns : ℝ)).trans
          hupper
  simpa [index, one_div] using hbound

/-- A fixed logarithmic scale, with the degenerate zero-survival case separated. -/
noncomputable def rationalSurvivalLogScale (ρ : ℚ) : ℝ :=
  if ρ = 0 then 0 else 1 / (-Real.log (ρ : ℝ))

theorem rationalSurvivalLogScale_nonneg {ρ : ℚ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) :
    0 ≤ rationalSurvivalLogScale ρ := by
  by_cases hzero : ρ = 0
  · simp [rationalSurvivalLogScale, hzero]
  · have hρ : 0 < ρ := lt_of_le_of_ne hρ0 (Ne.symm hzero)
    have hρreal : (0 : ℝ) < ρ := by exact_mod_cast hρ
    have hρreal1 : (ρ : ℝ) < 1 := by exact_mod_cast hρ1
    simp only [rationalSurvivalLogScale, ite_eq_right hzero]
    exact (div_pos zero_lt_one (neg_pos.mpr (Real.log_neg hρreal hρreal1))).le

/-- The packet's accuracy-dependent tolerance has a logarithmic cutoff bound,
including zero survival. This is a bound on the exact search, not its definition. -/
theorem rationalPowerCutoff_accuracy_le_log {ρ M η : ℚ}
    (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) (hη : 0 < η) (hηM : η ≤ M) :
    (rationalPowerCutoff ρ (η / (6 * M)) hρ0 hρ1
        (div_pos hη (mul_pos (by norm_num) (hη.trans_le hηM))) : ℝ) ≤
      1 + rationalSurvivalLogScale ρ * Real.log (6 * (M : ℝ) / (η : ℝ)) := by
  have hM : 0 < M := hη.trans_le hηM
  have htolerance : 0 < η / (6 * M) := div_pos hη (by positivity)
  by_cases hzero : ρ = 0
  · subst ρ
    simp [rationalPowerCutoff_zero, rationalSurvivalLogScale]
  · have hρ : 0 < ρ := lt_of_le_of_ne hρ0 (Ne.symm hzero)
    have htolerance1 : η / (6 * M) ≤ 1 := by
      apply (div_le_one (by positivity : 0 < 6 * M)).mpr
      linarith
    have hbound := rationalPowerCutoff_le_log_bound hρ hρ1 htolerance htolerance1
    have hreciprocal : 1 / ((η / (6 * M) : ℚ) : ℝ) =
        6 * (M : ℝ) / (η : ℝ) := by
      push_cast
      rw [one_div_div]
    rw [hreciprocal] at hbound
    simpa only [rationalSurvivalLogScale, ite_eq_right hzero, div_eq_mul_inv,
      one_mul, mul_comm] using hbound

/-- A fixed input admits a fixed eventual calendar constant. Its exact search
index times a mesh bound `A + B / η` is of order `η⁻¹ log(η⁻¹)`.
No constant is asserted uniformly as the survival rate approaches one. -/
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
  let scale := rationalSurvivalLogScale ρ
  have hscale : 0 ≤ scale := rationalSurvivalLogScale_nonneg hρ0 hρ1
  let factor := 1 + scale * (1 + |Real.log (6 * (M : ℝ))|)
  have hfactor : 0 < factor := by dsimp only [factor]; positivity
  let constant := factor * (A + B + 1)
  have hconstant : 0 < constant := mul_pos hfactor (by linarith)
  refine ⟨constant, hconstant, Real.exp (-1), Real.exp_pos _, ?_⟩
  intro η hη hηM hsmall
  have hηreal : (0 : ℝ) < η := by exact_mod_cast hη
  have hMreal : (0 : ℝ) < M := by exact_mod_cast hM
  have hηone : (η : ℝ) ≤ 1 :=
    hsmall.trans (Real.exp_le_one_iff.mpr (by norm_num))
  have hlog : 1 ≤ Real.log ((η : ℝ)⁻¹) := by
    have h := Real.log_le_log hηreal hsmall
    rw [Real.log_exp] at h
    rw [Real.log_inv]
    linarith
  have hlogProduct : Real.log (6 * (M : ℝ) / (η : ℝ)) =
      Real.log (6 * (M : ℝ)) + Real.log ((η : ℝ)⁻¹) := by
    simp only [Real.log_div (mul_pos (by norm_num : (0 : ℝ) < 6) hMreal).ne'
      hηreal.ne', Real.log_inv, sub_eq_add_neg]
  have hlogBound : Real.log (6 * (M : ℝ) / (η : ℝ)) ≤
      (1 + |Real.log (6 * (M : ℝ))|) * Real.log ((η : ℝ)⁻¹) := by
    rw [hlogProduct]
    have habs := le_mul_of_one_le_right (abs_nonneg (Real.log (6 * (M : ℝ)))) hlog
    nlinarith [le_abs_self (Real.log (6 * (M : ℝ)))]
  have hcut := rationalPowerCutoff_accuracy_le_log hρ0 hρ1 hη hηM
  have hcutScaled :
      (rationalPowerCutoff ρ (η / (6 * M)) hρ0 hρ1
          (div_pos hη (mul_pos (by norm_num) (hη.trans_le hηM))) : ℝ) ≤
        factor * Real.log ((η : ℝ)⁻¹) := by
    have hscaled := mul_le_mul_of_nonneg_left hlogBound hscale
    dsimp only [factor]
    change _ ≤ 1 + scale * _ at hcut
    nlinarith
  have hmesh : A + B / (η : ℝ) ≤ (A + B + 1) / (η : ℝ) := by
    apply (le_div_iff₀ hηreal).mpr
    rw [add_mul, div_mul_cancel₀ _ hηreal.ne']
    have hAη := mul_le_of_le_one_right hA hηone
    linarith
  calc
    _ ≤ (factor * Real.log ((η : ℝ)⁻¹)) * ((A + B + 1) / (η : ℝ)) :=
      mul_le_mul hcutScaled hmesh (by positivity) (by positivity)
    _ = constant * ((η : ℝ)⁻¹ * Real.log ((η : ℝ)⁻¹)) := by
      dsimp only [constant]
      ring

end Math
