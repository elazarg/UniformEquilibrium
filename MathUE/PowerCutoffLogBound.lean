import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! # Real logarithmic power cutoffs and fixed-input calendar bounds

Real logarithms select a positive comparison cutoff. Exact rational searches
may be bounded by this cutoff using their own minimality theorem; no executable
rational search is replaced. The constants below are fixed before accuracy,
and are not asserted uniformly when the survival rate approaches one.
-/

noncomputable section

namespace Math

/-- A real comparison cutoff, with zero survival handled separately. -/
def powerLogCutoff (ρ tolerance : ℝ) : ℕ := by
  classical
  exact if ρ = 0 then 1 else max 1 (Nat.ceil (Real.log tolerance / Real.log ρ))

/-- The logarithmic scale of a fixed survival rate, including zero survival. -/
def survivalLogScale (ρ : ℝ) : ℝ := by
  classical
  exact if ρ = 0 then 0 else 1 / (-Real.log ρ)

theorem powerLogCutoff_zero (tolerance : ℝ) : powerLogCutoff 0 tolerance = 1 := by
  simp [powerLogCutoff]

theorem survivalLogScale_nonneg {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) :
    0 ≤ survivalLogScale ρ := by
  by_cases hzero : ρ = 0
  · simp [survivalLogScale, hzero]
  · have hρ : 0 < ρ := lt_of_le_of_ne hρ0 (Ne.symm hzero)
    simp only [survivalLogScale, ite_eq_right hzero]
    exact (div_pos zero_lt_one (neg_pos.mpr (Real.log_neg hρ hρ1))).le

/-- The same real comparison index is positive, passes the power test, and
has the logarithmic size bound. -/
theorem powerLogCutoff_spec_and_bound {ρ tolerance : ℝ}
    (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) (htolerance : 0 < tolerance)
    (htolerance1 : tolerance ≤ 1) :
    0 < powerLogCutoff ρ tolerance ∧
      ρ ^ powerLogCutoff ρ tolerance ≤ tolerance ∧
      (powerLogCutoff ρ tolerance : ℝ) ≤
        1 + survivalLogScale ρ * Real.log (1 / tolerance) := by
  by_cases hzero : ρ = 0
  · subst ρ
    simp [powerLogCutoff, survivalLogScale, htolerance.le]
  · have hρ : 0 < ρ := lt_of_le_of_ne hρ0 (Ne.symm hzero)
    have hlogρ : Real.log ρ < 0 := Real.log_neg hρ hρ1
    let index := Real.log tolerance / Real.log ρ
    have hindex : 0 ≤ index :=
      div_nonneg_of_nonpos (Real.log_nonpos htolerance.le htolerance1) hlogρ.le
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
    have hcut : ρ ^ turns ≤ tolerance := by
      apply (Real.log_le_log_iff (pow_pos hρ _) htolerance).mp
      rw [Real.log_pow]
      have hmul := mul_le_mul_of_nonpos_right hlower hlogρ.le
      dsimp only [index] at hmul
      rw [div_mul_cancel₀ _ hlogρ.ne] at hmul
      exact hmul
    refine ⟨?_, ?_, ?_⟩
    · simpa only [powerLogCutoff, ite_eq_right hzero] using hturns
    · simpa only [powerLogCutoff, ite_eq_right hzero] using hcut
    · simpa [powerLogCutoff, survivalLogScale, hzero, turns, index, one_div,
        div_eq_mul_inv, mul_comm] using hupper

/-- The packet's accuracy-dependent tolerance has the real logarithmic bound. -/
theorem powerLogCutoff_accuracy_le_log {ρ M η : ℝ}
    (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) (hη : 0 < η) (hηM : η ≤ M) :
    (powerLogCutoff ρ (η / (6 * M)) : ℝ) ≤
      1 + survivalLogScale ρ * Real.log (6 * M / η) := by
  have hM : 0 < M := hη.trans_le hηM
  have htolerance : 0 < η / (6 * M) := div_pos hη (by positivity)
  have htolerance1 : η / (6 * M) ≤ 1 := by
    apply (div_le_one (by positivity : 0 < 6 * M)).mpr
    linarith
  have hbound := (powerLogCutoff_spec_and_bound hρ0 hρ1 htolerance htolerance1).2.2
  rwa [one_div_div] at hbound

/-- A fixed real survival rate and mesh coefficients have fixed eventual
calendar constants. No uniformity across boundary input tables is asserted. -/
theorem exists_powerCutoff_calendar_log_bound
    {ρ M : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) (hM : 0 < M)
    {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) :
    ∃ constant : ℝ, 0 < constant ∧
      ∃ threshold : ℝ, 0 < threshold ∧
        ∀ η : ℝ, 0 < η → η ≤ M → η ≤ threshold →
          (powerLogCutoff ρ (η / (6 * M)) : ℝ) * (A + B / η) ≤
            constant * (η⁻¹ * Real.log (η⁻¹)) := by
  let scale := survivalLogScale ρ
  have hscale : 0 ≤ scale := survivalLogScale_nonneg hρ0 hρ1
  let factor := 1 + scale * (1 + |Real.log (6 * M)|)
  have hfactor : 0 < factor := by dsimp only [factor]; positivity
  let constant := factor * (A + B + 1)
  have hconstant : 0 < constant := mul_pos hfactor (by linarith)
  refine ⟨constant, hconstant, Real.exp (-1), Real.exp_pos _, ?_⟩
  intro η hη hηM hsmall
  have hηone : η ≤ 1 := hsmall.trans (Real.exp_le_one_iff.mpr (by norm_num))
  have hlog : 1 ≤ Real.log (η⁻¹) := by
    have h := Real.log_le_log hη hsmall
    rw [Real.log_exp] at h
    rw [Real.log_inv]
    linarith
  have hlogProduct : Real.log (6 * M / η) = Real.log (6 * M) + Real.log (η⁻¹) := by
    simp only [Real.log_div (mul_pos (by norm_num : (0 : ℝ) < 6) hM).ne'
      hη.ne', Real.log_inv, sub_eq_add_neg]
  have hlogBound : Real.log (6 * M / η) ≤
      (1 + |Real.log (6 * M)|) * Real.log (η⁻¹) := by
    rw [hlogProduct]
    have habs := le_mul_of_one_le_right (abs_nonneg (Real.log (6 * M))) hlog
    nlinarith [le_abs_self (Real.log (6 * M))]
  have hcut := powerLogCutoff_accuracy_le_log hρ0 hρ1 hη hηM
  have hcutScaled : (powerLogCutoff ρ (η / (6 * M)) : ℝ) ≤
      factor * Real.log (η⁻¹) := by
    have hscaled := mul_le_mul_of_nonneg_left hlogBound hscale
    dsimp only [factor]
    change _ ≤ 1 + scale * _ at hcut
    nlinarith
  have hmesh : A + B / η ≤ (A + B + 1) / η := by
    apply (le_div_iff₀ hη).mpr
    rw [add_mul, div_mul_cancel₀ _ hη.ne']
    have hAη := mul_le_of_le_one_right hA hηone
    linarith
  calc
    _ ≤ (factor * Real.log (η⁻¹)) * ((A + B + 1) / η) :=
      mul_le_mul hcutScaled hmesh (by positivity) (by positivity)
    _ = constant * (η⁻¹ * Real.log (η⁻¹)) := by
      dsimp only [constant]
      ring

end Math
