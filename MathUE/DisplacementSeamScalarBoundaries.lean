import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecificLimits.Basic

/-! # Scalar boundaries for displacement variation and root seams

These are scalar sequence results, not counterexamples consisting of games,
behavioral profiles, or positive terminal exploitability gaps.
-/

noncomputable section

namespace Math

open Filter
open scoped Topology

/-- A nonzero displacement limit survives multiplication by coefficients
tending to one and addition of a summable remainder. The resulting signed
seam neither tends to zero nor forms a summable sequence. -/
theorem nonzero_displacement_limit_seam_not_tendsto_zero_not_summable
    (survival displacement remainder : ℕ → ℝ) {limit : ℝ}
    (hlimit : limit ≠ 0)
    (hsurvival : Tendsto survival atTop (nhds 1))
    (hdisplacement : Tendsto displacement atTop (nhds limit))
    (hremainder : Summable remainder) :
    Tendsto (fun n => -survival n * displacement n + remainder n)
        atTop (nhds (-limit)) ∧
      ¬ Tendsto (fun n => -survival n * displacement n + remainder n)
        atTop (nhds 0) ∧
      ¬ Summable (fun n => -survival n * displacement n + remainder n) := by
  have hseam : Tendsto (fun n => -survival n * displacement n + remainder n)
      atTop (nhds (-limit)) := by
    simpa using (hsurvival.neg.mul hdisplacement).add hremainder.tendsto_atTop_zero
  have hnot : ¬ Tendsto (fun n => -survival n * displacement n + remainder n)
      atTop (nhds 0) := by
    intro hzero
    have heq := tendsto_nhds_unique hseam hzero
    exact hlimit (neg_eq_zero.mp heq)
  exact ⟨hseam, hnot, fun hsummable => hnot hsummable.tendsto_atTop_zero⟩

/-- Harmonic displacement has absolutely summable adjacent increments. -/
theorem summable_abs_harmonic_displacement_increment :
    Summable (fun n : ℕ => |1 / ((n : ℝ) + 2) - 1 / ((n : ℝ) + 1)|) := by
  have hbase : Summable (fun n : ℕ => 1 / (n : ℝ) ^ 2) :=
    Real.summable_one_div_nat_pow.mpr (by norm_num)
  have hmajorant : Summable (fun n : ℕ => 1 / ((n : ℝ) + 1) ^ 2) := by
    simpa only [Function.comp_def, Nat.cast_succ] using
      hbase.comp_injective Nat.succ_injective
  apply Summable.of_nonneg_of_le (fun _ => abs_nonneg _) (fun n => ?_) hmajorant
  have hfirst : 0 < (n : ℝ) + 1 := by positivity
  have hsecond : 0 < (n : ℝ) + 2 := by positivity
  have hdecrease : 1 / ((n : ℝ) + 2) ≤ 1 / ((n : ℝ) + 1) :=
    one_div_le_one_div_of_le hfirst (by linarith)
  have heq : |1 / ((n : ℝ) + 2) - 1 / ((n : ℝ) + 1)| =
      1 / (((n : ℝ) + 1) * ((n : ℝ) + 2)) := by
    rw [abs_of_nonpos (sub_nonpos.mpr hdecrease)]
    field_simp
    ring
  rw [heq]
  apply one_div_le_one_div_of_le (sq_pos_of_pos hfirst)
  nlinarith

/-- The explicit harmonic sequence tends to zero and has finite total
variation, while its values are not summable. Thus neither finite variation
nor a zero displacement limit supplies summable chronology errors. -/
theorem harmonic_displacement_finite_variation_zero_limit_not_summable :
    Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (nhds 0) ∧
      Summable (fun n : ℕ =>
        |1 / (((n + 1 : ℕ) : ℝ) + 1) - 1 / ((n : ℝ) + 1)|) ∧
      ¬ Summable (fun n : ℕ => 1 / ((n : ℝ) + 1)) := by
  refine ⟨tendsto_one_div_add_atTop_nhds_zero_nat, ?_, ?_⟩
  · simpa only [Nat.cast_succ, add_assoc, one_add_one_eq_two] using
      summable_abs_harmonic_displacement_increment
  · exact_mod_cast mt (summable_nat_add_iff 1).1 Real.not_summable_one_div_natCast

end Math
