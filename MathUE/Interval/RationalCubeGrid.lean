import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.AbsoluteValue.Basic
import Mathlib.Data.Rat.Floor
import Mathlib.Analysis.Normed.Group.Constructions
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! # Common-denominator rational grids are dense in the closed finite cube

Floor rounding keeps zero and one faces. This is the canonical generic rounding
argument also used by the finite Boolean-game grid frontend.
-/

namespace Math.RationalCubeGrid

variable {n : ℕ}

/-- Round each coordinate down to the denominator `resolution + 1` grid. -/
noncomputable def point (probability : Fin n → ℝ)
    (hone : ∀ who, probability who ≤ 1) (resolution : ℕ) : Fin n → Fin (resolution + 2) :=
  fun who =>
    ⟨Nat.floor (probability who * (resolution + 1 : ℝ)), by
      have hproduct : probability who * (resolution + 1 : ℝ) ≤
          (resolution + 1 : ℕ) := by
        have hmul := mul_le_mul_of_nonneg_right (hone who)
          (show (0 : ℝ) ≤ resolution + 1 by positivity)
        simpa using hmul
      have hfloor : Nat.floor (probability who * (resolution + 1 : ℝ)) ≤ resolution + 1 :=
        Nat.floor_le_of_le hproduct
      exact Nat.lt_succ_of_le hfloor⟩

/-- The generic floor mesh estimate, independent of any game or profile. -/
theorem abs_floor_div_sub_lt_one_div
    (probability : ℝ) (hprobability : 0 ≤ probability)
    (denominator : ℕ) (hdenominator : 0 < denominator) :
    |((Nat.floor (probability * denominator) : ℕ) : ℝ) / denominator -
        probability| < 1 / denominator := by
  have hdenominatorReal : (0 : ℝ) < denominator := by exact_mod_cast hdenominator
  have hlower := Nat.floor_le (mul_nonneg hprobability hdenominatorReal.le)
  have hupper := Nat.lt_floor_add_one (probability * denominator)
  have hquotientLe :
      ((Nat.floor (probability * denominator) : ℕ) : ℝ) / denominator ≤
        probability := by
    rw [div_le_iff₀ hdenominatorReal]
    simpa [mul_comm] using hlower
  rw [abs_of_nonpos (sub_nonpos.mpr hquotientLe)]
  rw [neg_sub, sub_lt_iff_lt_add]
  calc
    probability = probability * denominator / denominator := by field_simp
    _ < (((Nat.floor (probability * denominator) : ℕ) : ℝ) + 1) /
        denominator := (div_lt_div_iff_of_pos_right hdenominatorReal).2 hupper
    _ = ((Nat.floor (probability * denominator) : ℕ) : ℝ) /
          denominator + 1 / denominator := by ring
    _ = 1 / denominator +
          ((Nat.floor (probability * denominator) : ℕ) : ℝ) / denominator := by ring

theorem point_close (probability : Fin n → ℝ)
    (hzero : ∀ who, 0 ≤ probability who) (hone : ∀ who, probability who ≤ 1)
    (resolution : ℕ) (who : Fin n) :
    |((((point probability hone resolution who : ℕ) : ℚ) /
        (resolution + 1) : ℚ) : ℝ) - probability who| < 1 / (resolution + 1 : ℝ) := by
  unfold point
  simp only [Rat.cast_div, Rat.cast_natCast]
  convert abs_floor_div_sub_lt_one_div (probability who) (hzero who)
    (resolution + 1) (Nat.zero_lt_succ resolution) using 1 <;> norm_num

/-- Every positive metric neighborhood of a closed-cube point meets some grid. -/
theorem exists_point_dist_lt (probability : Fin n → ℝ)
    (hzero : ∀ who, 0 ≤ probability who) (hone : ∀ who, probability who ≤ 1)
    (radius : ℝ) (hradius : 0 < radius) :
    ∃ resolution : ℕ, ∃ candidate : Fin n → Fin (resolution + 2),
      dist (fun who => ((((candidate who : ℕ) : ℚ) / (resolution + 1) : ℚ) : ℝ))
        (fun who => probability who) < radius := by
  obtain ⟨resolution, hmesh⟩ := exists_nat_one_div_lt hradius
  refine ⟨resolution, point probability hone resolution, ?_⟩
  apply (dist_pi_lt_iff hradius).mpr
  intro who
  rw [Real.dist_eq]
  exact (point_close probability hzero hone resolution who).trans hmesh

end Math.RationalCubeGrid
