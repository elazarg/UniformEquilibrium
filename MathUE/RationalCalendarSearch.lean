import MathUE.RationalArcSubdivision
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Data.Nat.Find
import Mathlib.Data.Rat.Floor

/-! # Executable rational mesh lengths and geometric cutoffs

The mesh uses an exact rational ceiling. The cutoff searches the decidable
rational successive-power test, starting at one. Its termination proof uses
the Archimedean power lemma; no real logarithm or approximate comparison is used.
-/

namespace Math

/-- Exact rational implementation of the scalar subdivision length. -/
def rationalArcLengthRat (q δ : ℚ) : ℕ := max 1 (Nat.ceil (q / (1 - q) / δ))

theorem rationalArcLengthRat_eq_real (q δ : ℚ) :
    rationalArcLengthRat q δ = rationalArcLength (q : ℝ) (δ : ℝ) := by
  unfold rationalArcLengthRat rationalArcLength rationalArcOdds
  have hcast : ((q / (1 - q) / δ : ℚ) : ℝ) = (q : ℝ) / (1 - q) / δ := by
    push_cast
    rfl
  rw [← hcast, ← Int.ceil_toNat, ← Int.ceil_toNat, Rat.ceil_cast]

theorem rationalArcLengthRat_pos (q δ : ℚ) : 0 < rationalArcLengthRat q δ :=
  lt_of_lt_of_le Nat.zero_lt_one (le_max_left _ _)

theorem exists_positive_rational_power_cutoff {ρ tolerance : ℚ}
    (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) (htolerance : 0 < tolerance) :
    ∃ turns : ℕ, 0 < turns ∧ ρ ^ turns ≤ tolerance := by
  obtain ⟨turns, hturns⟩ := exists_pow_lt_of_lt_one htolerance hρ1
  refine ⟨turns + 1, Nat.succ_pos _, ?_⟩
  rw [pow_succ]
  exact (mul_le_of_le_one_right (pow_nonneg hρ0 _) hρ1.le).trans hturns.le

/-- First positive cutoff passing the exact rational power comparison. This
definition is executable: its only branching predicate is rational arithmetic. -/
def rationalPowerCutoff (ρ tolerance : ℚ) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1)
    (htolerance : 0 < tolerance) : ℕ :=
  Nat.find (exists_positive_rational_power_cutoff hρ0 hρ1 htolerance)

theorem rationalPowerCutoff_pos (ρ tolerance : ℚ) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1)
    (htolerance : 0 < tolerance) :
    0 < rationalPowerCutoff ρ tolerance hρ0 hρ1 htolerance :=
  (Nat.find_spec (exists_positive_rational_power_cutoff hρ0 hρ1 htolerance)).1

theorem rationalPowerCutoff_spec (ρ tolerance : ℚ) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1)
    (htolerance : 0 < tolerance) :
    ρ ^ rationalPowerCutoff ρ tolerance hρ0 hρ1 htolerance ≤ tolerance :=
  (Nat.find_spec (exists_positive_rational_power_cutoff hρ0 hρ1 htolerance)).2

theorem rationalPowerCutoff_min (ρ tolerance : ℚ) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1)
    (htolerance : 0 < tolerance) {turns : ℕ} (hturns : 0 < turns)
    (hcut : ρ ^ turns ≤ tolerance) :
    rationalPowerCutoff ρ tolerance hρ0 hρ1 htolerance ≤ turns :=
  Nat.find_min' (exists_positive_rational_power_cutoff hρ0 hρ1 htolerance) ⟨hturns, hcut⟩

theorem rationalPowerCutoff_spec_real (ρ tolerance : ℚ) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1)
    (htolerance : 0 < tolerance) :
    (ρ : ℝ) ^ rationalPowerCutoff ρ tolerance hρ0 hρ1 htolerance ≤ (tolerance : ℝ) := by
  exact_mod_cast rationalPowerCutoff_spec ρ tolerance hρ0 hρ1 htolerance

end Math
