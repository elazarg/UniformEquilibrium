import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! # Capped-minimum and geometric recurrence bounds -/

namespace Math

/-- A quantity bounded by its initial value controls its own capped minimum
from below. -/
theorem scaled_le_min_of_le_initial
    {current initial threshold : ℝ}
    (hcurrent : 0 ≤ current) (hbound : current ≤ initial)
    (hthreshold : 0 ≤ threshold) (hinitial : threshold ≤ initial) :
    threshold * current / initial ≤ min current threshold := by
  have hinitialNonneg : 0 ≤ initial := hthreshold.trans hinitial
  by_cases hinitialZero : initial = 0
  · subst initial
    have hcurrentZero : current = 0 := le_antisymm hbound hcurrent
    have hthresholdZero : threshold = 0 := le_antisymm hinitial hthreshold
    simp [hcurrentZero, hthresholdZero]
  · have hinitialPos : 0 < initial := lt_of_le_of_ne hinitialNonneg
      (Ne.symm hinitialZero)
    apply le_min
    · apply (div_le_iff₀ hinitialPos).2
      nlinarith
    · apply (div_le_iff₀ hinitialPos).2
      nlinarith

/-- Iterating a nonnegative multiplicative contraction gives its literal
geometric envelope. -/
theorem sequence_le_geometric_of_step
    (value : ℕ → ℝ) (initial ratio : ℝ)
    (hratio : 0 ≤ ratio) (hzero : value 0 ≤ initial)
    (hstep : ∀ time, value (time + 1) ≤ ratio * value time) :
    ∀ time, value time ≤ ratio ^ time * initial := by
  intro time
  induction time with
  | zero => simpa using hzero
  | succ time ih =>
      rw [pow_succ]
      calc
        value (time + 1) ≤ ratio * value time := hstep time
        _ ≤ ratio * (ratio ^ time * initial) :=
          mul_le_mul_of_nonneg_left ih hratio
        _ = ratio ^ time * ratio * initial := by ring

/-- A nonnegative sequence under a genuine geometric envelope converges to
zero. -/
theorem tendsto_zero_of_sequence_le_geometric
    (value : ℕ → ℝ) (initial ratio : ℝ)
    (hvalue : ∀ time, 0 ≤ value time)
    (hratio : 0 ≤ ratio) (hratioOne : ratio < 1)
    (henvelope : ∀ time, value time ≤ ratio ^ time * initial) :
    Filter.Tendsto value Filter.atTop (nhds 0) := by
  have hlimit : Filter.Tendsto (fun time : ℕ => ratio ^ time * initial)
      Filter.atTop (nhds 0) := by
    simpa using
      (tendsto_pow_atTop_nhds_zero_of_lt_one hratio hratioOne).mul_const initial
  exact squeeze_zero' (Filter.Eventually.of_forall hvalue)
    (Filter.Eventually.of_forall henvelope) hlimit

end Math
