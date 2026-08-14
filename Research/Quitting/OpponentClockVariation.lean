import UniformEquilibrium.Quitting.Debt.Marked.TimeAdvance

/-!
# Opponent-clock variation kernels

The canonical marked successor-escape estimate already supplies the
unconditional one-step bound.  This Research residual keeps the genuinely
distinct scalar telescope consumed by an infinite version: bounded values and
a summable upper clock make the whole value path have finite total variation.
-/


noncomputable section

namespace GameTheory

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-! ## The Research-specific finite telescope -/

theorem sum_abs_forwardDifference_le_clock
    (value charge : ℕ → ℝ) (M C : ℝ)
    (hvalue : ∀ time, |value time| ≤ M)
    (hC : 0 ≤ C)
    (hcharge : ∀ time, 0 ≤ charge time)
    (hstep : ∀ time,
      value (time + 1) - value time ≤ C * charge time)
    (fuel : ℕ) :
    (∑ time ∈ Finset.range fuel,
        |value (time + 1) - value time|) ≤
      2 * M + 2 * C *
        ∑ time ∈ Finset.range fuel, charge time := by
  have hpointwise : ∀ time,
      |value (time + 1) - value time| ≤
        2 * C * charge time + (value time - value (time + 1)) := by
    intro time
    have hclock0 : 0 ≤ C * charge time :=
      mul_nonneg hC (hcharge time)
    by_cases hdiff : 0 ≤ value (time + 1) - value time
    · rw [abs_of_nonneg hdiff]
      nlinarith [hstep time]
    · rw [abs_of_nonpos (le_of_not_ge hdiff)]
      nlinarith
  calc
    (∑ time ∈ Finset.range fuel,
        |value (time + 1) - value time|) ≤
        ∑ time ∈ Finset.range fuel,
          (2 * C * charge time +
            (value time - value (time + 1))) := by
      exact Finset.sum_le_sum fun time _ => hpointwise time
    _ = 2 * C * (∑ time ∈ Finset.range fuel, charge time) +
        (value 0 - value fuel) := by
      rw [Finset.sum_add_distrib, Finset.sum_range_sub']
      congr 1
      rw [Finset.mul_sum]
    _ ≤ 2 * C * (∑ time ∈ Finset.range fuel, charge time) +
        2 * M := by
      have hzero := hvalue 0
      have hfuel := hvalue fuel
      rw [abs_le] at hzero hfuel
      linarith
    _ = 2 * M + 2 * C *
        ∑ time ∈ Finset.range fuel, charge time := by ring

end GameTheory
