import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-! # Reciprocal bounds for quadratic debt decrease -/

namespace Math

/-- One quadratic-decrease step increases the reciprocal by the uniform
amount obtained from an initial upper bound. -/
theorem one_div_sub_one_div_ge_of_variable_quadratic_step
    {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    {base slope initial current next : K}
    (hbase : 0 ≤ base) (hslope : 1 ≤ slope)
    (hinitial : current ≤ initial) (hcurrent : 0 < current)
    (hnext : 0 < next)
    (hstep : next ≤ current - current ^ 2 / (base + slope * current)) :
    1 / (base + (slope - 1) * initial) ≤ 1 / next - 1 / current := by
  let denominator := base + slope * current
  let C := base + (slope - 1) * initial
  have hdenominator : 0 < denominator := by
    dsimp only [denominator]
    nlinarith [mul_pos (by linarith : 0 < slope) hcurrent]
  have hC : 0 < C := by
    by_cases hslopeEq : slope = 1
    · subst slope
      have hbasePos : 0 < base := by
        by_contra hbaseNot
        have hbaseZero : base = 0 := le_antisymm (le_of_not_gt hbaseNot) hbase
        subst base
        have hquotient : current ^ 2 / current = current := by
          field_simp [hcurrent.ne']
        simp only [zero_add, one_mul, hquotient, sub_self] at hstep
        linarith
      simpa [C] using hbasePos
    · have hcoefficient : 0 < slope - 1 := lt_of_le_of_ne
        (sub_nonneg.mpr hslope) (Ne.symm (sub_ne_zero.mpr hslopeEq))
      dsimp only [C]
      nlinarith [mul_pos hcoefficient hcurrent]
  have hdrop : current ^ 2 ≤ (current - next) * denominator := by
    apply (div_le_iff₀ hdenominator).mp
    nlinarith
  have hnextDenominator : next * denominator ≤
      current * (base + (slope - 1) * current) := by
    have hscaled := (le_sub_iff_add_le).mp hstep
    have hmul := (div_le_iff₀ hdenominator).mp
      (show current ^ 2 / denominator ≤ current - next by linarith)
    dsimp only [denominator]
    nlinarith
  have hcoefficient : base + (slope - 1) * current ≤ C := by
    dsimp only [C]
    nlinarith [mul_nonneg (sub_nonneg.mpr hslope) (sub_nonneg.mpr hinitial)]
  have htarget : current * next ≤ C * (current - next) := by
    have hleft := mul_le_mul_of_nonneg_left hnextDenominator hcurrent.le
    have hright := mul_le_mul_of_nonneg_left hdrop hC.le
    have hmiddle := mul_le_mul_of_nonneg_right hcoefficient
      (sq_nonneg current)
    have hdenominatorNonneg := hdenominator.le
    nlinarith [mul_nonneg (mul_nonneg hcurrent.le hnext.le) hdenominatorNonneg]
  rw [show 1 / next - 1 / current =
      (current - next) / (next * current) by field_simp]
  apply (div_le_div_iff₀ hC (mul_pos hnext hcurrent)).2
  nlinarith

/-- Iterating the variable-denominator quadratic decrease gives the sharp
reciprocal envelope. Zero values are handled without taking reciprocals. -/
theorem sequence_le_reciprocal_of_variable_quadratic_step
    {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (value : ℕ → K) (base slope initial : K)
    (hbase : 0 ≤ base) (hslope : 1 ≤ slope) (hinitial : 0 < initial)
    (hC : 0 < base + (slope - 1) * initial)
    (hzero : value 0 ≤ initial)
    (hnonneg : ∀ time, 0 ≤ value time)
    (hantitone : Antitone value)
    (hstep : ∀ time, 0 < value time → value (time + 1) ≤
      value time - value time ^ 2 / (base + slope * value time)) :
    ∀ time, value time ≤
      (base + (slope - 1) * initial) * initial /
        (base + (slope - 1) * initial + time * initial) := by
  let C := base + (slope - 1) * initial
  intro time
  induction time with
  | zero => simpa [C, hC.ne'] using hzero
  | succ time ih =>
      let current := value time
      let next := value (time + 1)
      let currentTarget := C * initial / (C + time * initial)
      let nextTarget := C * initial / (C + (time + 1) * initial)
      have hcurrentTarget : 0 < currentTarget := by
        dsimp only [currentTarget]
        positivity
      have hnextTarget : 0 < nextTarget := by
        dsimp only [nextTarget]
        positivity
      by_cases hnextZero : next = 0
      · dsimp only [next, nextTarget, C] at hnextZero hnextTarget ⊢
        rw [hnextZero]
        simpa [Nat.cast_add, Nat.cast_one] using hnextTarget.le
      · have hnextPos : 0 < next := lt_of_le_of_ne
          (hnonneg (time + 1)) (Ne.symm hnextZero)
        have hnextLeCurrent : next ≤ current :=
          hantitone (Nat.le_add_right time 1)
        have hcurrentPos : 0 < current := hnextPos.trans_le hnextLeCurrent
        have hcurrentLeTarget : current ≤ currentTarget := ih
        have hinvCurrent : 1 / currentTarget ≤ 1 / current :=
          one_div_le_one_div_of_le hcurrentPos hcurrentLeTarget
        have hincrement : 1 / C ≤ 1 / next - 1 / current :=
          one_div_sub_one_div_ge_of_variable_quadratic_step hbase hslope
            ((hantitone (Nat.zero_le time)).trans hzero) hcurrentPos hnextPos
              (hstep time hcurrentPos)
        have hcurrentIdentity : 1 / currentTarget =
            1 / initial + time / C := by
          dsimp only [currentTarget]
          field_simp [show C ≠ 0 from hC.ne', hinitial.ne']
        have hnextIdentity : 1 / nextTarget =
            1 / initial + (time + 1) / C := by
          dsimp only [nextTarget]
          field_simp [show C ≠ 0 from hC.ne', hinitial.ne']
        have hinvNext : 1 / nextTarget ≤ 1 / next := by
          rw [hnextIdentity]
          calc
            1 / initial + (time + 1) / C =
                1 / C + 1 / currentTarget := by
              rw [hcurrentIdentity]
              ring
            _ ≤ 1 / C + 1 / current := by
              simpa [add_comm] using add_le_add_right hinvCurrent (1 / C)
            _ ≤ 1 / next := by linarith
        by_contra hbound
        have hstrict : nextTarget < next := by
          dsimp only [next, nextTarget, C]
          simpa [Nat.cast_add, Nat.cast_one] using lt_of_not_ge hbound
        have hinverse := one_div_lt_one_div_of_lt hnextTarget hstrict
        exact (not_lt_of_ge hinvNext) hinverse

/-- A positive sequence over an ordered field with a natural ceiling crosses
a positive threshold under fixed quadratic descent. -/
theorem exists_index_le_ceil_of_quadratic_descent
    {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] [FloorRing K]
    (value : ℕ → K) {scale threshold : K}
    (hscale : 0 < scale) (hthreshold : 0 < threshold)
    (hstep : ∀ n, 0 < value n →
      value (n + 1) ≤ value n - value n ^ 2 / scale) :
    ∃ n ≤ Nat.ceil (scale / threshold), value n ≤ threshold := by
  let horizon := Nat.ceil (scale / threshold)
  by_contra hnone
  push Not at hnone
  have habove : ∀ n, n ≤ horizon → threshold < value n := by
    intro n hn
    exact hnone n hn
  have hinverseStep : ∀ n, n < horizon →
      1 / value n + 1 / scale ≤ 1 / value (n + 1) := by
    intro n hn
    have hx : 0 < value n := hthreshold.trans (habove n hn.le)
    have hy : 0 < value (n + 1) := hthreshold.trans (habove (n + 1) hn)
    have hdropNonnegative : 0 ≤ value n ^ 2 / scale := by positivity
    have hyx : value (n + 1) ≤ value n :=
      (hstep n hx).trans (sub_le_self _ hdropNonnegative)
    have hscaledStep :
        scale * value (n + 1) ≤ scale * value n - value n ^ 2 := by
      have := mul_le_mul_of_nonneg_left (hstep n hx) hscale.le
      field_simp at this
      nlinarith
    have hproduct : value n * value (n + 1) ≤ value n ^ 2 := by
      nlinarith [mul_le_mul_of_nonneg_left hyx hx.le]
    have hcombined :
        (scale + value n) * value (n + 1) ≤ scale * value n := by
      nlinarith
    rw [show 1 / value n + 1 / scale =
        (scale + value n) / (scale * value n) by
      field_simp]
    apply (div_le_iff₀ (mul_pos hscale hx)).2
    calc
      scale + value n ≤ scale * value n / value (n + 1) :=
        (le_div_iff₀ hy).2 hcombined
      _ = 1 / value (n + 1) * (scale * value n) := by ring
  have hinverse : ∀ n, n ≤ horizon →
      (n : K) / scale ≤ 1 / value n := by
    intro n hn
    induction n with
    | zero =>
        simp only [Nat.cast_zero, zero_div]
        exact div_nonneg zero_le_one
          (hthreshold.trans (habove 0 (Nat.zero_le horizon))).le
    | succ n ih =>
        have hnlt : n < horizon := by omega
        have hprior := ih hnlt.le
        have hnext := hinverseStep n hnlt
        push_cast
        calc
          ((n : K) + 1) / scale = (n : K) / scale + 1 / scale := by ring
          _ ≤ 1 / value n + 1 / scale := by linarith
          _ ≤ 1 / value (n + 1) := hnext
  have hceil : scale / threshold ≤ (horizon : K) := Nat.le_ceil _
  have hhorizon : (horizon : K) / scale ≤ 1 / value horizon :=
    hinverse horizon le_rfl
  have hthresholdInverse : 1 / threshold ≤ (horizon : K) / scale := by
    apply (div_le_div_iff₀ hthreshold hscale).2
    have hscaled := (div_le_iff₀ hthreshold).mp hceil
    simpa [mul_comm] using hscaled
  have hstrictInverse : 1 / value horizon < 1 / threshold :=
    one_div_lt_one_div_of_lt hthreshold (habove horizon le_rfl)
  exact (not_lt_of_ge (hthresholdInverse.trans hhorizon)) hstrictInverse

/-- Rational specialization of the ordered-field recurrence. -/
theorem exists_index_le_rationalCeil_of_quadratic_descent
    (value : ℕ → ℚ) {scale threshold : ℚ}
    (hscale : 0 < scale) (hthreshold : 0 < threshold)
    (hstep : ∀ n, 0 < value n →
      value (n + 1) ≤ value n - value n ^ 2 / scale) :
    ∃ n ≤ Nat.ceil (scale / threshold), value n ≤ threshold :=
  exists_index_le_ceil_of_quadratic_descent
    value hscale hthreshold hstep

end Math
