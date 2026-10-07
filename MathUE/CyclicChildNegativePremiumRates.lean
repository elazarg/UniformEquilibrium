import MathUE.RationalizedQuadraticBracketRoot
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! # Rates for the negative-premium cyclic-child construction

The selected quadratic root is continuous on the closed interval, with zero
pivot rate at its right endpoint. Polynomial identities recover the actual
rational child and pivot balances.
-/

noncomputable section

namespace Math.CyclicChildNegativePremium

def leading (loss y : ℝ) : ℝ := -(16 + loss - 12 * y)
def linear (loss y : ℝ) : ℝ :=
  (9 * loss - 36) * y ^ 2 + (32 - 10 * loss) * y + 13
def constant (y : ℝ) : ℝ := -13 * y * (2 - 3 * y)
def cap (y : ℝ) : ℝ := (3 - 4 * y) / (4 - 3 * y)
def childPolynomial (loss p y : ℝ) : ℝ :=
  quadraticBracketValue (leading loss y) (linear loss y) (constant y) p
def selected (loss y : ℝ) : ℝ :=
  rationalizedQuadraticRoot (leading loss y) (linear loss y) (constant y)
def second (p y : ℝ) : ℝ := (p + y) / (3 * (1 - p) * (1 - y))
def denominator (p y : ℝ) : ℝ := 1 + 3 * y - p
def third (p y : ℝ) : ℝ := (3 * y - p) / denominator p y
def childBalance (loss p y : ℝ) : ℝ :=
  p * (1 - loss) / (1 - p) + second p y -
    (1 - second p y) * (3 * third p y - loss * p * (1 - third p y))
def pivotBalance (loss p y : ℝ) : ℝ :=
  (1 - loss * y) / (1 - y) - 2 +
    (1 - second p y) * (1 + loss * y) / denominator p y
def pivotPolynomial (loss p y : ℝ) : ℝ :=
  (6 * y - 3 - 3 * loss * y) * p ^ 2 +
    (12 * loss * y ^ 2 + 2 * loss * y - 18 * y ^ 2 + 2) * p +
    (18 - 13 * loss) * y ^ 2 - 7 * y

theorem cap_bounds {y : ℝ} (hy : y ∈ Set.Icc (2 / 5 : ℝ) (2 / 3)) :
    0 < cap y ∧ cap y ≤ 1 / 2 := by
  have hden : 0 < 4 - 3 * y := by linarith [hy.2]
  refine ⟨div_pos (by linarith [hy.2]) hden, ?_⟩
  unfold cap
  rw [div_le_iff₀ hden]
  linarith [hy.1]

theorem linear_pos {loss y : ℝ} (hloss : loss ∈ Set.Icc (0 : ℝ) 1)
    (hy : y ∈ Set.Icc (2 / 5 : ℝ) (2 / 3)) : 0 < linear loss y := by
  have hmul := mul_nonneg
    (show 0 ≤ 36 - 9 * loss by linarith [hloss.2])
    (show 0 ≤ 2 / 3 - y by linarith [hy.2])
  have hcoefficient : 4 ≤ 32 - 10 * loss - (36 - 9 * loss) * y := by
    nlinarith [hloss.2]
  have hproduct := mul_nonneg (show 0 ≤ y by linarith [hy.1])
    (sub_nonneg.mpr hcoefficient)
  have hid : linear loss y = 13 + 4 * y +
      y * (32 - 10 * loss - (36 - 9 * loss) * y - 4) := by
    unfold linear
    ring
  rw [hid]
  exact add_pos_of_pos_of_nonneg (by linarith [hy.1]) hproduct

theorem cap_polynomial_eq {loss y : ℝ}
    (hy : y ∈ Set.Icc (2 / 5 : ℝ) (2 / 3)) :
    childPolynomial loss (cap y) y =
      3 * (y - 1) * (9 * y ^ 2 - 13 * y - 1) *
        (4 - 3 * y - loss * (3 - 4 * y)) / (3 * y - 4) ^ 2 := by
  have hden : 4 - 3 * y ≠ 0 := ne_of_gt (by linarith [hy.2])
  rw [show (3 * y - 4) ^ 2 = (4 - 3 * y) ^ 2 by ring]
  unfold childPolynomial quadraticBracketValue leading linear constant cap
  generalize hcapDen : 4 - 3 * y = capDen at hden ⊢
  field_simp [hden]
  rw [← hcapDen]
  ring

theorem cap_polynomial_pos {loss y : ℝ} (hloss : loss ∈ Set.Icc (0 : ℝ) 1)
    (hy : y ∈ Set.Icc (2 / 5 : ℝ) (2 / 3)) :
    0 < childPolynomial loss (cap y) y := by
  have hy0 : 0 < y := by linarith [hy.1]
  have hy1 : y < 1 := by linarith [hy.2]
  have hpoly : 9 * y ^ 2 - 13 * y - 1 < 0 := by
    nlinarith [mul_nonneg hy0.le (sub_nonneg.mpr hy.2)]
  have hlast : 0 < 4 - 3 * y - loss * (3 - 4 * y) := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hloss.2)
      (show 0 ≤ 3 - 4 * y by linarith [hy.2])]
  rw [cap_polynomial_eq hy]
  apply div_pos
  · exact mul_pos (mul_pos_of_neg_of_neg
      (mul_neg_of_pos_of_neg (by norm_num) (sub_neg.mpr hy1)) hpoly) hlast
  · exact sq_pos_of_ne_zero (by linarith [hy.2])

theorem selected_spec {loss y : ℝ} (hloss : loss ∈ Set.Icc (0 : ℝ) 1)
    (hy : y ∈ Set.Ico (2 / 5 : ℝ) (2 / 3)) :
    selected loss y ∈ Set.Ioo (0 : ℝ) (cap y) ∧
      childPolynomial loss (selected loss y) y = 0 ∧
      0 < 2 * leading loss y * selected loss y + linear loss y := by
  have hconstant : constant y < 0 := by
    unfold constant
    exact mul_neg_of_neg_of_pos
      (mul_neg_of_neg_of_pos (by norm_num) (by linarith [hy.1]))
      (by linarith [hy.2])
  have hroot := rationalizedQuadraticRoot_spec hconstant
    (cap_bounds ⟨hy.1, hy.2.le⟩).1 (cap_polynomial_pos hloss ⟨hy.1, hy.2.le⟩)
  exact ⟨hroot.2.2.1, hroot.2.2.2.1, hroot.2.2.2.2.1⟩

theorem selected_right (loss : ℝ) : selected loss (2 / 3) = 0 := by
  unfold selected
  rw [show constant (2 / 3) = 0 by norm_num [constant]]
  exact rationalizedQuadraticRoot_constant_zero _ _

theorem selected_right_derivative_pos {loss : ℝ} (hloss : loss ∈ Set.Icc (0 : ℝ) 1) :
    0 < 2 * leading loss (2 / 3) * selected loss (2 / 3) + linear loss (2 / 3) := by
  rw [selected_right, mul_zero, zero_add]
  exact linear_pos hloss ⟨by norm_num, le_rfl⟩

theorem selected_continuous {loss : ℝ} (hloss : loss ∈ Set.Icc (0 : ℝ) 1) :
    ContinuousOn (selected loss) (Set.Icc (2 / 5 : ℝ) (2 / 3)) := by
  unfold selected
  apply continuousOn_rationalizedQuadraticRoot_of_linear_pos
  · unfold leading
    fun_prop
  · unfold linear
    fun_prop
  · unfold constant
    fun_prop
  · intro y hy
    exact linear_pos hloss hy

theorem selected_closed_bounds {loss y : ℝ} (hloss : loss ∈ Set.Icc (0 : ℝ) 1)
    (hy : y ∈ Set.Icc (2 / 5 : ℝ) (2 / 3)) :
    0 ≤ selected loss y ∧ selected loss y < cap y := by
  by_cases hright : y = 2 / 3
  · subst y
    rw [selected_right]
    exact ⟨le_rfl, (cap_bounds hy).1⟩
  · have hs := (selected_spec hloss ⟨hy.1, lt_of_le_of_ne hy.2 hright⟩).1
    exact ⟨hs.1.le, hs.2⟩

theorem rates_spec {p y : ℝ} (hy : y ∈ Set.Icc (2 / 5 : ℝ) (2 / 3))
    (hp : 0 ≤ p ∧ p < cap y) :
    p < 1 / 2 ∧ 0 < denominator p y ∧
      second p y ∈ Set.Ioo (0 : ℝ) 1 ∧ third p y ∈ Set.Ioo (0 : ℝ) 1 := by
  have hpHalf : p < 1 / 2 := hp.2.trans_le (cap_bounds hy).2
  have hpy : 0 < 1 - p := by linarith
  have hyy : 0 < 1 - y := by linarith [hy.2]
  have hcapDen : 0 < 4 - 3 * y := by linarith [hy.2]
  have hpCap : p * (4 - 3 * y) < 3 - 4 * y :=
    (lt_div_iff₀ hcapDen).mp hp.2
  have hden : 0 < denominator p y := by unfold denominator; linarith [hy.1]
  refine ⟨hpHalf, hden, ?_, ?_⟩
  · unfold second
    refine ⟨div_pos (by linarith [hy.1]) (mul_pos (mul_pos (by norm_num) hpy) hyy), ?_⟩
    rw [div_lt_one (mul_pos (mul_pos (by norm_num) hpy) hyy)]
    nlinarith only [hpCap]
  · unfold third
    refine ⟨div_pos (by linarith [hy.1]) hden, ?_⟩
    rw [div_lt_one hden]
    unfold denominator
    linarith

theorem child_balance_identity {loss p y : ℝ}
    (hp : p < 1) (hy : y < 1) (hden : 0 < denominator p y) :
    childBalance loss p y * (3 * (1 - p) * (1 - y) * denominator p y) =
      childPolynomial loss p y := by
  unfold childBalance second third childPolynomial quadraticBracketValue
    leading linear constant
  field_simp [(sub_pos.mpr hp).ne', (sub_pos.mpr hy).ne', hden.ne']
  unfold denominator
  ring

theorem pivot_balance_identity {loss p y : ℝ}
    (hp : p < 1) (hy : y < 1) (hden : 0 < denominator p y) :
    pivotBalance loss p y * (3 * (1 - p) * (1 - y) * denominator p y) =
      pivotPolynomial loss p y := by
  unfold pivotBalance second pivotPolynomial
  field_simp [(sub_pos.mpr hp).ne', (sub_pos.mpr hy).ne', hden.ne']
  unfold denominator
  ring

theorem selected_left_lower {loss : ℝ} (hloss : loss ∈ Set.Icc (0 : ℝ) 1) :
    1 / 5 < selected loss (2 / 5) := by
  let root := selected loss (2 / 5)
  have hs := selected_spec hloss (show (2 / 5 : ℝ) ∈ Set.Ico (2 / 5) (2 / 3)
    from ⟨le_rfl, by norm_num⟩)
  have hcap : cap (2 / 5) = 1 / 2 := by norm_num [cap]
  rw [hcap] at hs
  have hleading : leading loss (2 / 5) < 0 := by
    unfold leading
    linarith [hloss.1]
  have hcapValue := cap_polynomial_pos hloss
    (show (2 / 5 : ℝ) ∈ Set.Icc (2 / 5) (2 / 3) from ⟨le_rfl, by norm_num⟩)
  rw [hcap] at hcapValue
  have hfactor (point : ℝ) : childPolynomial loss point (2 / 5) =
      (point - root) * (leading loss (2 / 5) * (point + root) + linear loss (2 / 5)) := by
    have hzero := hs.2.1
    change childPolynomial loss root (2 / 5) = 0 at hzero
    unfold childPolynomial quadraticBracketValue at hzero ⊢
    nlinarith only [hzero]
  rw [hfactor] at hcapValue
  have hcoefficient : 0 < leading loss (2 / 5) * (1 / 2 + root) + linear loss (2 / 5) :=
    pos_of_mul_pos_right hcapValue (sub_pos.mpr hs.1.2).le
  by_contra hnot
  have hsmall : root ≤ 1 / 5 := le_of_not_gt hnot
  have hcoefficient' : 0 < leading loss (2 / 5) * (1 / 5 + root) + linear loss (2 / 5) := by
    nlinarith only [hcoefficient, hleading]
  have hnonnegative := mul_nonneg (sub_nonneg.mpr hsmall) hcoefficient'.le
  rw [← hfactor] at hnonnegative
  have hvalue : childPolynomial loss (1 / 5) (2 / 5) = -3 * (23 * loss + 25) / 125 := by
    unfold childPolynomial quadraticBracketValue leading linear constant
    ring
  rw [hvalue] at hnonnegative
  nlinarith only [hnonnegative, hloss.1]

theorem pivot_left_neg {loss : ℝ} (hloss : loss ∈ Set.Icc (0 : ℝ) 1) :
    pivotPolynomial loss (selected loss (2 / 5)) (2 / 5) < 0 := by
  let p := selected loss (2 / 5)
  have hpLower : 1 / 5 < p := selected_left_lower hloss
  have hpUpper : p < 1 / 2 := ((selected_spec hloss
    (show (2 / 5 : ℝ) ∈ Set.Ico (2 / 5) (2 / 3) from ⟨le_rfl, by norm_num⟩)).1.2).trans_le
      (cap_bounds ⟨le_rfl, by norm_num⟩).2
  have hbase : -3 * p ^ 2 / 5 - 22 * p / 25 + 2 / 25 < 0 := by
    nlinarith only [hpLower, sq_nonneg p]
  have hcoefficient : -6 * p ^ 2 / 5 + 68 * p / 25 - 52 / 25 < 0 := by
    nlinarith only [hpUpper, sq_nonneg p]
  have hproduct := mul_nonpos_of_nonneg_of_nonpos hloss.1 hcoefficient.le
  have hid : pivotPolynomial loss p (2 / 5) =
      (-3 * p ^ 2 / 5 - 22 * p / 25 + 2 / 25) +
        loss * (-6 * p ^ 2 / 5 + 68 * p / 25 - 52 / 25) := by
    unfold pivotPolynomial
    ring
  rw [hid]
  linarith only [hbase, hproduct]

theorem pivot_right_eq (loss : ℝ) :
    pivotPolynomial loss (selected loss (2 / 3)) (2 / 3) = (30 - 52 * loss) / 9 := by
  rw [selected_right]
  unfold pivotPolynomial
  ring

theorem pivot_continuous {loss : ℝ} (hloss : loss ∈ Set.Icc (0 : ℝ) 1) :
    ContinuousOn (fun y => pivotPolynomial loss (selected loss y) y)
      (Set.Icc (2 / 5 : ℝ) (2 / 3)) := by
  unfold pivotPolynomial
  have hselected := selected_continuous hloss
  fun_prop

/-- The scalar crossing internally produces the four proper rates, their
positive rational denominators and both actual balance equations. -/
theorem exists_low_rates {loss : ℝ} (hloss : loss ∈ Set.Ioo (0 : ℝ) (15 / 26)) :
    ∃ y ∈ Set.Ioo (2 / 5 : ℝ) (2 / 3),
      selected loss y ∈ Set.Ioo (0 : ℝ) (1 / 2) ∧
      0 < denominator (selected loss y) y ∧
      second (selected loss y) y ∈ Set.Ioo (0 : ℝ) 1 ∧
      third (selected loss y) y ∈ Set.Ioo (0 : ℝ) 1 ∧
      childBalance loss (selected loss y) y = 0 ∧
      pivotBalance loss (selected loss y) y = 0 := by
  have hbox : loss ∈ Set.Icc (0 : ℝ) 1 := ⟨hloss.1.le, by linarith [hloss.2]⟩
  have hright : 0 < pivotPolynomial loss (selected loss (2 / 3)) (2 / 3) := by
    rw [pivot_right_eq]
    linarith [hloss.2]
  obtain ⟨y, hy, hzero⟩ := intermediate_value_Ioo
    (show (2 / 5 : ℝ) ≤ 2 / 3 by norm_num) (pivot_continuous hbox)
    ⟨pivot_left_neg hbox, hright⟩
  change pivotPolynomial loss (selected loss y) y = 0 at hzero
  have hs := selected_spec hbox ⟨hy.1.le, hy.2⟩
  have hr := rates_spec (Set.Ioo_subset_Icc_self hy) ⟨hs.1.1.le, hs.1.2⟩
  have hp : selected loss y < 1 := by linarith only [hr.1]
  have hy1 : y < 1 := by linarith only [hy.2]
  have hproduct : 0 < 3 * (1 - selected loss y) * (1 - y) *
      denominator (selected loss y) y :=
    mul_pos (mul_pos (mul_pos (by norm_num) (sub_pos.mpr hp))
      (sub_pos.mpr hy1)) hr.2.1
  refine ⟨y, hy, ⟨hs.1.1, hr.1⟩, hr.2.1, hr.2.2.1, hr.2.2.2, ?_, ?_⟩
  · have hid := child_balance_identity (loss := loss) hp hy1 hr.2.1
    rw [hs.2.1] at hid
    exact (mul_eq_zero.mp hid).resolve_right hproduct.ne'
  · have hid := pivot_balance_identity (loss := loss) hp hy1 hr.2.1
    rw [hzero] at hid
    exact (mul_eq_zero.mp hid).resolve_right hproduct.ne'

theorem boundary_rates : second 0 (2 / 3) = 2 / 3 ∧ third 0 (2 / 3) = 2 / 3 := by
  norm_num [second, third, denominator]

end Math.CyclicChildNegativePremium
