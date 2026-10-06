import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! # Four positive phase masses with a prescribed period survival

This branch-independent normalization supplies tails and proper hazards.
No eigenvalue or game is part of its input.
-/

noncomputable section

namespace Math

structure FourPhasePositiveMass where
  periodSurvival : ℝ
  periodSurvival_pos : 0 < periodSurvival
  normalizedWeightZero : ℝ
  normalizedWeightOne : ℝ
  normalizedWeightTwo : ℝ
  normalizedWeightThree : ℝ
  normalizedWeightZero_pos : 0 < normalizedWeightZero
  normalizedWeightOne_pos : 0 < normalizedWeightOne
  normalizedWeightTwo_pos : 0 < normalizedWeightTwo
  normalizedWeightThree_pos : 0 < normalizedWeightThree
  sum_normalizedWeight : normalizedWeightZero + normalizedWeightOne +
    normalizedWeightTwo + normalizedWeightThree = 1 - periodSurvival

namespace FourPhasePositiveMass

/-- Normalize four positive raw weights without selecting a spectral branch. -/
def ofPositiveWeights (period zero one two three : ℝ)
    (hperiod : 0 < period) (hperiod_lt : period < 1)
    (hzero : 0 < zero) (hone : 0 < one) (htwo : 0 < two) (hthree : 0 < three) :
    FourPhasePositiveMass where
  periodSurvival := period
  periodSurvival_pos := hperiod
  normalizedWeightZero := (1 - period) * zero / (zero + one + two + three)
  normalizedWeightOne := (1 - period) * one / (zero + one + two + three)
  normalizedWeightTwo := (1 - period) * two / (zero + one + two + three)
  normalizedWeightThree := (1 - period) * three / (zero + one + two + three)
  normalizedWeightZero_pos := div_pos (mul_pos (sub_pos.mpr hperiod_lt) hzero)
    (by linarith)
  normalizedWeightOne_pos := div_pos (mul_pos (sub_pos.mpr hperiod_lt) hone)
    (by linarith)
  normalizedWeightTwo_pos := div_pos (mul_pos (sub_pos.mpr hperiod_lt) htwo)
    (by linarith)
  normalizedWeightThree_pos := div_pos (mul_pos (sub_pos.mpr hperiod_lt) hthree)
    (by linarith)
  sum_normalizedWeight := by
    have hsum : zero + one + two + three ≠ 0 := ne_of_gt (by linarith)
    field_simp [hsum]

variable (data : FourPhasePositiveMass)

theorem periodSurvival_lt_one : data.periodSurvival < 1 := by
  have hsum := data.sum_normalizedWeight
  linarith [data.normalizedWeightZero_pos, data.normalizedWeightOne_pos,
    data.normalizedWeightTwo_pos, data.normalizedWeightThree_pos]

def tailZero (_data : FourPhasePositiveMass) : ℝ := 1
def tailOne : ℝ := 1 - data.normalizedWeightZero
def tailTwo : ℝ := data.tailOne - data.normalizedWeightOne
def tailThree : ℝ := data.tailTwo - data.normalizedWeightTwo
def tailFour : ℝ := data.tailThree - data.normalizedWeightThree

def hazardZero : ℝ := data.normalizedWeightZero / data.tailZero
def hazardOne : ℝ := data.normalizedWeightOne / data.tailOne
def hazardTwo : ℝ := data.normalizedWeightTwo / data.tailTwo
def hazardThree : ℝ := data.normalizedWeightThree / data.tailThree

def survivalZero : ℝ := data.tailOne / data.tailZero
def survivalOne : ℝ := data.tailTwo / data.tailOne
def survivalTwo : ℝ := data.tailThree / data.tailTwo
def survivalThree : ℝ := data.tailFour / data.tailThree

theorem tail_identities :
    data.tailOne = data.periodSurvival + data.normalizedWeightOne +
        data.normalizedWeightTwo + data.normalizedWeightThree ∧
      data.tailTwo = data.periodSurvival + data.normalizedWeightTwo +
        data.normalizedWeightThree ∧
      data.tailThree = data.periodSurvival + data.normalizedWeightThree ∧
      data.tailFour = data.periodSurvival := by
  have hsum := data.sum_normalizedWeight
  dsimp [tailOne, tailTwo, tailThree, tailFour]
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> linarith

theorem tails_pos : 0 < data.tailOne ∧ 0 < data.tailTwo ∧
    0 < data.tailThree ∧ 0 < data.tailFour := by
  obtain ⟨hOne, hTwo, hThree, hFour⟩ := data.tail_identities
  have hA := data.periodSurvival_pos
  constructor
  · rw [hOne]
    positivity [data.normalizedWeightOne_pos, data.normalizedWeightTwo_pos,
      data.normalizedWeightThree_pos]
  constructor
  · rw [hTwo]
    positivity [data.normalizedWeightTwo_pos, data.normalizedWeightThree_pos]
  constructor
  · rw [hThree]
    positivity [data.normalizedWeightThree_pos]
  · rw [hFour]
    exact hA

theorem hazard_pos_and_lt_one :
    (0 < data.hazardZero ∧ data.hazardZero < 1) ∧
      (0 < data.hazardOne ∧ data.hazardOne < 1) ∧
      (0 < data.hazardTwo ∧ data.hazardTwo < 1) ∧
      (0 < data.hazardThree ∧ data.hazardThree < 1) := by
  obtain ⟨htOne, htTwo, htThree, -⟩ := data.tails_pos
  have hA := data.periodSurvival_pos
  have hid := data.tail_identities
  unfold hazardZero hazardOne hazardTwo hazardThree tailZero
  refine ⟨⟨by simpa [tailZero] using data.normalizedWeightZero_pos, ?_⟩,
    ⟨div_pos data.normalizedWeightOne_pos htOne, ?_⟩,
    ⟨div_pos data.normalizedWeightTwo_pos htTwo, ?_⟩,
    ⟨div_pos data.normalizedWeightThree_pos htThree, ?_⟩⟩
  · have hsum := data.sum_normalizedWeight
    have hA_lt := data.periodSurvival_lt_one
    linarith [data.normalizedWeightOne_pos, data.normalizedWeightTwo_pos,
      data.normalizedWeightThree_pos]
  · apply (div_lt_one htOne).2
    rw [hid.1]
    linarith [hA, data.normalizedWeightTwo_pos, data.normalizedWeightThree_pos]
  · apply (div_lt_one htTwo).2
    rw [hid.2.1]
    linarith [hA, data.normalizedWeightThree_pos]
  · apply (div_lt_one htThree).2
    rw [hid.2.2.1]
    linarith

theorem survival_eq_one_sub_hazard :
    data.survivalZero = 1 - data.hazardZero ∧
      data.survivalOne = 1 - data.hazardOne ∧
      data.survivalTwo = 1 - data.hazardTwo ∧
      data.survivalThree = 1 - data.hazardThree := by
  obtain ⟨htOne, htTwo, htThree, -⟩ := data.tails_pos
  unfold survivalZero survivalOne survivalTwo survivalThree
    hazardZero hazardOne hazardTwo hazardThree
  constructor
  · simp [tailZero, tailOne]
  constructor
  · field_simp [ne_of_gt htOne]
    rfl
  constructor
  · field_simp [ne_of_gt htTwo]
    rfl
  · field_simp [ne_of_gt htThree]
    rfl

theorem survival_product_eq_periodSurvival :
    data.survivalZero * data.survivalOne * data.survivalTwo * data.survivalThree =
      data.periodSurvival := by
  obtain ⟨htOne, htTwo, htThree, -⟩ := data.tails_pos
  rw [← data.tail_identities.2.2.2]
  unfold survivalZero survivalOne survivalTwo survivalThree tailZero
  field_simp [ne_of_gt htOne, ne_of_gt htTwo, ne_of_gt htThree]

end FourPhasePositiveMass
end Math
