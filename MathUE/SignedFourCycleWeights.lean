import MathUE.SignedFourCycleAlgebra

noncomputable section

namespace Math

/-- The strict spectral tests, attached to raw coefficients only after the
smaller-eigenvalue reconstruction has been defined. -/
structure SignedFourCycleStrictData where
  coefficients : SignedFourCycleCoefficients
  discriminant_pos : 0 < coefficients.discriminant
  smallerEigenvalue_gt_one : 1 < coefficients.smallerEigenvalue
  upperRight_neg : coefficients.upperRight < 0
  rawWeightOne_pos : 0 < coefficients.rawWeightOne
  rawWeightTwo_pos : 0 < coefficients.rawWeightTwo
  rawWeightThree_pos : 0 < coefficients.rawWeightThree

namespace SignedFourCycleStrictData

variable (data : SignedFourCycleStrictData)

def rawWeightSum : ℝ :=
  data.coefficients.rawWeightZero + data.coefficients.rawWeightOne +
    data.coefficients.rawWeightTwo + data.coefficients.rawWeightThree

def normalizedWeightZero : ℝ :=
  (1 - data.coefficients.periodSurvival) * data.coefficients.rawWeightZero / data.rawWeightSum
def normalizedWeightOne : ℝ :=
  (1 - data.coefficients.periodSurvival) * data.coefficients.rawWeightOne / data.rawWeightSum
def normalizedWeightTwo : ℝ :=
  (1 - data.coefficients.periodSurvival) * data.coefficients.rawWeightTwo / data.rawWeightSum
def normalizedWeightThree : ℝ :=
  (1 - data.coefficients.periodSurvival) * data.coefficients.rawWeightThree / data.rawWeightSum

theorem rawWeightZero_pos : 0 < data.coefficients.rawWeightZero :=
  data.coefficients.rawWeightZero_pos data.upperRight_neg

theorem rawWeightSum_pos : 0 < data.rawWeightSum := by
  unfold rawWeightSum
  nlinarith [data.rawWeightZero_pos, data.rawWeightOne_pos,
    data.rawWeightTwo_pos, data.rawWeightThree_pos]

theorem normalizedWeightZero_pos : 0 < data.normalizedWeightZero := by
  unfold normalizedWeightZero
  positivity [data.coefficients.periodSurvival_lt_one data.smallerEigenvalue_gt_one,
    data.rawWeightZero_pos, data.rawWeightSum_pos]

theorem normalizedWeightOne_pos : 0 < data.normalizedWeightOne := by
  unfold normalizedWeightOne
  positivity [data.coefficients.periodSurvival_lt_one data.smallerEigenvalue_gt_one,
    data.rawWeightOne_pos, data.rawWeightSum_pos]

theorem normalizedWeightTwo_pos : 0 < data.normalizedWeightTwo := by
  unfold normalizedWeightTwo
  positivity [data.coefficients.periodSurvival_lt_one data.smallerEigenvalue_gt_one,
    data.rawWeightTwo_pos, data.rawWeightSum_pos]

theorem normalizedWeightThree_pos : 0 < data.normalizedWeightThree := by
  unfold normalizedWeightThree
  positivity [data.coefficients.periodSurvival_lt_one data.smallerEigenvalue_gt_one,
    data.rawWeightThree_pos, data.rawWeightSum_pos]

theorem sum_normalizedWeight :
    data.normalizedWeightZero + data.normalizedWeightOne +
        data.normalizedWeightTwo + data.normalizedWeightThree =
      1 - data.coefficients.periodSurvival := by
  unfold normalizedWeightZero normalizedWeightOne normalizedWeightTwo
    normalizedWeightThree
  have hne : data.rawWeightSum ≠ 0 := ne_of_gt data.rawWeightSum_pos
  field_simp [hne]
  unfold rawWeightSum
  ring_nf

def tailZero (_data : SignedFourCycleStrictData) : ℝ := 1
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
    data.tailOne = data.coefficients.periodSurvival + data.normalizedWeightOne +
        data.normalizedWeightTwo + data.normalizedWeightThree ∧
      data.tailTwo = data.coefficients.periodSurvival + data.normalizedWeightTwo +
        data.normalizedWeightThree ∧
      data.tailThree = data.coefficients.periodSurvival + data.normalizedWeightThree ∧
      data.tailFour = data.coefficients.periodSurvival := by
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
  have hA := data.coefficients.periodSurvival_pos data.smallerEigenvalue_gt_one
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
  have hA := data.coefficients.periodSurvival_pos data.smallerEigenvalue_gt_one
  have hid := data.tail_identities
  unfold hazardZero hazardOne hazardTwo hazardThree tailZero
  refine ⟨⟨by simpa [tailZero] using data.normalizedWeightZero_pos, ?_⟩,
    ⟨div_pos data.normalizedWeightOne_pos htOne, ?_⟩,
    ⟨div_pos data.normalizedWeightTwo_pos htTwo, ?_⟩,
    ⟨div_pos data.normalizedWeightThree_pos htThree, ?_⟩⟩
  · have hsum := data.sum_normalizedWeight
    have hA_lt := data.coefficients.periodSurvival_lt_one data.smallerEigenvalue_gt_one
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
      data.coefficients.periodSurvival := by
  obtain ⟨htOne, htTwo, htThree, -⟩ := data.tails_pos
  rw [← data.tail_identities.2.2.2]
  unfold survivalZero survivalOne survivalTwo survivalThree tailZero
  field_simp [ne_of_gt htOne, ne_of_gt htTwo, ne_of_gt htThree]

end SignedFourCycleStrictData
end Math
