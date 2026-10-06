import MathUE.SignedFourCycleAlgebra
import MathUE.FourPhasePositiveMass

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

/-- Shared phase construction, independent of the selected spectral branch. -/
def positiveMass : FourPhasePositiveMass where
  periodSurvival := data.coefficients.periodSurvival
  periodSurvival_pos := data.coefficients.periodSurvival_pos data.smallerEigenvalue_gt_one
  normalizedWeightZero := data.normalizedWeightZero
  normalizedWeightOne := data.normalizedWeightOne
  normalizedWeightTwo := data.normalizedWeightTwo
  normalizedWeightThree := data.normalizedWeightThree
  normalizedWeightZero_pos := data.normalizedWeightZero_pos
  normalizedWeightOne_pos := data.normalizedWeightOne_pos
  normalizedWeightTwo_pos := data.normalizedWeightTwo_pos
  normalizedWeightThree_pos := data.normalizedWeightThree_pos
  sum_normalizedWeight := data.sum_normalizedWeight

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
      data.tailFour = data.coefficients.periodSurvival :=
  data.positiveMass.tail_identities

theorem tails_pos : 0 < data.tailOne ∧ 0 < data.tailTwo ∧
    0 < data.tailThree ∧ 0 < data.tailFour :=
  data.positiveMass.tails_pos

theorem hazard_pos_and_lt_one :
    (0 < data.hazardZero ∧ data.hazardZero < 1) ∧
      (0 < data.hazardOne ∧ data.hazardOne < 1) ∧
      (0 < data.hazardTwo ∧ data.hazardTwo < 1) ∧
      (0 < data.hazardThree ∧ data.hazardThree < 1) :=
  data.positiveMass.hazard_pos_and_lt_one

theorem survival_eq_one_sub_hazard :
    data.survivalZero = 1 - data.hazardZero ∧
      data.survivalOne = 1 - data.hazardOne ∧
      data.survivalTwo = 1 - data.hazardTwo ∧
      data.survivalThree = 1 - data.hazardThree :=
  data.positiveMass.survival_eq_one_sub_hazard

theorem survival_product_eq_periodSurvival :
    data.survivalZero * data.survivalOne * data.survivalTwo * data.survivalThree =
      data.coefficients.periodSurvival :=
  data.positiveMass.survival_product_eq_periodSurvival

end SignedFourCycleStrictData
end Math
