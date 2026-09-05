import MathUE.SignedFourCycleWeights
import UniformEquilibrium.Quitting.Classification.LCP.QuittingRewardAdapter

noncomputable section

namespace GameTheory

open QuittingLCPClassification

/-- Literal signed singleton-comparison input. The balance equations are not
fields: they are reconstructed from these twelve table entries. -/
structure SignedFourCycleSingletonData
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)) where
  b : Fin 4 → ℝ
  g : Fin 4 → ℝ
  h : Fin 4 → ℝ
  b_pos : ∀ i, 0 < b i
  h_pos : ∀ i, 0 < h i
  successor : ∀ i, quittingSingletonMatrix reward i (i + 1) = -b i
  opposite : ∀ i, quittingSingletonMatrix reward i (i + 2) = g i
  predecessor : ∀ i, quittingSingletonMatrix reward i (i + 3) = h i

namespace SignedFourCycleSingletonData

variable {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
variable (data : SignedFourCycleSingletonData reward)

def coefficients : Math.SignedFourCycleCoefficients where
  aZero := data.g 0 / data.b 0
  aOne := data.g 1 / data.b 1
  aTwo := data.g 2 / data.b 2
  aThree := data.g 3 / data.b 3
  dZero := data.h 0 / data.b 0
  dOne := data.h 1 / data.b 1
  dTwo := data.h 2 / data.b 2
  dThree := data.h 3 / data.b 3

/-- Strict spectral and raw-weight positivity tests on the coefficients
computed from the actual reward table. -/
structure StrictTests : Prop where
  discriminant_pos : 0 < data.coefficients.discriminant
  smallerEigenvalue_gt_one : 1 < data.coefficients.smallerEigenvalue
  upperRight_neg : data.coefficients.upperRight < 0
  rawWeightOne_pos : 0 < data.coefficients.rawWeightOne
  rawWeightTwo_pos : 0 < data.coefficients.rawWeightTwo
  rawWeightThree_pos : 0 < data.coefficients.rawWeightThree

def StrictTests.weights (tests : data.StrictTests) : Math.SignedFourCycleStrictData where
  coefficients := data.coefficients
  discriminant_pos := tests.discriminant_pos
  smallerEigenvalue_gt_one := tests.smallerEigenvalue_gt_one
  upperRight_neg := tests.upperRight_neg
  rawWeightOne_pos := tests.rawWeightOne_pos
  rawWeightTwo_pos := tests.rawWeightTwo_pos
  rawWeightThree_pos := tests.rawWeightThree_pos

/-- All four cyclic weighted balances for the actual singleton comparison
matrix of the supplied reward table. -/
theorem weighted_singleton_comparison_balances (tests : data.StrictTests) :
    let weights := tests.weights
    weights.normalizedWeightOne * quittingSingletonMatrix reward 0 1 +
        weights.normalizedWeightTwo * quittingSingletonMatrix reward 0 2 +
        weights.normalizedWeightThree * quittingSingletonMatrix reward 0 3 = 0 ∧
    weights.normalizedWeightTwo * quittingSingletonMatrix reward 1 2 +
        weights.normalizedWeightThree * quittingSingletonMatrix reward 1 3 +
        data.coefficients.periodSurvival * weights.normalizedWeightZero *
          quittingSingletonMatrix reward 1 0 = 0 ∧
    weights.normalizedWeightThree * quittingSingletonMatrix reward 2 3 +
        data.coefficients.periodSurvival *
          (weights.normalizedWeightZero * quittingSingletonMatrix reward 2 0 +
            weights.normalizedWeightOne * quittingSingletonMatrix reward 2 1) = 0 ∧
    data.coefficients.periodSurvival *
        (weights.normalizedWeightZero * quittingSingletonMatrix reward 3 0 +
          weights.normalizedWeightOne * quittingSingletonMatrix reward 3 1 +
          weights.normalizedWeightTwo * quittingSingletonMatrix reward 3 2) = 0 := by
  dsimp only
  let weights := tests.weights
  have hbalances := data.coefficients.reconstructed_balance_identities
    tests.discriminant_pos.le tests.smallerEigenvalue_gt_one
  have hb0 := data.b_pos 0
  have hb1 := data.b_pos 1
  have hb2 := data.b_pos 2
  have hb3 := data.b_pos 3
  have hs0 : quittingSingletonMatrix reward 0 1 = -data.b 0 := by
    simpa using data.successor 0
  have ho0 : quittingSingletonMatrix reward 0 2 = data.g 0 := by
    simpa using data.opposite 0
  have hp0 : quittingSingletonMatrix reward 0 3 = data.h 0 := by
    simpa using data.predecessor 0
  have hs1 : quittingSingletonMatrix reward 1 2 = -data.b 1 := by
    simpa using data.successor 1
  have ho1 : quittingSingletonMatrix reward 1 3 = data.g 1 := by
    simpa using data.opposite 1
  have hp1 : quittingSingletonMatrix reward 1 0 = data.h 1 := by
    simpa using data.predecessor 1
  have hs2 : quittingSingletonMatrix reward 2 3 = -data.b 2 := by
    simpa using data.successor 2
  have ho2 : quittingSingletonMatrix reward 2 0 = data.g 2 := by
    simpa using data.opposite 2
  have hp2 : quittingSingletonMatrix reward 2 1 = data.h 2 := by
    simpa using data.predecessor 2
  have hs3 : quittingSingletonMatrix reward 3 0 = -data.b 3 := by
    simpa using data.successor 3
  have ho3 : quittingSingletonMatrix reward 3 1 = data.g 3 := by
    simpa using data.opposite 3
  have hp3 : quittingSingletonMatrix reward 3 2 = data.h 3 := by
    simpa using data.predecessor 3
  rw [hs0, ho0, hp0, hs1, ho1, hp1, hs2, ho2, hp2, hs3, ho3, hp3]
  have hw0 : weights.normalizedWeightZero =
      ((1 - data.coefficients.periodSurvival) / weights.rawWeightSum) *
        data.coefficients.rawWeightZero := by
    unfold Math.SignedFourCycleStrictData.normalizedWeightZero
    dsimp [weights, StrictTests.weights]
    ring
  have hw1 : weights.normalizedWeightOne =
      ((1 - data.coefficients.periodSurvival) / weights.rawWeightSum) *
        data.coefficients.rawWeightOne := by
    unfold Math.SignedFourCycleStrictData.normalizedWeightOne
    dsimp [weights, StrictTests.weights]
    ring
  have hw2 : weights.normalizedWeightTwo =
      ((1 - data.coefficients.periodSurvival) / weights.rawWeightSum) *
        data.coefficients.rawWeightTwo := by
    unfold Math.SignedFourCycleStrictData.normalizedWeightTwo
    dsimp [weights, StrictTests.weights]
    ring
  have hw3 : weights.normalizedWeightThree =
      ((1 - data.coefficients.periodSurvival) / weights.rawWeightSum) *
        data.coefficients.rawWeightThree := by
    unfold Math.SignedFourCycleStrictData.normalizedWeightThree
    dsimp [weights, StrictTests.weights]
    ring
  have hbal0 : data.b 0 * data.coefficients.rawWeightOne =
      data.g 0 * data.coefficients.rawWeightTwo +
        data.h 0 * data.coefficients.rawWeightThree := by
    rw [hbalances.1]
    dsimp [coefficients]
    field_simp [ne_of_gt hb0]
  have hbal1 : data.b 1 * data.coefficients.rawWeightTwo =
      data.coefficients.periodSurvival * data.h 1 *
          data.coefficients.rawWeightZero +
        data.g 1 * data.coefficients.rawWeightThree := by
    rw [hbalances.2.2.1]
    dsimp [coefficients]
    field_simp [ne_of_gt hb1]
  have hbal2 : data.b 2 * data.coefficients.rawWeightThree =
      data.coefficients.periodSurvival *
        (data.g 2 * data.coefficients.rawWeightZero +
          data.h 2 * data.coefficients.rawWeightOne) := by
    rw [hbalances.2.2.2]
    dsimp [coefficients]
    field_simp [ne_of_gt hb2]
  have hbal3 : data.b 3 * data.coefficients.rawWeightZero =
      data.g 3 * data.coefficients.rawWeightOne +
        data.h 3 * data.coefficients.rawWeightTwo := by
    rw [hbalances.2.1]
    dsimp [coefficients]
    field_simp [ne_of_gt hb3]
  rw [hw0, hw1, hw2, hw3]
  constructor
  · linear_combination
      -((1 - data.coefficients.periodSurvival) / weights.rawWeightSum) * hbal0
  constructor
  · linear_combination
      -((1 - data.coefficients.periodSurvival) / weights.rawWeightSum) * hbal1
  constructor
  · linear_combination
      -((1 - data.coefficients.periodSurvival) / weights.rawWeightSum) * hbal2
  · linear_combination
      -(data.coefficients.periodSurvival *
        ((1 - data.coefficients.periodSurvival) / weights.rawWeightSum)) * hbal3

end SignedFourCycleSingletonData
end GameTheory
