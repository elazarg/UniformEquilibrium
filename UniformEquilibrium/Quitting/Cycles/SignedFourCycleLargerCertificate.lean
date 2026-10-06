import UniformEquilibrium.Quitting.Cycles.SignedFourCycleLargerRewardAdapter
import UniformEquilibrium.Quitting.Cycles.FourPhaseSingletonCertificate

/-! # A behavioral equilibrium from the larger spectral branch

All masses and singleton balances are computed from literal raw table tests.
The branch-independent compiler supplies the fixed target and behavioral caps.
-/

noncomputable section

namespace GameTheory.SignedFourCycleSingletonData

variable {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
variable (data : SignedFourCycleSingletonData reward) (tests : data.LargerTests)

def largerPositiveMass : Math.FourPhasePositiveMass :=
  Math.FourPhasePositiveMass.ofPositiveWeights data.coefficients.largerPeriodSurvival
    data.coefficients.largerRawWeightZero data.coefficients.largerRawWeightOne
    data.coefficients.largerRawWeightTwo data.coefficients.largerRawWeightThree
    (data.larger_weights_positive_of_raw_tests tests).1
    (data.larger_weights_positive_of_raw_tests tests).2.1
    (data.larger_weights_positive_of_raw_tests tests).2.2.1
    (data.larger_weights_positive_of_raw_tests tests).2.2.2.1
    (data.larger_weights_positive_of_raw_tests tests).2.2.2.2.1
    (data.larger_weights_positive_of_raw_tests tests).2.2.2.2.2

theorem larger_singleton_balances :
    FourPhaseSingletonValues.HasSingletonBalance reward (data.largerPositiveMass tests) := by
  have hbalance := data.coefficients.larger_reconstructed_balance_identities
    tests.coefficientTests.characteristic_one_neg
  have hone : data.coefficients.largerRawWeightTwo =
      data.coefficients.largerPeriodSurvival * data.coefficients.dOne *
        data.coefficients.largerRawWeightZero +
      data.coefficients.aOne * data.coefficients.largerRawWeightThree := rfl
  have htwo : data.coefficients.largerRawWeightThree =
      data.coefficients.largerPeriodSurvival *
        (data.coefficients.aTwo * data.coefficients.largerRawWeightZero +
          data.coefficients.dTwo * data.coefficients.largerRawWeightOne) := rfl
  unfold FourPhaseSingletonValues.HasSingletonBalance
  rw [data.singletonMatrix_eq_diagonal_mul_normalized]
  simp only [Matrix.diagonal_mul]
  simp only [Math.SignedFourCycleCoefficients.normalizedComparisonMatrix,
    Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  dsimp only [largerPositiveMass, Math.FourPhasePositiveMass.ofPositiveWeights]
  let factor := (1 - data.coefficients.largerPeriodSurvival) /
    (data.coefficients.largerRawWeightZero + data.coefficients.largerRawWeightOne +
      data.coefficients.largerRawWeightTwo + data.coefficients.largerRawWeightThree)
  constructor
  · linear_combination -(data.b 0 * factor) * hbalance.1
  constructor
  · linear_combination -(data.b 1 * factor) * hone
  constructor
  · linear_combination -(data.b 2 * factor) * htwo
  · linear_combination -(data.coefficients.largerPeriodSurvival * data.b 3 * factor) *
      hbalance.2

def largerTargetValue : Payoff (Fin 4) :=
  FourPhaseSingletonValues.targetValue reward (data.largerPositiveMass tests)

def largerCertificate : BalancedSingletonCycleCertificate (L := 4) reward :=
  FourPhaseSingletonValues.certificate data (data.largerPositiveMass tests)
    (data.larger_singleton_balances tests)

/-- One computed target works for every accuracy and unrestricted behavioral deviation. -/
theorem largerTargetValue_isUniformEquilibriumPayoff :
    (quittingGame reward).IsUniformEquilibriumPayoff none (data.largerTargetValue tests) :=
  FourPhaseSingletonValues.targetValue_isUniformEquilibriumPayoff data
    (data.largerPositiveMass tests) (data.larger_singleton_balances tests)

end GameTheory.SignedFourCycleSingletonData
