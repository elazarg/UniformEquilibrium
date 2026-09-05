import UniformEquilibrium.Quitting.Cycles.SignedFourCycleValues
import UniformEquilibrium.Diagnostics.Quitting.SignedFourCycleRawSpectralFixtures

noncomputable section

namespace GameTheory.SignedFourCycleValueFixtures

open SignedFourCycleRawSpectralFixtures

def oneOwn : Fin 4 → ℝ := fun _ ↦ 1

theorem rewardWithSingletonMatrix_singleton (M) (own) (other) (i j : Fin 4) :
    rewardWithSingletonMatrix M own other
        ⟨{j}, Finset.singleton_nonempty j⟩ i =
      own i + M i j := by
  simp [rewardWithSingletonMatrix]

theorem rewardWithSingletonMatrix_nonsingleton (M) (own) (other)
    (S : {S : Finset (Fin 4) // S.Nonempty}) (hS : S.1.card ≠ 1) :
    rewardWithSingletonMatrix M own other S = other S := by
  simp [rewardWithSingletonMatrix, hS]

theorem star_own_singletons (other) (i : Fin 4) :
    starReward oneOwn other ⟨{i}, Finset.singleton_nonempty i⟩ i = 1 := by
  unfold starReward
  rw [rewardWithSingletonMatrix_singleton]
  fin_cases i <;> norm_num [oneOwn,
    QuittingLCPClassification.SignedFourCycleMatrixFixtures.gammaStar]

theorem dagger_own_singletons (other) (i : Fin 4) :
    daggerReward oneOwn other ⟨{i}, Finset.singleton_nonempty i⟩ i = 1 := by
  unfold daggerReward
  rw [rewardWithSingletonMatrix_singleton]
  fin_cases i <;> norm_num [oneOwn,
    QuittingLCPClassification.SignedFourCycleMatrixFixtures.gammaDagger]

theorem doubleDagger_own_singletons (other) (i : Fin 4) :
    doubleDaggerReward oneOwn other
        ⟨{i}, Finset.singleton_nonempty i⟩ i = 1 := by
  unfold doubleDaggerReward
  rw [rewardWithSingletonMatrix_singleton]
  fin_cases i <;> norm_num [oneOwn,
    QuittingLCPClassification.SignedFourCycleMatrixFixtures.gammaDoubleDagger]

theorem star_coarse_values (other) :
    (starData oneOwn other).coarseValue (starStrictTests oneOwn other) =
      ![![1, 4, 2, 1], ![1, 1, 4, 2], ![2, 1, 1, 4], ![4, 2, 1, 1]] := by
  funext phase who
  fin_cases phase <;> fin_cases who <;>
    norm_num [SignedFourCycleSingletonData.coarseValue,
      SignedFourCycleSingletonData.targetValue,
      SignedFourCycleSingletonData.afterZeroValue,
      SignedFourCycleSingletonData.afterOneValue,
      SignedFourCycleSingletonData.afterTwoValue,
      quittingSoloReward,
      starReward, rewardWithSingletonMatrix, oneOwn, starStrictTests, starData,
      SignedFourCycleSingletonData.StrictTests.weights,
      Math.SignedFourCycleStrictData.normalizedWeightZero,
      Math.SignedFourCycleStrictData.normalizedWeightOne,
      Math.SignedFourCycleStrictData.normalizedWeightTwo,
      Math.SignedFourCycleStrictData.normalizedWeightThree,
      Math.SignedFourCycleStrictData.rawWeightSum,
      Math.SignedFourCycleStrictData.tailOne,
      Math.SignedFourCycleStrictData.tailTwo,
      Math.SignedFourCycleStrictData.tailThree,
      SignedFourCycleSingletonData.coefficients,
      Math.SignedFourCycleCoefficients.discriminant,
      Math.SignedFourCycleCoefficients.smallerEigenvalue,
      Math.SignedFourCycleCoefficients.upperLeft,
      Math.SignedFourCycleCoefficients.upperRight,
      Math.SignedFourCycleCoefficients.lowerLeft,
      Math.SignedFourCycleCoefficients.lowerRight,
      Math.SignedFourCycleCoefficients.rawWeightZero,
      Math.SignedFourCycleCoefficients.rawWeightOne,
      Math.SignedFourCycleCoefficients.rawWeightTwo,
      Math.SignedFourCycleCoefficients.rawWeightThree,
      Math.SignedFourCycleCoefficients.periodSurvival,
      QuittingLCPClassification.SignedFourCycleMatrixFixtures.gammaStar,
      Matrix.cons_val_two, Matrix.cons_val_three]

theorem dagger_coarse_values (other) :
    (daggerData oneOwn other).coarseValue (daggerStrictTests oneOwn other) =
      ![![1, 4, 2, 1], ![1, 1, 4, 2], ![2, 1, 1, 4], ![39 / 10, 2, 1, 1]] := by
  funext phase who
  fin_cases phase <;> fin_cases who <;>
    norm_num [SignedFourCycleSingletonData.coarseValue,
      SignedFourCycleSingletonData.targetValue,
      SignedFourCycleSingletonData.afterZeroValue,
      SignedFourCycleSingletonData.afterOneValue,
      SignedFourCycleSingletonData.afterTwoValue, quittingSoloReward,
      daggerReward, rewardWithSingletonMatrix, oneOwn, daggerStrictTests, daggerData,
      SignedFourCycleSingletonData.StrictTests.weights,
      Math.SignedFourCycleStrictData.normalizedWeightZero,
      Math.SignedFourCycleStrictData.normalizedWeightOne,
      Math.SignedFourCycleStrictData.normalizedWeightTwo,
      Math.SignedFourCycleStrictData.normalizedWeightThree,
      Math.SignedFourCycleStrictData.rawWeightSum,
      Math.SignedFourCycleStrictData.tailOne, Math.SignedFourCycleStrictData.tailTwo,
      Math.SignedFourCycleStrictData.tailThree,
      SignedFourCycleSingletonData.coefficients,
      Math.SignedFourCycleCoefficients.discriminant,
      Math.SignedFourCycleCoefficients.smallerEigenvalue,
      Math.SignedFourCycleCoefficients.upperLeft,
      Math.SignedFourCycleCoefficients.upperRight,
      Math.SignedFourCycleCoefficients.lowerLeft,
      Math.SignedFourCycleCoefficients.lowerRight,
      Math.SignedFourCycleCoefficients.rawWeightZero,
      Math.SignedFourCycleCoefficients.rawWeightOne,
      Math.SignedFourCycleCoefficients.rawWeightTwo,
      Math.SignedFourCycleCoefficients.rawWeightThree,
      Math.SignedFourCycleCoefficients.periodSurvival,
      QuittingLCPClassification.SignedFourCycleMatrixFixtures.gammaDagger,
      Matrix.cons_val_two, Matrix.cons_val_three]

theorem doubleDagger_coarse_values (other) :
    (doubleDaggerData oneOwn other).coarseValue
        (doubleDaggerStrictTests oneOwn other) =
      ![![1, 4, 2, 1], ![1, 1, 3, 3 / 2], ![2, 1, 1, 3], ![4, 2, 1, 1]] := by
  funext phase who
  fin_cases phase <;> fin_cases who <;>
    norm_num [SignedFourCycleSingletonData.coarseValue,
      SignedFourCycleSingletonData.targetValue,
      SignedFourCycleSingletonData.afterZeroValue,
      SignedFourCycleSingletonData.afterOneValue,
      SignedFourCycleSingletonData.afterTwoValue, quittingSoloReward,
      doubleDaggerReward, rewardWithSingletonMatrix, oneOwn,
      doubleDaggerStrictTests, doubleDaggerData,
      SignedFourCycleSingletonData.StrictTests.weights,
      Math.SignedFourCycleStrictData.normalizedWeightZero,
      Math.SignedFourCycleStrictData.normalizedWeightOne,
      Math.SignedFourCycleStrictData.normalizedWeightTwo,
      Math.SignedFourCycleStrictData.normalizedWeightThree,
      Math.SignedFourCycleStrictData.rawWeightSum,
      Math.SignedFourCycleStrictData.tailOne, Math.SignedFourCycleStrictData.tailTwo,
      Math.SignedFourCycleStrictData.tailThree,
      SignedFourCycleSingletonData.coefficients,
      Math.SignedFourCycleCoefficients.discriminant,
      Math.SignedFourCycleCoefficients.smallerEigenvalue,
      Math.SignedFourCycleCoefficients.upperLeft,
      Math.SignedFourCycleCoefficients.upperRight,
      Math.SignedFourCycleCoefficients.lowerLeft,
      Math.SignedFourCycleCoefficients.lowerRight,
      Math.SignedFourCycleCoefficients.rawWeightZero,
      Math.SignedFourCycleCoefficients.rawWeightOne,
      Math.SignedFourCycleCoefficients.rawWeightTwo,
      Math.SignedFourCycleCoefficients.rawWeightThree,
      Math.SignedFourCycleCoefficients.periodSurvival,
      QuittingLCPClassification.SignedFourCycleMatrixFixtures.gammaDoubleDagger,
      Matrix.cons_val_two, Matrix.cons_val_three]

theorem star_largerEigenvalue_rawWeightOne (other) :
    (starData oneOwn other).coefficients.upperLeft - 81 = -26 := by
  norm_num [starData, SignedFourCycleSingletonData.coefficients,
    Math.SignedFourCycleCoefficients.upperLeft,
    Math.SignedFourCycleCoefficients.lowerLeft]

end GameTheory.SignedFourCycleValueFixtures
