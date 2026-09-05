import UniformEquilibrium.Quitting.Cycles.SignedFourCycleRewardAdapter
import UniformEquilibrium.Diagnostics.Quitting.SignedFourCycleMatrixFixtures

noncomputable section

namespace GameTheory.SignedFourCycleRawSpectralFixtures

open QuittingLCPClassification
open QuittingLCPClassification.SignedFourCycleMatrixFixtures

def rewardWithSingletonMatrix (M : Matrix (Fin 4) (Fin 4) ℝ)
    (own : Fin 4 → ℝ)
    (other : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (S : {S : Finset (Fin 4) // S.Nonempty}) : Payoff (Fin 4) :=
  if S.1.card = 1 then fun i ↦ own i + M i (S.1.min' S.2)
  else other S

def starReward := rewardWithSingletonMatrix gammaStar
def daggerReward := rewardWithSingletonMatrix gammaDagger
def doubleDaggerReward := rewardWithSingletonMatrix gammaDoubleDagger

theorem quittingSingletonMatrix_starReward (own) (other) :
    quittingSingletonMatrix (starReward own other) = gammaStar := by
  funext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [quittingSingletonMatrix, starReward, rewardWithSingletonMatrix,
      gammaStar, Matrix.cons_val_two, Matrix.cons_val_three, Fin.add_def]

theorem quittingSingletonMatrix_daggerReward (own) (other) :
    quittingSingletonMatrix (daggerReward own other) = gammaDagger := by
  funext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [quittingSingletonMatrix, daggerReward, rewardWithSingletonMatrix,
      gammaDagger, Matrix.cons_val_two, Matrix.cons_val_three, Fin.add_def]

theorem quittingSingletonMatrix_doubleDaggerReward (own) (other) :
    quittingSingletonMatrix (doubleDaggerReward own other) = gammaDoubleDagger := by
  funext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [quittingSingletonMatrix, doubleDaggerReward, rewardWithSingletonMatrix,
      gammaDoubleDagger, Matrix.cons_val_two, Matrix.cons_val_three, Fin.add_def]

def starData (own) (other) : SignedFourCycleSingletonData (starReward own other) where
  b := fun _ ↦ 1
  g := fun _ ↦ -1
  h := fun _ ↦ 6
  b_pos := by norm_num
  h_pos := by norm_num
  successor := by
    intro i
    rw [quittingSingletonMatrix_starReward]
    fin_cases i <;> simp [gammaStar, Fin.add_def, Matrix.cons_val_two,
      Matrix.cons_val_three]
  opposite := by
    intro i
    rw [quittingSingletonMatrix_starReward]
    fin_cases i <;> simp [gammaStar, Fin.add_def, Matrix.cons_val_two,
      Matrix.cons_val_three]
  predecessor := by
    intro i
    rw [quittingSingletonMatrix_starReward]
    fin_cases i <;> simp [gammaStar, Fin.add_def, Matrix.cons_val_two,
      Matrix.cons_val_three]

def daggerData (own) (other) : SignedFourCycleSingletonData (daggerReward own other) where
  b := fun _ ↦ 1
  g := ![-9 / 10, -1, -1, -1]
  h := ![29 / 5, 6, 6, 6]
  b_pos := by norm_num
  h_pos := by intro i; fin_cases i <;> norm_num
  successor := by
    intro i
    rw [quittingSingletonMatrix_daggerReward]
    fin_cases i <;> norm_num [gammaDagger, Fin.add_def, Matrix.cons_val_two,
      Matrix.cons_val_three]
  opposite := by
    intro i
    rw [quittingSingletonMatrix_daggerReward]
    fin_cases i <;> norm_num [gammaDagger, Fin.add_def, Matrix.cons_val_two,
      Matrix.cons_val_three]
  predecessor := by
    intro i
    rw [quittingSingletonMatrix_daggerReward]
    fin_cases i <;> norm_num [gammaDagger, Fin.add_def, Matrix.cons_val_two,
      Matrix.cons_val_three]

def doubleDaggerData (own) (other) :
    SignedFourCycleSingletonData (doubleDaggerReward own other) where
  b := fun _ ↦ 1
  g := fun _ ↦ -1
  h := ![6, 9, 4, 4]
  b_pos := by norm_num
  h_pos := by intro i; fin_cases i <;> norm_num
  successor := by
    intro i
    rw [quittingSingletonMatrix_doubleDaggerReward]
    fin_cases i <;> norm_num [gammaDoubleDagger, Fin.add_def, Matrix.cons_val_two,
      Matrix.cons_val_three]
  opposite := by
    intro i
    rw [quittingSingletonMatrix_doubleDaggerReward]
    fin_cases i <;> norm_num [gammaDoubleDagger, Fin.add_def, Matrix.cons_val_two,
      Matrix.cons_val_three]
  predecessor := by
    intro i
    rw [quittingSingletonMatrix_doubleDaggerReward]
    fin_cases i <;> norm_num [gammaDoubleDagger, Fin.add_def, Matrix.cons_val_two,
      Matrix.cons_val_three]

theorem starStrictTests (own) (other) : (starData own other).StrictTests := by
  constructor <;>
    norm_num [starData, SignedFourCycleSingletonData.coefficients,
      Math.SignedFourCycleCoefficients.discriminant,
      Math.SignedFourCycleCoefficients.smallerEigenvalue,
      Math.SignedFourCycleCoefficients.upperLeft,
      Math.SignedFourCycleCoefficients.upperRight,
      Math.SignedFourCycleCoefficients.lowerLeft,
      Math.SignedFourCycleCoefficients.lowerRight,
      Math.SignedFourCycleCoefficients.rawWeightOne,
      Math.SignedFourCycleCoefficients.rawWeightTwo,
      Math.SignedFourCycleCoefficients.rawWeightThree,
      Math.SignedFourCycleCoefficients.rawWeightZero,
      Math.SignedFourCycleCoefficients.periodSurvival,
      Matrix.cons_val_two, Matrix.cons_val_three]

theorem daggerStrictTests (own) (other) : (daggerData own other).StrictTests := by
  constructor <;>
    norm_num [daggerData, SignedFourCycleSingletonData.coefficients,
      Math.SignedFourCycleCoefficients.discriminant,
      Math.SignedFourCycleCoefficients.smallerEigenvalue,
      Math.SignedFourCycleCoefficients.upperLeft,
      Math.SignedFourCycleCoefficients.upperRight,
      Math.SignedFourCycleCoefficients.lowerLeft,
      Math.SignedFourCycleCoefficients.lowerRight,
      Math.SignedFourCycleCoefficients.rawWeightOne,
      Math.SignedFourCycleCoefficients.rawWeightTwo,
      Math.SignedFourCycleCoefficients.rawWeightThree,
      Math.SignedFourCycleCoefficients.rawWeightZero,
      Math.SignedFourCycleCoefficients.periodSurvival,
      Matrix.cons_val_two, Matrix.cons_val_three]

theorem doubleDaggerStrictTests (own) (other) :
    (doubleDaggerData own other).StrictTests := by
  constructor <;>
    norm_num [doubleDaggerData, SignedFourCycleSingletonData.coefficients,
      Math.SignedFourCycleCoefficients.discriminant,
      Math.SignedFourCycleCoefficients.smallerEigenvalue,
      Math.SignedFourCycleCoefficients.upperLeft,
      Math.SignedFourCycleCoefficients.upperRight,
      Math.SignedFourCycleCoefficients.lowerLeft,
      Math.SignedFourCycleCoefficients.lowerRight,
      Math.SignedFourCycleCoefficients.rawWeightOne,
      Math.SignedFourCycleCoefficients.rawWeightTwo,
      Math.SignedFourCycleCoefficients.rawWeightThree,
      Math.SignedFourCycleCoefficients.rawWeightZero,
      Math.SignedFourCycleCoefficients.periodSurvival,
      Matrix.cons_val_two, Matrix.cons_val_three]

theorem star_exact_spectral_data (own) (other) :
    let c := (starData own other).coefficients
    c.discriminant = 4225 ∧ c.smallerEigenvalue = 16 ∧
      c.periodSurvival = 1 / 16 ∧ c.rawWeightZero = 78 ∧
      c.rawWeightOne = 39 ∧ c.rawWeightTwo = 39 / 2 ∧
      c.rawWeightThree = 39 / 4 := by
  norm_num [starData, SignedFourCycleSingletonData.coefficients,
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
    Math.SignedFourCycleCoefficients.periodSurvival]

theorem dagger_exact_spectral_data (own) (other) :
    let c := (daggerData own other).coefficients
    c.discriminant = 388129 / 100 ∧ c.smallerEigenvalue = 16 ∧
      c.periodSurvival = 1 / 16 ∧ c.rawWeightZero = 381 / 5 ∧
      c.rawWeightOne = 381 / 10 ∧ c.rawWeightTwo = 381 / 20 ∧
      c.rawWeightThree = 381 / 40 := by
  norm_num [daggerData, SignedFourCycleSingletonData.coefficients,
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
    Matrix.cons_val_two, Matrix.cons_val_three]

theorem doubleDagger_exact_spectral_data (own) (other) :
    let c := (doubleDaggerData own other).coefficients
    c.discriminant = 3600 ∧ c.smallerEigenvalue = 12 ∧
      c.periodSurvival = 1 / 12 ∧ c.rawWeightZero = 44 ∧
      c.rawWeightOne = 44 ∧ c.rawWeightTwo = 22 ∧ c.rawWeightThree = 11 := by
  norm_num [doubleDaggerData, SignedFourCycleSingletonData.coefficients,
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
    Matrix.cons_val_two, Matrix.cons_val_three]

theorem star_normalized_hazards (own) (other) :
    let weights := (starStrictTests own other).weights
    weights.hazardZero = 1 / 2 ∧ weights.hazardOne = 1 / 2 ∧
      weights.hazardTwo = 1 / 2 ∧ weights.hazardThree = 1 / 2 := by
  norm_num [SignedFourCycleSingletonData.StrictTests.weights, starStrictTests,
    starData, SignedFourCycleSingletonData.coefficients,
    Math.SignedFourCycleStrictData.hazardZero,
    Math.SignedFourCycleStrictData.hazardOne,
    Math.SignedFourCycleStrictData.hazardTwo,
    Math.SignedFourCycleStrictData.hazardThree,
    Math.SignedFourCycleStrictData.normalizedWeightZero,
    Math.SignedFourCycleStrictData.normalizedWeightOne,
    Math.SignedFourCycleStrictData.normalizedWeightTwo,
    Math.SignedFourCycleStrictData.normalizedWeightThree,
    Math.SignedFourCycleStrictData.rawWeightSum,
    Math.SignedFourCycleStrictData.tailZero, Math.SignedFourCycleStrictData.tailOne,
    Math.SignedFourCycleStrictData.tailTwo, Math.SignedFourCycleStrictData.tailThree,
    Math.SignedFourCycleCoefficients,
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
    Matrix.cons_val_two, Matrix.cons_val_three]

theorem dagger_normalized_hazards (own) (other) :
    let weights := (daggerStrictTests own other).weights
    weights.hazardZero = 1 / 2 ∧ weights.hazardOne = 1 / 2 ∧
      weights.hazardTwo = 1 / 2 ∧ weights.hazardThree = 1 / 2 := by
  norm_num [SignedFourCycleSingletonData.StrictTests.weights, daggerStrictTests,
    daggerData, SignedFourCycleSingletonData.coefficients,
    Math.SignedFourCycleStrictData.hazardZero,
    Math.SignedFourCycleStrictData.hazardOne,
    Math.SignedFourCycleStrictData.hazardTwo,
    Math.SignedFourCycleStrictData.hazardThree,
    Math.SignedFourCycleStrictData.normalizedWeightZero,
    Math.SignedFourCycleStrictData.normalizedWeightOne,
    Math.SignedFourCycleStrictData.normalizedWeightTwo,
    Math.SignedFourCycleStrictData.normalizedWeightThree,
    Math.SignedFourCycleStrictData.rawWeightSum,
    Math.SignedFourCycleStrictData.tailZero, Math.SignedFourCycleStrictData.tailOne,
    Math.SignedFourCycleStrictData.tailTwo, Math.SignedFourCycleStrictData.tailThree,
    Math.SignedFourCycleCoefficients,
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
    Matrix.cons_val_two, Matrix.cons_val_three]

theorem doubleDagger_normalized_hazards (own) (other) :
    let weights := (doubleDaggerStrictTests own other).weights
    weights.hazardZero = 1 / 3 ∧ weights.hazardOne = 1 / 2 ∧
      weights.hazardTwo = 1 / 2 ∧ weights.hazardThree = 1 / 2 := by
  norm_num [SignedFourCycleSingletonData.StrictTests.weights,
    doubleDaggerStrictTests, doubleDaggerData,
    SignedFourCycleSingletonData.coefficients,
    Math.SignedFourCycleStrictData.hazardZero,
    Math.SignedFourCycleStrictData.hazardOne,
    Math.SignedFourCycleStrictData.hazardTwo,
    Math.SignedFourCycleStrictData.hazardThree,
    Math.SignedFourCycleStrictData.normalizedWeightZero,
    Math.SignedFourCycleStrictData.normalizedWeightOne,
    Math.SignedFourCycleStrictData.normalizedWeightTwo,
    Math.SignedFourCycleStrictData.normalizedWeightThree,
    Math.SignedFourCycleStrictData.rawWeightSum,
    Math.SignedFourCycleStrictData.tailZero, Math.SignedFourCycleStrictData.tailOne,
    Math.SignedFourCycleStrictData.tailTwo, Math.SignedFourCycleStrictData.tailThree,
    Math.SignedFourCycleCoefficients,
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
    Matrix.cons_val_two, Matrix.cons_val_three]

end GameTheory.SignedFourCycleRawSpectralFixtures
