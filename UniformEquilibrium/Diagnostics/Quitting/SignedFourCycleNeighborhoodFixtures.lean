import MathUE.LinearProgramming.TwoRowNegativeShapeNeighborhood
import UniformEquilibrium.Quitting.Cycles.SignedFourCycleStrictSourceBridge
import UniformEquilibrium.Diagnostics.Quitting.SignedFourCycleRawSpectralFixtures

noncomputable section

namespace GameTheory.SignedFourCycleNeighborhoodFixtures

open QuittingLCPClassification
open QuittingLCPClassification.SignedFourCycleMatrixFixtures
open SignedFourCycleRawSpectralFixtures
open Math.LinearProgramming

theorem starSingletonMatrix_mem_strictOpenLocus (own) (other) :
    Math.HasSignedFourCycleStrictTests
      (quittingSingletonMatrix (starReward own other)) :=
  (starData own other).hasStrictTests_singletonMatrix (starStrictTests own other)

theorem daggerSingletonMatrix_mem_strictOpenLocus (own) (other) :
    Math.HasSignedFourCycleStrictTests
      (quittingSingletonMatrix (daggerReward own other)) :=
  (daggerData own other).hasStrictTests_singletonMatrix (daggerStrictTests own other)

theorem doubleDaggerSingletonMatrix_mem_strictOpenLocus (own) (other) :
    Math.HasSignedFourCycleStrictTests
      (quittingSingletonMatrix (doubleDaggerReward own other)) :=
  (doubleDaggerData own other).hasStrictTests_singletonMatrix
    (doubleDaggerStrictTests own other)

def gammaDaggerZeroDiagonal : ZeroDiagonalFourMatrix :=
  ⟨gammaDagger, by
    intro i
    fin_cases i <;> norm_num [gammaDagger]⟩

theorem gammaDagger_mem_twoRowNegativeShapeNeighborhood :
    InTwoRowNegativeShapeNeighborhood gammaDaggerZeroDiagonal := by
  norm_num [InTwoRowNegativeShapeNeighborhood, gammaDaggerZeroDiagonal,
    twoRowNegativeShapeGap, gammaDagger, Matrix.cons_val_two,
    Matrix.cons_val_three]

theorem gammaDagger_not_scaledRelabelingCirculant_from_neighborhood :
    ¬IsPositiveRowScaledRelabelingRowCirculant gammaDagger :=
  inTwoRowNegativeShapeNeighborhood_not_scaledRelabelingCirculant
    gammaDagger_mem_twoRowNegativeShapeNeighborhood

end GameTheory.SignedFourCycleNeighborhoodFixtures
