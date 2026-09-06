import MathUE.LinearProgramming.TwoRowNegativeShapeNeighborhood
import UniformEquilibrium.Diagnostics.Quitting.SignedFourCycleMatrixRegimeOpenness
import UniformEquilibrium.Diagnostics.Quitting.SignedFourCycleNeighborhoodFixtures
import UniformEquilibrium.Quitting.Cycles.SignedFourCycleFiniteEarlyAbsorption

noncomputable section

namespace GameTheory.SignedFourCycleNeighborhood

open QuittingLCPClassification
open QuittingLCPClassification.SignedFourCycleMatrixFixtures
open QuittingLCPClassification.SignedFourCycleMatrixRegimeOpenness
open SignedFourCycleNeighborhoodFixtures SignedFourCycleSingletonData
open SignedFourCycleRawSpectralFixtures
open Math.LinearProgramming

def neighborhood : Set ZeroDiagonalFourMatrix :=
  {M | Math.HasSignedFourCycleStrictTests M.1 ∧ M.1 ∈ openRegime ∧
    InTwoRowNegativeShapeNeighborhood M}

theorem isOpen_neighborhood : IsOpen neighborhood := by
  unfold neighborhood
  exact (Math.isOpen_hasSignedFourCycleStrictTests.preimage continuous_subtype_val).inter
    ((isOpen_openRegime.preimage continuous_subtype_val).inter
      isOpen_inTwoRowNegativeShapeNeighborhood)

theorem gammaDagger_mem_neighborhood : gammaDaggerZeroDiagonal ∈ neighborhood := by
  refine ⟨?_, gammaDagger_mem_openRegime,
    gammaDagger_mem_twoRowNegativeShapeNeighborhood⟩
  have h := daggerSingletonMatrix_mem_strictOpenLocus
    (fun _ : Fin 4 ↦ 0) (fun _ _ ↦ 0)
  convert h using 1
  ext i j
  simpa [gammaDaggerZeroDiagonal] using
    congrFun (congrFun (quittingSingletonMatrix_daggerReward
      (fun _ : Fin 4 ↦ 0) (fun _ _ ↦ 0)).symm i) j

theorem actualReward_uniformPayoff_and_finiteEarlyAbsorption
    (M : ZeroDiagonalFourMatrix) (hM : M ∈ neighborhood)
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (hmatrix : quittingSingletonMatrix reward = M.1) :
    ∃ hstrict : Math.HasSignedFourCycleStrictTests
        (quittingSingletonMatrix reward),
      let data := ofSingletonMatrixStrictTests hstrict
      let tests := ofSingletonMatrixStrictTests_strictTests hstrict
      (quittingGame reward).IsUniformEquilibriumPayoff none
          (data.targetValue tests) ∧
        HasQuittingFiniteMenuFullEarlyAbsorption reward := by
  have hstrict : Math.HasSignedFourCycleStrictTests
      (quittingSingletonMatrix reward) := by
    rw [hmatrix]
    exact hM.1
  refine ⟨hstrict, ?_⟩
  exact ⟨(ofSingletonMatrixStrictTests hstrict).targetValue_isUniformEquilibriumPayoff
      (ofSingletonMatrixStrictTests_strictTests hstrict),
    (ofSingletonMatrixStrictTests hstrict).hasFiniteMenuFullEarlyAbsorption
      (ofSingletonMatrixStrictTests_strictTests hstrict)⟩

/-- Around the heterogeneous fixture, every comparison matrix retains the
strict raw producer, its matrix classification, and genuine noncyclicity;
every actual reward table over that matrix has the computed fixed target and
the unrestricted finite early-absorption source. -/
theorem exists_relative_open_uniformPayoff_neighborhood :
    ∃ U : Set ZeroDiagonalFourMatrix, IsOpen U ∧
      gammaDaggerZeroDiagonal ∈ U ∧
      ∀ M ∈ U,
        Math.HasSignedFourCycleStrictTests M.1 ∧
        normalCore M.1 = Finset.univ ∧ IsStandardQMatrix M.1 ∧
        ¬HasHomogeneousSimplexSolution M.1 ∧ ¬IsProjectiveQBarMatrix M.1 ∧
        ¬IsPositiveRowScaledRelabelingRowCirculant M.1 ∧
        ∀ reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4),
          quittingSingletonMatrix reward = M.1 →
          ∃ hstrict : Math.HasSignedFourCycleStrictTests
              (quittingSingletonMatrix reward),
            let data := ofSingletonMatrixStrictTests hstrict
            let tests := ofSingletonMatrixStrictTests_strictTests hstrict
            (quittingGame reward).IsUniformEquilibriumPayoff none
                (data.targetValue tests) ∧
              HasQuittingFiniteMenuFullEarlyAbsorption reward := by
  refine ⟨neighborhood, isOpen_neighborhood, gammaDagger_mem_neighborhood, ?_⟩
  intro M hM
  have hclassification := openRegime_classification M.1 hM.2.1 M.2
  exact ⟨hM.1, hclassification.1, hclassification.2.1,
    hclassification.2.2.1, hclassification.2.2.2,
    inTwoRowNegativeShapeNeighborhood_not_scaledRelabelingCirculant hM.2.2,
    fun reward hmatrix ↦ actualReward_uniformPayoff_and_finiteEarlyAbsorption
      M hM reward hmatrix⟩

end GameTheory.SignedFourCycleNeighborhood
