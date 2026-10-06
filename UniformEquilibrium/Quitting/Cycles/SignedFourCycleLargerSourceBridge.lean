import MathUE.SignedFourCycleLargerOpenness
import UniformEquilibrium.Quitting.Cycles.SignedFourCycleLargerRewardAdapter

noncomputable section

namespace GameTheory

open QuittingLCPClassification

/-- Only polynomial inequalities in the literal reward coordinates are inputs. -/
def HasLargerSignedFourCycleSingletonTable
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)) : Prop :=
  Math.HasSignedFourCycleLargerTests (quittingSingletonMatrix reward)

theorem isOpen_hasLargerSignedFourCycleSingletonTable :
    IsOpen {reward | HasLargerSignedFourCycleSingletonTable reward} := by
  have hmatrix : Continuous (fun reward : {S : Finset (Fin 4) // S.Nonempty} →
      Payoff (Fin 4) => quittingSingletonMatrix reward) := by
    unfold quittingSingletonMatrix
    fun_prop
  exact Math.isOpen_hasSignedFourCycleLargerTests.preimage hmatrix

namespace SignedFourCycleSingletonData

variable {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}

/-- Canonical actual source: no weights, eigenvector or strategic witness are supplied. -/
def ofSingletonMatrixLargerTests (htests : HasLargerSignedFourCycleSingletonTable reward) :
    SignedFourCycleSingletonData reward where
  b player := -quittingSingletonMatrix reward player (player + 1)
  g player := quittingSingletonMatrix reward player (player + 2)
  h player := quittingSingletonMatrix reward player (player + 3)
  b_pos player := neg_pos.mpr (htests.1 player)
  h_pos player := htests.2.1 player
  successor := by intro player; simp
  opposite := by intro player; rfl
  predecessor := by intro player; rfl

theorem ofSingletonMatrixLargerTests_coefficients
    (htests : HasLargerSignedFourCycleSingletonTable reward) :
    (ofSingletonMatrixLargerTests htests).coefficients =
      Math.signedFourCycleCoefficientsOfMatrix (quittingSingletonMatrix reward) := rfl

theorem ofSingletonMatrixLargerTests_largerTests
    (htests : HasLargerSignedFourCycleSingletonTable reward) :
    (ofSingletonMatrixLargerTests htests).LargerTests := by
  rcases htests with ⟨hsuccessor, _, hzero, hone, htwo, hthree, hgap, hdet⟩
  refine ⟨hzero, hone, htwo, hthree, ?_, hdet⟩
  change 1 < (Math.signedFourCycleCoefficientsOfMatrix
    (quittingSingletonMatrix reward)).lowerRight
  exact (Math.lowerRight_gt_one_iff_largerDGap_pos
    (by simpa using hsuccessor 0) (by simpa using hsuccessor 1)
    (by simpa using hsuccessor 2)).mpr hgap

end SignedFourCycleSingletonData
end GameTheory
