import MathUE.SignedFourCycleStrictOpenness
import UniformEquilibrium.Quitting.Cycles.SignedFourCycleRewardAdapter

noncomputable section

namespace GameTheory.SignedFourCycleSingletonData

open QuittingLCPClassification

variable {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}

/-- Matrix extraction recovers exactly the coefficients built from the actual reward table. -/
theorem coefficientsOfSingletonMatrix_eq (data : SignedFourCycleSingletonData reward) :
    Math.signedFourCycleCoefficientsOfMatrix (quittingSingletonMatrix reward) =
      data.coefficients := by
  have hs0 : quittingSingletonMatrix reward 0 1 = -data.b 0 := by
    simpa using data.successor 0
  have hs1 : quittingSingletonMatrix reward 1 2 = -data.b 1 := by
    simpa using data.successor 1
  have hs2 : quittingSingletonMatrix reward 2 3 = -data.b 2 := by
    simpa using data.successor 2
  have hs3 : quittingSingletonMatrix reward 3 0 = -data.b 3 := by
    simpa using data.successor 3
  have ho0 : quittingSingletonMatrix reward 0 2 = data.g 0 := by
    simpa using data.opposite 0
  have ho1 : quittingSingletonMatrix reward 1 3 = data.g 1 := by
    simpa using data.opposite 1
  have ho2 : quittingSingletonMatrix reward 2 0 = data.g 2 := by
    simpa using data.opposite 2
  have ho3 : quittingSingletonMatrix reward 3 1 = data.g 3 := by
    simpa using data.opposite 3
  have hp0 : quittingSingletonMatrix reward 0 3 = data.h 0 := by
    simpa using data.predecessor 0
  have hp1 : quittingSingletonMatrix reward 1 0 = data.h 1 := by
    simpa using data.predecessor 1
  have hp2 : quittingSingletonMatrix reward 2 1 = data.h 2 := by
    simpa using data.predecessor 2
  have hp3 : quittingSingletonMatrix reward 3 2 = data.h 3 := by
    simpa using data.predecessor 3
  unfold Math.signedFourCycleCoefficientsOfMatrix coefficients
  congr 1 <;> simp [hs0, hs1, hs2, hs3, ho0, ho1, ho2, ho3,
    hp0, hp1, hp2, hp3]

/-- Actual signed singleton data satisfying `StrictTests` belongs to the open matrix locus. -/
theorem hasStrictTests_singletonMatrix (data : SignedFourCycleSingletonData reward)
    (tests : data.StrictTests) :
    Math.HasSignedFourCycleStrictTests (quittingSingletonMatrix reward) := by
  have hcoeff := data.coefficientsOfSingletonMatrix_eq
  rw [Math.HasSignedFourCycleStrictTests, hcoeff]
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩,
    tests.discriminant_pos, tests.smallerEigenvalue_gt_one, tests.upperRight_neg,
    tests.rawWeightOne_pos, tests.rawWeightTwo_pos, tests.rawWeightThree_pos⟩
  · rw [show quittingSingletonMatrix reward 0 1 = -data.b 0 by
      simpa using data.successor 0]
    exact neg_neg_of_pos (data.b_pos 0)
  · rw [show quittingSingletonMatrix reward 0 3 = data.h 0 by
      simpa using data.predecessor 0]
    exact data.h_pos 0
  · rw [show quittingSingletonMatrix reward 1 2 = -data.b 1 by
      simpa using data.successor 1]
    exact neg_neg_of_pos (data.b_pos 1)
  · rw [show quittingSingletonMatrix reward 1 0 = data.h 1 by
      simpa using data.predecessor 1]
    exact data.h_pos 1
  · rw [show quittingSingletonMatrix reward 2 3 = -data.b 2 by
      simpa using data.successor 2]
    exact neg_neg_of_pos (data.b_pos 2)
  · rw [show quittingSingletonMatrix reward 2 1 = data.h 2 by
      simpa using data.predecessor 2]
    exact data.h_pos 2
  · rw [show quittingSingletonMatrix reward 3 0 = -data.b 3 by
      simpa using data.successor 3]
    exact neg_neg_of_pos (data.b_pos 3)
  · rw [show quittingSingletonMatrix reward 3 2 = data.h 3 by
      simpa using data.predecessor 3]
    exact data.h_pos 3

/-- Build literal signed-cycle source data from an actual singleton matrix in the strict locus. -/
def ofSingletonMatrixStrictTests
    (h : Math.HasSignedFourCycleStrictTests (quittingSingletonMatrix reward)) :
    SignedFourCycleSingletonData reward where
  b i := -quittingSingletonMatrix reward i (i + 1)
  g i := quittingSingletonMatrix reward i (i + 2)
  h i := quittingSingletonMatrix reward i (i + 3)
  b_pos := by
    intro i
    fin_cases i <;> simp only [Fin.add_def] <;>
      exact neg_pos.mpr (by rcases h with ⟨⟨h01, -⟩, ⟨h12, -⟩,
        ⟨h23, -⟩, ⟨h30, -⟩, -⟩; assumption)
  h_pos := by
    intro i
    fin_cases i <;> simp only [Fin.add_def] <;>
      rcases h with ⟨⟨-, h03⟩, ⟨-, h10⟩, ⟨-, h21⟩, ⟨-, h32⟩, -⟩ <;>
      assumption
  successor := by intro i; simp
  opposite := by intro i; rfl
  predecessor := by intro i; rfl

/-- The reconstructed actual source carries exactly the strict tests used to construct it. -/
theorem ofSingletonMatrixStrictTests_strictTests
    (h : Math.HasSignedFourCycleStrictTests (quittingSingletonMatrix reward)) :
    (ofSingletonMatrixStrictTests h).StrictTests := by
  have hcoeff := (ofSingletonMatrixStrictTests h).coefficientsOfSingletonMatrix_eq
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rw [← hcoeff]
  · exact h.2.2.2.2.1
  · exact h.2.2.2.2.2.1
  · exact h.2.2.2.2.2.2.1
  · exact h.2.2.2.2.2.2.2.1
  · exact h.2.2.2.2.2.2.2.2.1
  · exact h.2.2.2.2.2.2.2.2.2

end GameTheory.SignedFourCycleSingletonData
