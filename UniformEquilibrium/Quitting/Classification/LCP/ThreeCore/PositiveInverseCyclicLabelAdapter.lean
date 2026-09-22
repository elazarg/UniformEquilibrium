import UniformEquilibrium.Quitting.Classification.LCP.PositiveInverse
import UniformEquilibrium.Quitting.Classification.LCP.ThreeCore.CyclicLabelAdapter

/-! # Cyclic labeling from a strictly positive inverse

This is a hypothesis adapter to the existing three-coordinate classification,
not a second classification proof. No game or equilibrium hypothesis is used.
-/

noncomputable section

namespace GameTheory.ThreeCoreCyclicLabelAdapter

open QuittingLCPClassification
open QuittingLCPClassification.ThreeByThreeZeroDiagonalQ
open Math.LinearProgramming

/-- A zero-diagonal three-coordinate matrix with strictly positive inverse
has the canonical directed-cycle labeling with positive parameters and gap. -/
theorem exists_directedCycle_labeling_of_strictlyPositiveInverse
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (matrix : Matrix ι ι ℝ) (hcard : Fintype.card ι = 3)
    (hdiag : ∀ i, matrix i i = 0)
    (hpositive : HasStrictlyPositiveInverse matrix) :
    ∃ (label : ι ≃ Fin 3) (a b c d e f : ℝ),
      0 < a ∧ 0 < b ∧ 0 < c ∧ 0 < d ∧ 0 < e ∧ 0 < f ∧
      0 < cycleGap a b c d e f ∧
      reindexMatrix label matrix = directedCycleMatrix a b c d e f := by
  apply exists_directedCycle_labeling matrix hcard hdiag
  · exact isStandardQMatrix_of_positive_rightInverse matrix matrix⁻¹
      (Matrix.mul_nonsing_inv matrix (isUnit_iff_ne_zero.mpr hpositive.1))
      hpositive.2
  · exact noHomogeneousSimplexSolution_of_positive_leftInverse matrix matrix⁻¹
      (Matrix.nonsing_inv_mul matrix (isUnit_iff_ne_zero.mpr hpositive.1))
      hpositive.2

end GameTheory.ThreeCoreCyclicLabelAdapter
