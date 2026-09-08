import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
# Oriented facet determinants

The affine vertex determinant uses homogeneous rows `(1, vertex)`. Moving an
omitted vertex to the first row gives the usual alternating boundary sign.
Two apices reflected across a pair of common face vertices have opposite
facet determinants. Both facts delegate to the existing determinant and
finite-permutation algebra; no chain complex or degree is constructed here.
-/

noncomputable section

namespace Math.OrientedSimplexFacet

variable {n : ℕ} {R : Type*} [CommRing R]

/-- Affine orientation volume, with the supplied vertex and coordinate orders. -/
def determinant (vertices : Fin (n + 1) → (Fin n → R)) : R :=
  Matrix.det (fun vertex => Fin.cons 1 (vertices vertex))

/-- The oriented determinant of a common face with an apex placed first. -/
def facetDeterminant (face : Fin n → (Fin n → R)) (apex : Fin n → R) : R :=
  determinant (Fin.cons apex face)

/-- The inherited ordered face has exactly the alternating deletion coefficient. -/
theorem facetDeterminant_delete
    (vertices : Fin (n + 1) → (Fin n → R)) (omitted : Fin (n + 1)) :
    facetDeterminant (fun kept => vertices (omitted.succAbove kept)) (vertices omitted) =
      (-1) ^ (omitted : ℕ) * determinant vertices := by
  have hmatrix :
      (fun vertex => Fin.cons (1 : R)
        ((Fin.cons (vertices omitted)
          (fun kept => vertices (omitted.succAbove kept)) : Fin (n + 1) → Fin n → R) vertex)) =
      (show Matrix (Fin (n + 1)) (Fin (n + 1)) R from
        fun vertex => Fin.cons (1 : R) (vertices vertex)).submatrix
        omitted.cycleRange.symm id := by
    ext vertex coordinate
    induction vertex using Fin.cases with
    | zero => simp
    | succ kept => simp
  unfold facetDeterminant determinant
  rw [hmatrix, Matrix.det_permute]
  simp

/-- Reflection through the midpoint of two face vertices reverses the actual
oriented facet determinant, without a separate supplied orientation hypothesis. -/
theorem facetDeterminant_add_eq_zero_of_reflection
    (face : Fin n → (Fin n → R)) (first second : Fin n → R)
    (left right : Fin n)
    (hreflection : first + second = face left + face right) :
    facetDeterminant face first + facetDeterminant face second = 0 := by
  let matrix : Matrix (Fin (n + 1)) (Fin (n + 1)) R :=
    fun vertex => Fin.cons 1 ((Fin.cons first face : Fin (n + 1) → Fin n → R) vertex)
  have hrows : Fin.cons (1 : R) first + Fin.cons 1 second =
      matrix left.succ + matrix right.succ := by
    ext coordinate
    induction coordinate using Fin.cases with
    | zero => simp [matrix]
    | succ coordinate => exact congrFun hreflection coordinate
  have hdet := congrArg (fun row => (matrix.updateRow 0 row).det) hrows
  rw [Matrix.det_updateRow_add, Matrix.det_updateRow_add,
    Matrix.det_updateRow_eq_zero (Fin.succ_ne_zero left),
    Matrix.det_updateRow_eq_zero (Fin.succ_ne_zero right), add_zero] at hdet
  have hfirst : matrix.updateRow 0 (Fin.cons 1 first) = matrix := by
    ext vertex coordinate
    induction vertex using Fin.cases with
    | zero => simp [matrix]
    | succ vertex => simp [matrix]
  have hsecond : matrix.updateRow 0 (Fin.cons 1 second) =
      (fun vertex => Fin.cons (1 : R)
        ((Fin.cons second face : Fin (n + 1) → Fin n → R) vertex)) := by
    ext vertex coordinate
    induction vertex using Fin.cases with
    | zero => simp [matrix]
    | succ vertex => simp [matrix]
  rw [hfirst, hsecond] at hdet
  exact hdet

end Math.OrientedSimplexFacet
