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

/-- A constant-last-coordinate face has the spatial determinant multiplied
by its signed apex displacement. The coordinate order is spatial, then parameter. -/
theorem facetDeterminant_eq_lastCoordinate_displacement
    {n : ℕ} {R : Type*} [CommRing R]
    (face : Fin (n + 1) → Fin (n + 1) → R) (apex : Fin (n + 1) → R)
    (parameter : R) (hface : ∀ vertex, face vertex (Fin.last n) = parameter) :
    facetDeterminant face apex = (-1) ^ (n + 1) *
      (apex (Fin.last n) - parameter) * determinant (fun vertex => Fin.init (face vertex)) := by
  let matrix : Matrix (Fin (n + 2)) (Fin (n + 2)) R :=
    fun vertex => Fin.cons 1
      ((Fin.cons apex face : Fin (n + 2) → Fin (n + 1) → R) vertex)
  let shifted := matrix.updateCol (Fin.last (n + 1))
    (fun vertex => matrix vertex (Fin.last (n + 1)) + (-parameter) • matrix vertex 0)
  have hlast : (Fin.last (n + 1) : Fin (n + 2)) ≠ 0 := by
    intro h
    have hval := congrArg Fin.val h
    simp at hval
  have hdet : shifted.det = matrix.det :=
    Matrix.det_updateCol_add_smul_self matrix hlast (-parameter)
  have hzero : shifted 0 (Fin.last (n + 1)) = apex (Fin.last n) - parameter := by
    simp [shifted, matrix, sub_eq_add_neg]
  have hsucc (vertex : Fin (n + 1)) : shifted vertex.succ (Fin.last (n + 1)) = 0 := by
    simp [shifted, matrix, hface]
  have hminor : shifted.submatrix (0 : Fin (n + 2)).succAbove
      (Fin.last (n + 1)).succAbove =
      (fun vertex => Fin.cons (1 : R) (Fin.init (face vertex))) := by
    ext vertex coordinate
    simp only [Matrix.submatrix_apply, Fin.succAbove_zero, Fin.succAbove_last]
    have hne : coordinate.castSucc ≠ Fin.last (n + 1) := Fin.castSucc_ne_last coordinate
    simp only [shifted, Matrix.updateCol_ne hne]
    induction coordinate using Fin.cases with
    | zero => simp [matrix]
    | succ coordinate => simp [matrix, Fin.init]
  change matrix.det = _
  rw [← hdet, Matrix.det_succ_column shifted (Fin.last (n + 1)), Fin.sum_univ_succ]
  simp only [hzero, hsucc, mul_zero, zero_mul, Finset.sum_const_zero, add_zero,
    Fin.val_zero, Fin.val_last, zero_add, hminor]
  rfl

end Math.OrientedSimplexFacet
