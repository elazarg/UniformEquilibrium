import Mathlib.LinearAlgebra.Matrix.Transvection
import Mathlib.Topology.Instances.Matrix
import Mathlib.Topology.Path

/-!
# Determinant-preserving paths to diagonal matrices

The existing Gaussian-elimination factorization writes a matrix as a diagonal
matrix between two finite products of transvections. Scaling all transvection
coefficients to zero gives a continuous path with constant determinant.
The construction also applies to singular matrices and to the empty index type.
No local-degree comparison is asserted here.
-/

noncomputable section

namespace Math.LinearAlgebra

open Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Scale each coefficient of a finite transvection product from its original
value at parameter zero to zero at parameter one. -/
def transvectionProductDeformation (factors : List (TransvectionStruct ι ℝ))
    (parameter : ℝ) : Matrix ι ι ℝ :=
  (factors.map fun factor =>
    transvection factor.i factor.j ((1 - parameter) * factor.c)).prod

@[simp] theorem transvectionProductDeformation_zero
    (factors : List (TransvectionStruct ι ℝ)) :
    transvectionProductDeformation factors 0 =
      (factors.map TransvectionStruct.toMatrix).prod := by
  simp only [transvectionProductDeformation, sub_zero, one_mul]
  rfl

@[simp] theorem transvectionProductDeformation_one
    (factors : List (TransvectionStruct ι ℝ)) :
    transvectionProductDeformation factors 1 = 1 := by
  simp [transvectionProductDeformation]

/-- The displayed finite product is continuous for every real parameter. -/
theorem continuous_transvectionProductDeformation
    (factors : List (TransvectionStruct ι ℝ)) :
    Continuous (transvectionProductDeformation factors) := by
  apply continuous_list_prod factors
  intro factor _
  apply continuous_matrix
  intro i j
  simp only [transvection, Matrix.add_apply, Matrix.single_apply]
  exact continuous_const.add
    (((continuous_const.sub continuous_id).mul continuous_const).if_const _ continuous_const)

/-- Every scaled factor, and hence its product, has determinant one. -/
@[simp] theorem det_transvectionProductDeformation
    (factors : List (TransvectionStruct ι ℝ)) (parameter : ℝ) :
    (transvectionProductDeformation factors parameter).det = 1 := by
  induction factors with
  | nil => simp [transvectionProductDeformation]
  | cons factor factors ih =>
      simp only [transvectionProductDeformation, List.map_cons, List.prod_cons,
        Matrix.det_mul, det_transvection_of_ne _ _ factor.hij, one_mul] at ⊢
      exact ih

/-- Every finite square real matrix admits an actual path to a diagonal
matrix with its determinant fixed throughout. No nonsingularity is required. -/
theorem exists_path_diagonal_det_eq (matrix : Matrix ι ι ℝ) :
    ∃ diagonalEntries : ι → ℝ, ∃ path : Path matrix (diagonal diagonalEntries),
      ∀ parameter, (path parameter).det = matrix.det := by
  obtain ⟨left, right, diagonalEntries, hmatrix⟩ :=
    Matrix.Pivot.exists_list_transvec_mul_diagonal_mul_list_transvec matrix
  let curve : ℝ → Matrix ι ι ℝ := fun parameter =>
    transvectionProductDeformation left parameter * diagonal diagonalEntries *
      transvectionProductDeformation right parameter
  have hcontinuous : Continuous curve :=
    ((continuous_transvectionProductDeformation left).mul continuous_const).mul
      (continuous_transvectionProductDeformation right)
  have hzero : curve 0 = matrix := by
    simpa only [curve, transvectionProductDeformation_zero] using hmatrix.symm
  have hone : curve 1 = diagonal diagonalEntries := by simp [curve]
  let path : Path matrix (diagonal diagonalEntries) :=
    { toFun := fun parameter => curve parameter
      continuous_toFun := hcontinuous.comp continuous_subtype_val
      source' := hzero
      target' := hone }
  refine ⟨diagonalEntries, path, fun parameter => ?_⟩
  have hdet : (diagonal diagonalEntries).det = matrix.det := by
    rw [hmatrix]
    simp
  change (curve parameter).det = matrix.det
  simpa only [curve, Matrix.det_mul, det_transvectionProductDeformation,
    one_mul, mul_one] using hdet

/-- A nonsingular input has a path of nonsingular matrices to a nonsingular
diagonal matrix; this is a corollary of the determinant-preserving construction. -/
theorem exists_path_diagonal_det_ne_zero (matrix : Matrix ι ι ℝ)
    (hnonsingular : matrix.det ≠ 0) :
    ∃ diagonalEntries : ι → ℝ, ∃ path : Path matrix (diagonal diagonalEntries),
      (∀ parameter, (path parameter).det = matrix.det) ∧
        ∀ parameter, (path parameter).det ≠ 0 := by
  obtain ⟨diagonalEntries, path, hdet⟩ := exists_path_diagonal_det_eq matrix
  exact ⟨diagonalEntries, path, hdet, fun parameter => (hdet parameter).trans_ne hnonsingular⟩

end Math.LinearAlgebra
