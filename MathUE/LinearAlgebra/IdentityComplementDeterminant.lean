import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Logic.Equiv.Set

/-! # Determinants with identity complement rows

Only the complement rows are constrained. Entries from active rows into the
complement remain arbitrary, so this reduction retains full ambient matrices.
-/

namespace Math.Matrix

open Set

theorem det_eq_active_submatrix_of_identity_complement_rows
    {ι R : Type*} [Fintype ι] [DecidableEq ι] [CommRing R]
    (matrix : _root_.Matrix ι ι R) (active : Finset ι)
    (hrows : ∀ row ∉ active, ∀ column,
      matrix row column = if row = column then 1 else 0) :
    matrix.det = (matrix.submatrix
      (fun row : {row // row ∈ active} => row.val)
      (fun column : {column // column ∈ active} => column.val)).det := by
  classical
  let equivalence := Equiv.Set.sumCompl (active : Set ι)
  let upper := matrix.submatrix
    (fun row : (active : Set ι) => row.val)
    (fun column : ↥((active : Set ι)ᶜ) => column.val)
  let principal := matrix.submatrix
    (fun row : (active : Set ι) => row.val)
    (fun column : (active : Set ι) => column.val)
  have hblock : matrix.submatrix equivalence equivalence =
      _root_.Matrix.fromBlocks principal upper 0 1 := by
    ext row column
    rcases row with row | row <;> rcases column with column | column
    · rfl
    · rfl
    · change matrix row.val column.val = 0
      rw [hrows row.val row.property]
      have hne : row.val ≠ column.val := by
        intro heq
        apply row.property
        rw [heq]
        exact column.property
      simp only [hne, ite_false]
    · change matrix row.val column.val =
        (1 : _root_.Matrix ↥((active : Set ι)ᶜ) ↥((active : Set ι)ᶜ) R) row column
      rw [hrows row.val row.property, _root_.Matrix.one_apply]
      simp only [Subtype.ext_iff]
  rw [← _root_.Matrix.det_submatrix_equiv_self equivalence matrix, hblock,
    _root_.Matrix.det_fromBlocks_zero₂₁, _root_.Matrix.det_one, mul_one]
  rfl

end Math.Matrix
