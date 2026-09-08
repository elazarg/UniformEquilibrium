import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Data.Fintype.Pigeonhole

/-!
# Integer cancellation for the labeled boundary of one simplex

A square label sequence has the sign of its label permutation, or zero when
labels repeat. Its alternating deletion weights cancel in the integers on
the boundary of a simplex with one more vertex than labels. This is the local
label calculation needed by an oriented simplicial count; it does not supply
geometric cell orientations, interior-face compatibility, or a topological
degree.
-/

noncomputable section

namespace Math.SignedSimplexLabel

open Matrix

/-- Integer label orientation: the determinant of the label incidence matrix. -/
def orientation {n : ℕ} (labels : Fin n → Fin n) : ℤ :=
  Matrix.det (fun vertex label => if labels vertex = label then (1 : ℤ) else 0)

/-- Repeated labels give zero orientation. -/
theorem orientation_eq_zero_of_not_injective {n : ℕ} (labels : Fin n → Fin n)
    (hinjective : ¬ Function.Injective labels) : orientation labels = 0 := by
  obtain ⟨first, second, hequal, hne⟩ := Function.not_injective_iff.mp hinjective
  apply Matrix.det_zero_of_row_eq hne
  funext label
  simp only [hequal]

/-- For a complete label sequence, the determinant is its literal permutation sign. -/
theorem orientation_equiv {n : ℕ} (labels : Equiv.Perm (Fin n)) :
    orientation labels = (Equiv.Perm.sign labels : ℤ) := by
  have hmatrix : (fun vertex label => if labels vertex = label then (1 : ℤ) else 0) =
      (1 : Matrix (Fin n) (Fin n) ℤ).submatrix labels id := by
    ext vertex label
    simp only [Matrix.submatrix_apply, Matrix.one_apply, id_eq]
    rfl
  rw [orientation, hmatrix, Matrix.det_permute, Matrix.det_one, mul_one]
  rfl

/-- Reordering the vertices changes the label orientation by the same permutation sign. -/
theorem orientation_comp_permutation {n : ℕ} (labels : Fin n → Fin n)
    (permutation : Equiv.Perm (Fin n)) :
    orientation (labels ∘ permutation) =
      (Equiv.Perm.sign permutation : ℤ) * orientation labels := by
  exact Matrix.det_permute permutation
    (fun vertex label => if labels vertex = label then (1 : ℤ) else 0)

/-- A complete square label sequence has nonzero integer orientation. -/
theorem orientation_ne_zero_iff {n : ℕ} (labels : Fin n → Fin n) :
    orientation labels ≠ 0 ↔ Function.Injective labels := by
  constructor
  · intro h
    by_contra hn
    exact h (orientation_eq_zero_of_not_injective labels hn)
  · intro hinjective
    let permutation : Equiv.Perm (Fin n) :=
      Equiv.ofBijective labels ((Fintype.bijective_iff_injective_and_card _).mpr
        ⟨hinjective, rfl⟩)
    change orientation permutation ≠ 0
    rw [orientation_equiv]
    exact Units.ne_zero _

/-- The signed coefficient of a deletion face, retaining its inherited order. -/
def deletionWeight {n : ℕ} (labels : Fin (n + 2) → Fin (n + 1))
    (omitted : Fin (n + 2)) : ℤ :=
  (-1) ^ (omitted : ℕ) * orientation (fun kept => labels (omitted.succAbove kept))

theorem deletionWeight_eq_zero_of_not_injective {n : ℕ}
    (labels : Fin (n + 2) → Fin (n + 1)) (omitted : Fin (n + 2))
    (hinjective : ¬ Function.Injective fun kept => labels (omitted.succAbove kept)) :
    deletionWeight labels omitted = 0 := by
  rw [deletionWeight, orientation_eq_zero_of_not_injective _ hinjective, mul_zero]

/-- The integer boundary sum vanishes, not merely its reduction modulo two. -/
theorem sum_deletionWeight_eq_zero {n : ℕ} (labels : Fin (n + 2) → Fin (n + 1)) :
    ∑ omitted, deletionWeight labels omitted = 0 := by
  let augmented : Matrix (Fin (n + 2)) (Fin (n + 2)) ℤ :=
    fun vertex => Fin.cons 1 (fun label => if labels vertex = label then 1 else 0)
  obtain ⟨first, second, hne, hequal⟩ :=
    Fintype.exists_ne_map_eq_of_card_lt labels (by simp)
  have hzero : augmented.det = 0 := by
    apply Matrix.det_zero_of_row_eq hne
    funext label
    simp only [augmented, hequal]
  rw [Matrix.det_succ_column_zero] at hzero
  calc
    _ = ∑ omitted : Fin (n + 2), (-1) ^ (omitted : ℕ) * augmented omitted 0 *
        (augmented.submatrix omitted.succAbove Fin.succ).det := by
      apply Finset.sum_congr rfl
      intro omitted _
      have hminor : augmented.submatrix omitted.succAbove Fin.succ =
          (fun vertex label =>
            if labels (omitted.succAbove vertex) = label then (1 : ℤ) else 0) := by
        ext vertex label
        rfl
      rw [hminor]
      simp only [augmented, Fin.cons_zero, mul_one, deletionWeight, orientation]
    _ = 0 := hzero

/-- Restricting to complete deletion faces leaves the same zero integer sum.
The predicate is exactly injectivity of the retained label sequence. -/
theorem sum_complete_deletionWeight_eq_zero {n : ℕ}
    (labels : Fin (n + 2) → Fin (n + 1)) :
    ∑ omitted ∈ Finset.univ.filter
      (fun omitted => Function.Injective fun kept => labels (omitted.succAbove kept)),
      deletionWeight labels omitted = 0 := by
  classical
  rw [Finset.sum_filter]
  have hsum : (∑ omitted, if Function.Injective
      (fun kept => labels (omitted.succAbove kept)) then deletionWeight labels omitted else 0) =
      ∑ omitted, deletionWeight labels omitted := by
    apply Finset.sum_congr rfl
    intro omitted _
    split_ifs with hinjective
    · rfl
    · exact (deletionWeight_eq_zero_of_not_injective labels omitted hinjective).symm
  rw [hsum, sum_deletionWeight_eq_zero]

end Math.SignedSimplexLabel
