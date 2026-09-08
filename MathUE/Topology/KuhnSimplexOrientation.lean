import MathUE.Topology.KuhnSimplexGeometry
import MathUE.Topology.OrientedSimplexFacetDeterminant

/-!
# Unit lattice determinants of actual ordered Kuhn simplices

The actual unit coordinate steps form a permutation: every coordinate must
occur because the last vertex exceeds the first in every coordinate. Existing
determinant row operations turn the homogeneous vertex matrix into that
permutation matrix. Thus the literal integer determinant is a permutation
sign and has absolute value one, including dimension zero.
-/

noncomputable section

namespace Math.KuhnSimplex

open OrientedSimplexFacet

/-- Unit coordinate increments have the sign of their chronological axis
permutation over any commutative ring. The determinant algebra is the existing
successive-row operation and permutation formula. -/
theorem determinant_eq_sign_of_unitCoordinatePermutation
    {n : ℕ} {R : Type*} [CommRing R]
    (vertices : Fin (n + 1) → Fin n → R) (permutation : Equiv.Perm (Fin n))
    (hstep : ∀ step coordinate, vertices step.succ coordinate =
      vertices step.castSucc coordinate + if coordinate = permutation step then 1 else 0) :
    determinant vertices = ((Equiv.Perm.sign permutation : ℤ) : R) := by
  let original : Matrix (Fin (n + 1)) (Fin (n + 1)) R :=
    fun vertex => Fin.cons 1 (vertices vertex)
  let delta : Matrix (Fin n) (Fin n) R :=
    fun step coordinate => if permutation step = coordinate then 1 else 0
  let reduced : Matrix (Fin (n + 1)) (Fin (n + 1)) R :=
    Fin.cons (Fin.cons 1 (vertices 0)) (fun step => Fin.cons 0 (delta step))
  have hrow : original.det = reduced.det :=
    Matrix.det_eq_of_forall_row_eq_smul_add_pred (fun _ => 1)
      (fun _ => rfl) (by
        intro step coordinate
        induction coordinate using Fin.cases with
        | zero => simp [original, reduced]
        | succ coordinate =>
          simpa [original, reduced, delta, eq_comm, add_comm] using hstep step coordinate)
  have hdelta : delta = (1 : Matrix (Fin n) (Fin n) R).submatrix permutation id := by
    ext step coordinate
    simp only [delta, Matrix.submatrix_apply, Matrix.one_apply, id_eq]
    rfl
  change original.det = _
  rw [hrow, Matrix.det_succ_column_zero, Fin.sum_univ_succ]
  simp only [reduced, Fin.cons_zero, Fin.cons_succ, Fin.val_zero, pow_zero, one_mul,
    mul_zero, zero_mul, Finset.sum_const_zero, add_zero]
  change delta.det = _
  rw [hdelta, Matrix.det_permute, Matrix.det_one, mul_one]

/-- The actual determinant is the sign of the existing chronological step
equivalence; no new coordinate witness is selected. -/
theorem determinant_eq_coordinateEquivalence_sign
    (cube : SpernerCube) (vertices : Fin (cube.n + 1) → cube.G)
    (hsimplex : simplex cube cube.n vertices) :
    determinant (fun vertex coordinate => ((vertices vertex coordinate).val : ℤ)) =
      (Equiv.Perm.sign (coordinateEquivalence hsimplex rfl) : ℤ) := by
  apply determinant_eq_sign_of_unitCoordinatePermutation _
    (coordinateEquivalence hsimplex rfl)
  exact integerCoordinate_eq_add_stepIndicator hsimplex rfl

/-- Every actual top-dimensional ordered Kuhn simplex has a unit lattice determinant. -/
theorem abs_determinant_eq_one_of_simplex
    (cube : SpernerCube) (vertices : Fin (cube.n + 1) → cube.G)
    (hsimplex : simplex cube cube.n vertices) :
    |determinant (fun vertex coordinate => ((vertices vertex coordinate).val : ℤ))| = 1 := by
  rw [determinant_eq_coordinateEquivalence_sign cube vertices hsimplex]
  exact Int.units_eq_one_or (Equiv.Perm.sign (coordinateEquivalence hsimplex rfl)) |>.elim
    (fun h => by simp [h]) (fun h => by simp [h])

end Math.KuhnSimplex
