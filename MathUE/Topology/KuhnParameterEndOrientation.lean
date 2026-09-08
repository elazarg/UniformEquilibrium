import MathUE.Topology.KuhnSimplexIncidence
import MathUE.Topology.OrientedSimplexFacetDeterminant

/-! # Signed incidence at the parameter ends of an actual Kuhn prism -/

noncomputable section

namespace Math.KuhnSharedFace

open OrientedSimplexFacet
open KuhnSimplex

/-- Literal parent incidence at the left parameter end gives its inherited
signed spatial determinant, with the parameter coordinate last. -/
theorem exists_leftParameterEnd_signed_determinant
    (cube : SpernerCube) {dimension : ℕ} (hdimension : dimension + 1 = cube.n)
    (face : Fin (dimension + 1) → cube.G) (parent : Fin (cube.n + 1) → cube.G)
    (hincident : is_face cube face parent)
    (hend : ∀ vertex, face vertex (Fin.cast hdimension (Fin.last dimension)) = 0) :
    ∃ omitted : Fin (cube.n + 1),
      face = @delete_vertex cube dimension hdimension omitted parent ∧
      (-1) ^ (omitted : ℕ) *
        determinant (fun vertex coordinate => ((parent vertex coordinate).val : ℤ)) =
      (-1) ^ (dimension + 1) * determinant (fun vertex coordinate =>
        ((face vertex (Fin.cast hdimension coordinate.castSucc)).val : ℤ)) := by
  rcases cube with ⟨ambient, resolution, label, hlabel⟩
  cases hdimension
  obtain ⟨omitted, homitted⟩ :=
    (@child_simplex_char _ dimension rfl face parent hincident.2.1).mp hincident
  refine ⟨omitted, homitted, ?_⟩
  have hstandard : ∀ kept, face kept = parent (omitted.succAbove kept) := by
    intro kept
    have h := congrFun homitted kept
    simpa only [delete_vertex, insertIndex_eq_succAbove_cast, Fin.cast_refl, id_eq] using h
  have hcoordinate := KuhnSimplex.omittedCoordinate_eq_one_of_zero_face
    _ parent hincident.2.1 omitted (Fin.last dimension) (fun kept => by
      rw [← hstandard]
      exact hend kept)
  have hfaceCast : (fun kept coordinate =>
      ((parent (omitted.succAbove kept) coordinate).val : ℤ)) =
      (fun kept coordinate => ((face kept coordinate).val : ℤ)) := by
    funext kept coordinate
    rw [← hstandard]
  have hdeletion := facetDeterminant_delete
    (fun vertex coordinate => ((parent vertex coordinate).val : ℤ)) omitted
  rw [hfaceCast] at hdeletion
  rw [← hdeletion, facetDeterminant_eq_lastCoordinate_displacement _ _ 0 (by
    intro vertex
    exact_mod_cast hend vertex)]
  simp only [hcoordinate, Nat.cast_one, sub_zero, mul_one]
  rfl

/-- Literal parent incidence at the right parameter end gives the opposite
parameter-boundary sign, without an extra positive-resolution assumption. -/
theorem exists_rightParameterEnd_signed_determinant
    (cube : SpernerCube) {dimension : ℕ} (hdimension : dimension + 1 = cube.n)
    (face : Fin (dimension + 1) → cube.G) (parent : Fin (cube.n + 1) → cube.G)
    (hincident : is_face cube face parent)
    (hend : ∀ vertex,
      (face vertex (Fin.cast hdimension (Fin.last dimension))).val = cube.p) :
    ∃ omitted : Fin (cube.n + 1),
      face = @delete_vertex cube dimension hdimension omitted parent ∧
      (-1) ^ (omitted : ℕ) *
        determinant (fun vertex coordinate => ((parent vertex coordinate).val : ℤ)) =
      (-1) ^ dimension * determinant (fun vertex coordinate =>
        ((face vertex (Fin.cast hdimension coordinate.castSucc)).val : ℤ)) := by
  rcases cube with ⟨ambient, resolution, label, hlabel⟩
  cases hdimension
  obtain ⟨omitted, homitted⟩ :=
    (@child_simplex_char _ dimension rfl face parent hincident.2.1).mp hincident
  refine ⟨omitted, homitted, ?_⟩
  have hstandard : ∀ kept, face kept = parent (omitted.succAbove kept) := by
    intro kept
    have h := congrFun homitted kept
    simpa only [delete_vertex, insertIndex_eq_succAbove_cast, Fin.cast_refl, id_eq] using h
  have hcoordinate := KuhnSimplex.omittedCoordinate_add_one_eq_resolution_of_maximal_face
    _ parent hincident.2.1 omitted (Fin.last dimension) (fun kept => by
      rw [← hstandard]
      exact hend kept)
  have hdisplacement : ((parent omitted (Fin.last dimension)).val : ℤ) - resolution = -1 := by
    dsimp only [SpernerCube.p] at hcoordinate
    omega
  have hfaceCast : (fun kept coordinate =>
      ((parent (omitted.succAbove kept) coordinate).val : ℤ)) =
      (fun kept coordinate => ((face kept coordinate).val : ℤ)) := by
    funext kept coordinate
    rw [← hstandard]
  have hdeletion := facetDeterminant_delete
    (fun vertex coordinate => ((parent vertex coordinate).val : ℤ)) omitted
  rw [hfaceCast] at hdeletion
  rw [← hdeletion, facetDeterminant_eq_lastCoordinate_displacement _ _ (resolution : ℤ) (by
    intro vertex
    exact_mod_cast hend vertex), hdisplacement]
  simp only [pow_succ, mul_neg, mul_one, neg_neg]
  rfl

end Math.KuhnSharedFace
