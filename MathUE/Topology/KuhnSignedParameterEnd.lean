import MathUE.Topology.KuhnSignedColumnCancellation
import MathUE.Topology.KuhnParameterEndOrientation

/-!
# Integer weights at actual Kuhn parameter ends

The checked parameter-end cofactor identifies the unique parent column with
the signed spatial label weight. Parent uniqueness is supplied by the pinned
coordinate-boundary theorem, not by a new counting argument.
-/

noncomputable section

namespace Math.KuhnSimplex

open Classical OrientedSimplexFacet

variable {cube : SpernerCube} {dimension : ℕ}
  (hdimension : dimension + 1 = cube.n) (label : cube.G → Fin (dimension + 1))

/-- Spatial geometric orientation times the ordered external label orientation. -/
def parameterFaceWeight (face : CompleteFace cube dimension label) : ℤ :=
  determinant (fun vertex coordinate =>
    ((face.1 vertex (Fin.cast hdimension coordinate.castSucc)).val : ℤ)) *
      SignedSimplexLabel.orientation (fun vertex => label (face.1 vertex))

/-- An actual left-end parent has the inherited left parameter-boundary sign. -/
theorem signedIncidence_eq_leftParameterEnd_weight
    (cell : Cell cube) (face : CompleteFace cube dimension label)
    (hincident : Incident cell face)
    (hend : ∀ vertex, face.1 vertex (Fin.cast hdimension (Fin.last dimension)) = 0) :
    signedIncidence hdimension label cell face =
      (-1) ^ (dimension + 1) * parameterFaceWeight hdimension label face := by
  obtain ⟨omitted, hface, hsign⟩ :=
    KuhnSharedFace.exists_leftParameterEnd_signed_determinant
      cube hdimension face.1 cell.1 hincident hend
  rw [signedIncidence_eq_of_face_eq_delete hdimension label cell face omitted hface]
  have h := congrArg
    (fun value : ℤ => value * SignedSimplexLabel.orientation (fun vertex => label (face.1 vertex)))
    hsign
  unfold parameterFaceWeight
  convert h using 1 <;> ring

/-- An actual right-end parent has the opposite parameter-boundary sign. -/
theorem signedIncidence_eq_rightParameterEnd_weight
    (cell : Cell cube) (face : CompleteFace cube dimension label)
    (hincident : Incident cell face)
    (hend : ∀ vertex,
      (face.1 vertex (Fin.cast hdimension (Fin.last dimension))).val = cube.p) :
    signedIncidence hdimension label cell face =
      (-1) ^ dimension * parameterFaceWeight hdimension label face := by
  obtain ⟨omitted, hface, hsign⟩ :=
    KuhnSharedFace.exists_rightParameterEnd_signed_determinant
      cube hdimension face.1 cell.1 hincident hend
  rw [signedIncidence_eq_of_face_eq_delete hdimension label cell face omitted hface]
  have h := congrArg
    (fun value : ℤ => value * SignedSimplexLabel.orientation (fun vertex => label (face.1 vertex)))
    hsign
  unfold parameterFaceWeight
  convert h using 1 <;> ring

/-- The complete left-end column is its single actual parent's signed spatial weight. -/
theorem sum_signedIncidence_cells_eq_leftParameterEnd_weight
    (face : CompleteFace cube dimension label)
    (hend : ∀ vertex, face.1 vertex (Fin.cast hdimension (Fin.last dimension)) = 0) :
    (∑ cell : Cell cube, signedIncidence hdimension label cell face) =
      (-1) ^ (dimension + 1) * parameterFaceWeight hdimension label face := by
  have hcard := @case_A_parent_count cube dimension hdimension face.1 face.2.1
    ⟨Fin.cast hdimension (Fin.last dimension), hend⟩
  rw [← face.incidentCell_card_eq_parent_card] at hcard
  obtain ⟨cell, hcell⟩ := Finset.card_eq_one.mp hcard
  have hincident : Incident cell face := by
    have hmem : cell ∈ Finset.univ.filter (fun cell : Cell cube => Incident cell face) := by
      rw [hcell]
      exact Finset.mem_singleton_self cell
    exact (Finset.mem_filter.mp hmem).2
  rw [sum_signedIncidence_cells_eq_incident_sum, hcell, Finset.sum_singleton]
  exact signedIncidence_eq_leftParameterEnd_weight hdimension label cell face hincident hend

/-- The complete right-end column is its single actual parent's signed spatial weight. -/
theorem sum_signedIncidence_cells_eq_rightParameterEnd_weight
    (face : CompleteFace cube dimension label)
    (hend : ∀ vertex,
      (face.1 vertex (Fin.cast hdimension (Fin.last dimension))).val = cube.p) :
    (∑ cell : Cell cube, signedIncidence hdimension label cell face) =
      (-1) ^ dimension * parameterFaceWeight hdimension label face := by
  have hcard := @case_B_parent_count cube dimension hdimension face.1 face.2.1
    ⟨Fin.cast hdimension (Fin.last dimension), fun vertex => Fin.ext (hend vertex)⟩
  rw [← face.incidentCell_card_eq_parent_card] at hcard
  obtain ⟨cell, hcell⟩ := Finset.card_eq_one.mp hcard
  have hincident : Incident cell face := by
    have hmem : cell ∈ Finset.univ.filter (fun cell : Cell cube => Incident cell face) := by
      rw [hcell]
      exact Finset.mem_singleton_self cell
    exact (Finset.mem_filter.mp hmem).2
  rw [sum_signedIncidence_cells_eq_incident_sum, hcell, Finset.sum_singleton]
  exact signedIncidence_eq_rightParameterEnd_weight hdimension label cell face hincident hend

/-- Actual finite signed endpoint sums agree when every complete geometric
boundary face lies at a parameter end. The external-labeling prism interface
supplies this boundary classification; no degree invariant is assumed. -/
theorem sum_parameterFaceWeight_left_eq_right
    (hboundary : ∀ face : CompleteFace cube dimension label, is_boundary_face cube face.1 →
      (∀ vertex, face.1 vertex (Fin.cast hdimension (Fin.last dimension)) = 0) ∨
      (∀ vertex,
        (face.1 vertex (Fin.cast hdimension (Fin.last dimension))).val = cube.p)) :
    (∑ face ∈ Finset.univ.filter (fun face : CompleteFace cube dimension label =>
      ∀ vertex, face.1 vertex (Fin.cast hdimension (Fin.last dimension)) = 0),
      parameterFaceWeight hdimension label face) =
    ∑ face ∈ Finset.univ.filter (fun face : CompleteFace cube dimension label =>
      ∀ vertex, (face.1 vertex (Fin.cast hdimension (Fin.last dimension))).val = cube.p),
      parameterFaceWeight hdimension label face := by
  let leftEnd (face : CompleteFace cube dimension label) : Prop :=
    ∀ vertex, face.1 vertex (Fin.cast hdimension (Fin.last dimension)) = 0
  let rightEnd (face : CompleteFace cube dimension label) : Prop :=
    ∀ vertex, (face.1 vertex (Fin.cast hdimension (Fin.last dimension))).val = cube.p
  have hdisjoint (face : CompleteFace cube dimension label)
      (hleft : leftEnd face) (hright : rightEnd face) : False := by
    have hzero := congrArg Fin.val (hleft 0)
    have hmax := hright 0
    have hp : cube.p = 0 := by simp only [Fin.val_zero] at hzero; omega
    exact (@p_ne_zero_of_cube cube dimension hdimension) (Fin.ext hp)
  have htotal : (∑ face : CompleteFace cube dimension label, ∑ cell : Cell cube,
      signedIncidence hdimension label cell face) = 0 := by
    rw [Finset.sum_comm]
    simp only [sum_signedIncidence_faces_eq_zero, Finset.sum_const_zero]
  have hcolumn (face : CompleteFace cube dimension label) :
      (∑ cell : Cell cube, signedIncidence hdimension label cell face) =
      (if leftEnd face then (-1) ^ (dimension + 1) *
        parameterFaceWeight hdimension label face else 0) +
      (if rightEnd face then (-1) ^ dimension *
        parameterFaceWeight hdimension label face else 0) := by
    by_cases hleft : leftEnd face
    · have hright : ¬ rightEnd face := hdisjoint face hleft
      simp only [if_pos hleft, if_neg hright, add_zero]
      exact sum_signedIncidence_cells_eq_leftParameterEnd_weight
        hdimension label face hleft
    · by_cases hright : rightEnd face
      · simp only [if_neg hleft, if_pos hright, zero_add]
        exact sum_signedIncidence_cells_eq_rightParameterEnd_weight
          hdimension label face hright
      · simp only [if_neg hleft, if_neg hright, zero_add]
        apply sum_signedIncidence_cells_eq_zero_of_not_boundary
        intro hface
        exact (hboundary face hface).elim hleft hright
  simp_rw [hcolumn] at htotal
  rw [Finset.sum_add_distrib, ← Finset.sum_filter, ← Finset.sum_filter,
    ← Finset.mul_sum, ← Finset.mul_sum] at htotal
  have hfactor : (-1 : ℤ) ^ dimension *
      ((∑ face ∈ Finset.univ.filter rightEnd, parameterFaceWeight hdimension label face) -
        ∑ face ∈ Finset.univ.filter leftEnd, parameterFaceWeight hdimension label face) = 0 := by
    rw [pow_succ] at htotal
    convert htotal using 1
    ring
  exact (sub_eq_zero.mp ((mul_eq_zero.mp hfactor).resolve_left
    (pow_ne_zero _ (by norm_num)))).symm

end Math.KuhnSimplex
