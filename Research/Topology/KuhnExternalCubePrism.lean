import Research.Topology.BoxComplementaritySpernerSubdivisionPrism

/-! # Prism comparison for external proper cube labels -/

noncomputable section

namespace Math

open Classical

variable {n resolution : ℕ}

/-- A completely discrete switch between two proper labels on the same grid.
No continuity of the switch is asserted or used. -/
def externalCubeLabelPrism
    {n resolution : ℕ} (hresolution : 0 < resolution)
    (left right : KuhnCubeBoundaryLabeling n resolution) :
    KuhnPrismSpatialBoundaryLabeling n resolution hresolution where
  label vertex := if vertex (Fin.last n) = 0
    then left.label (Fin.init vertex) else right.label (Fin.init vertex)
  label_ne_of_spatial_eq_zero vertex who hzero := by
    split_ifs with hparameter
    · exact left.label_ne_of_eq_zero (Fin.init vertex) who hzero
    · exact right.label_ne_of_eq_zero (Fin.init vertex) who hzero
  label_le_of_spatial_eq_top vertex who htop := by
    split_ifs with hparameter
    · exact left.label_le_of_eq_top (Fin.init vertex) who htop
    · exact right.label_le_of_eq_top (Fin.init vertex) who htop

@[simp] theorem externalCubeLabelPrism_left_end
    {n resolution : ℕ} (hresolution : 0 < resolution)
    (left right : KuhnCubeBoundaryLabeling n resolution)
    (vertex : Fin n → Fin (resolution + 1)) :
    (externalCubeLabelPrism hresolution left right).label
      (kuhnPrismEndVertex resolution hresolution 0 vertex) = left.label vertex := by
  simp only [externalCubeLabelPrism]
  rw [kuhnPrismEndVertex_last]
  have hinit : Fin.init (kuhnPrismEndVertex resolution hresolution 0 vertex) =
      vertex := by
    funext who
    exact kuhnPrismEndVertex_castSucc resolution hresolution 0 vertex who
  rw [hinit]
  change (if (0 : Fin (resolution + 1)) = 0 then left.label vertex
    else right.label vertex) = left.label vertex
  rw [if_pos rfl]

@[simp] theorem externalCubeLabelPrism_right_end
    {n resolution : ℕ} (hresolution : 0 < resolution)
    (left right : KuhnCubeBoundaryLabeling n resolution)
    (vertex : Fin n → Fin (resolution + 1)) :
    (externalCubeLabelPrism hresolution left right).label
      (kuhnPrismEndVertex resolution hresolution (Fin.last resolution) vertex) =
        right.label vertex := by
  simp only [externalCubeLabelPrism]
  rw [kuhnPrismEndVertex_last]
  have hinit : Fin.init (kuhnPrismEndVertex resolution hresolution
      (Fin.last resolution) vertex) = vertex := by
    funext who
    exact kuhnPrismEndVertex_castSucc resolution hresolution
      (Fin.last resolution) vertex who
  rw [hinit]
  have hlast : Fin.last resolution ≠ (0 : Fin (resolution + 1)) := by
    intro heq
    have := congrArg Fin.val heq
    simp only [Fin.val_last, Fin.val_zero] at this
    omega
  change (if Fin.last resolution = 0 then left.label vertex
    else right.label vertex) = right.label vertex
  rw [if_neg hlast]

/-- The generic finite prism immediately compares the signed endpoint face
sums of the two external proper cube labels. -/
theorem externalCubeLabelPrism_leftEndSignedWeight_eq_rightEndSignedWeight
    {n resolution : ℕ} (hresolution : 0 < resolution)
    (left right : KuhnCubeBoundaryLabeling n resolution) :
    (∑ face ∈ Finset.univ.filter (fun face : KuhnPrismFace n resolution hresolution
      (externalCubeLabelPrism hresolution left right).label ↦ face.IsLeftEnd),
      KuhnSimplex.parameterFaceWeight rfl
        (externalCubeLabelPrism hresolution left right).label face) =
    ∑ face ∈ Finset.univ.filter (fun face : KuhnPrismFace n resolution hresolution
      (externalCubeLabelPrism hresolution left right).label ↦ face.IsRightEnd),
      KuhnSimplex.parameterFaceWeight rfl
        (externalCubeLabelPrism hresolution left right).label face :=
  (externalCubeLabelPrism hresolution left right).leftEndSignedWeight_eq_rightEndSignedWeight

def externalCubeLabelPrismLeftEndEquiv
    (hresolution : 0 < resolution) (left right : KuhnCubeBoundaryLabeling n resolution) :
    {face : KuhnPrismFace n resolution hresolution
      (externalCubeLabelPrism hresolution left right).label // face.IsLeftEnd} ≃
      KuhnExternalEndpointSimplex left hresolution :=
  externalPrismParameterEndEquiv hresolution
    (externalCubeLabelPrism hresolution left right) 0 left
      (externalCubeLabelPrism_left_end hresolution left right)

def externalCubeLabelPrismRightEndEquiv
    (hresolution : 0 < resolution) (left right : KuhnCubeBoundaryLabeling n resolution) :
    {face : KuhnPrismFace n resolution hresolution
      (externalCubeLabelPrism hresolution left right).label // face.IsRightEnd} ≃
      KuhnExternalEndpointSimplex right hresolution :=
  (Equiv.subtypeEquivProp (by
    funext face
    apply propext
    constructor
    · intro h index
      apply Fin.ext
      exact h index
    · intro h index
      exact congrArg Fin.val (h index))).trans
    (externalPrismParameterEndEquiv hresolution
      (externalCubeLabelPrism hresolution left right) (Fin.last resolution) right
      (externalCubeLabelPrism_right_end hresolution left right))

/-- Weighted signed endpoint sums agree for any two proper external labels,
provided the multiplier is constant across incident cell-face pairs. -/
theorem externalCubeLabelPrism_endpointWeightedSum_eq
    (hresolution : 0 < resolution) (left right : KuhnCubeBoundaryLabeling n resolution)
    (selection : (Fin n → Fin (resolution + 1)) → ℤ)
    (hcompatible : ∀ cell : KuhnPrismCell n resolution hresolution,
      ∀ face : KuhnPrismFace n resolution hresolution
        (externalCubeLabelPrism hresolution left right).label,
      kuhnPrismIncident cell face →
        selection (Fin.init (cell.1 0)) = selection (Fin.init (face.1 0))) :
    (∑ endpoint : KuhnExternalEndpointSimplex left hresolution,
      selection (endpoint.1 0) * endpoint.signedWeight) =
    ∑ endpoint : KuhnExternalEndpointSimplex right hresolution,
      selection (endpoint.1 0) * endpoint.signedWeight :=
  (externalCubeLabelPrism hresolution left right).externalEndpointWeightedSum_eq
    left right (externalCubeLabelPrism_left_end hresolution left right)
      (externalCubeLabelPrism_right_end hresolution left right) selection hcompatible

theorem externalCubeLabelPrism_endpointSignedWeight_eq
    (hresolution : 0 < resolution) (left right : KuhnCubeBoundaryLabeling n resolution) :
    (∑ endpoint : KuhnExternalEndpointSimplex left hresolution,
      endpoint.signedWeight) =
    ∑ endpoint : KuhnExternalEndpointSimplex right hresolution,
      endpoint.signedWeight := by
  simpa only [one_mul] using externalCubeLabelPrism_endpointWeightedSum_eq
    hresolution left right (fun _ ↦ 1) (fun _ _ _ ↦ rfl)

end Math
