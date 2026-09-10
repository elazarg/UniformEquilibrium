import Research.Topology.BoxComplementaritySpernerSubdivisionPrism

/-! # Prism comparison for external proper cube labels -/

noncomputable section

namespace Math

open Classical

variable {n resolution : ℕ}

/-- A bounded external label on one cubical grid, with exactly the spatial
boundary conditions needed by the finite prism argument. -/
structure KuhnCubeBoundaryLabeling (n resolution : ℕ) where
  label : (Fin n → Fin (resolution + 1)) → Fin (n + 1)
  label_ne_of_eq_zero : ∀ vertex (who : Fin n),
    vertex who = 0 → label vertex ≠ who.castSucc
  label_le_of_eq_top : ∀ vertex (who : Fin n),
    (vertex who).1 = resolution → label vertex ≤ who.castSucc

/-- The bounded finite label supplied by a proper `SpernerCube`. -/
def SpernerCube.toKuhnCubeBoundaryLabeling (cube : SpernerCube) :
    KuhnCubeBoundaryLabeling cube.n cube.p where
  label vertex := ⟨cube.RL vertex, Nat.lt_succ_of_le (cube.rl_proper vertex).1⟩
  label_ne_of_eq_zero vertex who hzero := by
    intro heq
    exact (cube.rl_proper vertex).2 who |>.1 hzero (congrArg Fin.val heq)
  label_le_of_eq_top vertex who htop := by
    apply Fin.val_fin_le.mpr
    exact (cube.rl_proper vertex).2 who |>.2 htop

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
  have hinit : Fin.init (kuhnPrismEndVertex resolution hresolution 0 vertex) = vertex := by
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
      (externalCubeLabelPrism hresolution left right).label => face.IsLeftEnd),
      KuhnSimplex.parameterFaceWeight rfl
        (externalCubeLabelPrism hresolution left right).label face) =
    ∑ face ∈ Finset.univ.filter (fun face : KuhnPrismFace n resolution hresolution
      (externalCubeLabelPrism hresolution left right).label => face.IsRightEnd),
      KuhnSimplex.parameterFaceWeight rfl
        (externalCubeLabelPrism hresolution left right).label face :=
  (externalCubeLabelPrism hresolution left right).leftEndSignedWeight_eq_rightEndSignedWeight

/-- A spatial Kuhn simplex carrying every external finite label. -/
def KuhnExternalEndpointSimplex (labeling : KuhnCubeBoundaryLabeling n resolution)
    (hresolution : 0 < resolution) :=
  {vertices : Fin (n + 1) →
      (boxComplementaritySpernerCube (zeroBoxComplementarityProblem n)
        resolution hresolution).G //
    simplex (boxComplementaritySpernerCube (zeroBoxComplementarityProblem n)
      resolution hresolution) n vertices ∧
      Function.Injective fun index ↦ labeling.label (vertices index)}

instance (labeling : KuhnCubeBoundaryLabeling n resolution)
    (hresolution : 0 < resolution) :
    Finite (KuhnExternalEndpointSimplex labeling hresolution) :=
  Finite.of_injective Subtype.val Subtype.val_injective

noncomputable instance (labeling : KuhnCubeBoundaryLabeling n resolution)
    (hresolution : 0 < resolution) :
    Fintype (KuhnExternalEndpointSimplex labeling hresolution) :=
  Fintype.ofFinite _

/-- Literal geometric and external-label weight of an endpoint simplex. -/
def KuhnExternalEndpointSimplex.signedWeight
    {labeling : KuhnCubeBoundaryLabeling n resolution} {hresolution : 0 < resolution}
    (simplex : KuhnExternalEndpointSimplex labeling hresolution) : ℤ :=
  OrientedSimplexFacet.determinant
      (fun vertex coordinate => ((simplex.1 vertex coordinate).val : ℤ)) *
    SignedSimplexLabel.orientation (fun vertex => labeling.label (simplex.1 vertex))

theorem externalPrism_label_eq_endpoint_of_last_eq
    (hresolution : 0 < resolution)
    (boundary : KuhnPrismSpatialBoundaryLabeling n resolution hresolution)
    (parameter : Fin (resolution + 1)) (endpoint : KuhnCubeBoundaryLabeling n resolution)
    (hlabel : ∀ vertex, boundary.label
      (kuhnPrismEndVertex resolution hresolution parameter vertex) = endpoint.label vertex)
    (vertex : (kuhnPrismGeometryCube n resolution hresolution).G)
    (hlast : vertex (Fin.last n) = parameter) :
    boundary.label vertex = endpoint.label (Fin.init vertex) := by
  rw [← hlabel]
  congr 1
  funext coordinate
  refine Fin.lastCases ?_ (fun who ↦ ?_) coordinate
  · simpa using hlast
  · rw [kuhnPrismEndVertex_castSucc]
    rfl

/-- A prism parameter end is the corresponding externally labeled simplex. -/
def externalPrismParameterEndEquiv
    (hresolution : 0 < resolution)
    (boundary : KuhnPrismSpatialBoundaryLabeling n resolution hresolution)
    (parameter : Fin (resolution + 1))
    (endpoint : KuhnCubeBoundaryLabeling n resolution)
    (hlabel : ∀ vertex : Fin n → Fin (resolution + 1),
      boundary.label (kuhnPrismEndVertex resolution hresolution parameter vertex) =
        endpoint.label vertex) :
    {face : KuhnPrismFace n resolution hresolution boundary.label //
      ∀ index, face.1 index (Fin.last n) = parameter} ≃
      KuhnExternalEndpointSimplex endpoint hresolution where
  toFun face := ⟨fun index ↦ Fin.init (face.1.1 index),
    simplex_finInit_of_kuhnPrismEnd (zeroBoxComplementarityProblem n)
      resolution hresolution parameter face.1.1 face.1.2.1 face.2, by
      intro first second heq
      apply face.1.2.2
      change endpoint.label (Fin.init (face.1.1 first)) =
        endpoint.label (Fin.init (face.1.1 second)) at heq
      change boundary.label (face.1.1 first) = boundary.label (face.1.1 second)
      rw [externalPrism_label_eq_endpoint_of_last_eq hresolution boundary parameter
        endpoint hlabel (face.1.1 first) (face.2 first),
        externalPrism_label_eq_endpoint_of_last_eq hresolution boundary parameter
        endpoint hlabel (face.1.1 second) (face.2 second)]
      exact heq⟩
  invFun simplex := ⟨⟨fun index ↦ kuhnPrismEndVertex resolution hresolution parameter
      (simplex.1 index), simplex_kuhnPrismEndVertex (zeroBoxComplementarityProblem n)
        resolution hresolution parameter simplex.1 simplex.2.1, by
          intro first second heq
          apply simplex.2.2
          simpa only [hlabel] using heq⟩, fun index ↦
            kuhnPrismEndVertex_last resolution hresolution parameter (simplex.1 index)⟩
  left_inv face := by
    apply Subtype.ext
    apply Subtype.ext
    funext index coordinate
    refine Fin.lastCases ?_ (fun who ↦ ?_) coordinate
    · simpa using (face.2 index).symm
    · simp only [kuhnPrismEndVertex_castSucc]
      rfl
  right_inv simplex := by
    apply Subtype.ext
    funext index who
    simp

/-- The parameter-end equivalence preserves the existing signed weight. -/
theorem externalPrismParameterEndEquiv_signedWeight
    (hresolution : 0 < resolution)
    (boundary : KuhnPrismSpatialBoundaryLabeling n resolution hresolution)
    (parameter : Fin (resolution + 1))
    (endpoint : KuhnCubeBoundaryLabeling n resolution)
    (hlabel : ∀ vertex, boundary.label
      (kuhnPrismEndVertex resolution hresolution parameter vertex) = endpoint.label vertex)
    (face : {face : KuhnPrismFace n resolution hresolution boundary.label //
      ∀ index, face.1 index (Fin.last n) = parameter}) :
    KuhnSimplex.parameterFaceWeight rfl boundary.label face.1 =
      (externalPrismParameterEndEquiv hresolution boundary parameter endpoint hlabel
        face).signedWeight := by
  unfold KuhnSimplex.parameterFaceWeight KuhnExternalEndpointSimplex.signedWeight
  congr 1
  apply congrArg SignedSimplexLabel.orientation
  funext vertex
  exact externalPrism_label_eq_endpoint_of_last_eq hresolution boundary parameter
    endpoint hlabel (face.1.1 vertex) (face.2 vertex)

def externalCubeLabelPrismLeftEndEquiv
    (hresolution : 0 < resolution) (left right : KuhnCubeBoundaryLabeling n resolution) :
    {face : KuhnPrismFace n resolution hresolution
      (externalCubeLabelPrism hresolution left right).label // face.IsLeftEnd} ≃
      KuhnExternalEndpointSimplex left hresolution :=
  externalPrismParameterEndEquiv hresolution (externalCubeLabelPrism hresolution left right)
    0 left (externalCubeLabelPrism_left_end hresolution left right)

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
      selection (endpoint.1 0) * endpoint.signedWeight := by
  let boundary := externalCubeLabelPrism hresolution left right
  let faceWeight := fun face : KuhnPrismFace n resolution hresolution boundary.label =>
    selection (Fin.init (face.1 0)) * KuhnSimplex.parameterFaceWeight rfl boundary.label face
  have hleft : (∑ face ∈ Finset.univ.filter (fun face : KuhnPrismFace n resolution
      hresolution boundary.label => face.IsLeftEnd), faceWeight face) =
      ∑ endpoint : KuhnExternalEndpointSimplex left hresolution,
        selection (endpoint.1 0) * endpoint.signedWeight := by
    rw [Finset.sum_subtype (p := KuhnPrismFace.IsLeftEnd) _ (by intro face; simp) faceWeight]
    apply Fintype.sum_equiv (externalCubeLabelPrismLeftEndEquiv hresolution left right)
    intro face
    unfold faceWeight boundary
    rw [externalPrismParameterEndEquiv_signedWeight]
    rfl
  have hright : (∑ face ∈ Finset.univ.filter (fun face : KuhnPrismFace n resolution
      hresolution boundary.label => face.IsRightEnd), faceWeight face) =
      ∑ endpoint : KuhnExternalEndpointSimplex right hresolution,
        selection (endpoint.1 0) * endpoint.signedWeight := by
    rw [Finset.sum_subtype (p := KuhnPrismFace.IsRightEnd) _ (by intro face; simp) faceWeight]
    apply Fintype.sum_equiv (externalCubeLabelPrismRightEndEquiv hresolution left right)
    intro face
    unfold faceWeight boundary
    have hparameter : ∀ index, face.1.1 index (Fin.last n) = Fin.last resolution :=
      fun index => Fin.ext (face.2 index)
    have hweight := externalPrismParameterEndEquiv_signedWeight hresolution
      (externalCubeLabelPrism hresolution left right) (Fin.last resolution) right
      (externalCubeLabelPrism_right_end hresolution left right) ⟨face.1, hparameter⟩
    rw [hweight]
    change selection (Fin.init (face.1.1 0)) * _ = _
    simp only [externalCubeLabelPrismRightEndEquiv, Equiv.trans_apply]
    rfl
  rw [← hleft, ← hright]
  have h := KuhnSimplex.sum_weighted_parameterFaceWeight_left_eq_right rfl boundary.label
    (fun cell => selection (Fin.init (cell.1 0)))
    (fun face => selection (Fin.init (face.1 0))) hcompatible
    (fun face hface => (boundary.isGeometricBoundary_iff face).mp hface)
  have hcast : Fin.cast (show n + 1 = (kuhnPrismGeometryCube n resolution hresolution).n
      from rfl) (Fin.last n) = Fin.last n := Fin.ext rfl
  have hp : (kuhnPrismGeometryCube n resolution hresolution).p = resolution := rfl
  simpa only [hcast, hp, KuhnPrismFace.IsLeftEnd, KuhnPrismFace.IsRightEnd,
    faceWeight] using h

theorem externalCubeLabelPrism_endpointSignedWeight_eq
    (hresolution : 0 < resolution) (left right : KuhnCubeBoundaryLabeling n resolution) :
    (∑ endpoint : KuhnExternalEndpointSimplex left hresolution, endpoint.signedWeight) =
      ∑ endpoint : KuhnExternalEndpointSimplex right hresolution, endpoint.signedWeight := by
  simpa only [one_mul] using externalCubeLabelPrism_endpointWeightedSum_eq
    hresolution left right (fun _ => 1) (fun _ _ _ => rfl)

end Math
