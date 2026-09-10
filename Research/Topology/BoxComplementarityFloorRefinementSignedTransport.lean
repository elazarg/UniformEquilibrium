import Research.Topology.BoxComplementarityFloorRefinementPrismCluster
import Research.Topology.BoxComplementarityLocalSignedHomotopy

/-! # Local signed-count transport through coordinate-floor refinement -/

noncomputable section

namespace Math

open Classical Filter Set Topology

variable {n : ℕ}

/-- A complete simplex for any proper Sperner cube is the corresponding
generic external endpoint simplex. -/
def completeSimplexEquivKuhnExternalEndpointSimplex
    (cube : SpernerCube) (hresolution : 0 < cube.p) :
    {vertices : Fin (cube.n + 1) → cube.G //
      complete_simplex cube cube.n vertices} ≃
      KuhnExternalEndpointSimplex
        (SpernerCube.toKuhnCubeBoundaryLabeling cube) hresolution where
  toFun vertices := ⟨vertices.1, by
    constructor
    · simpa only [simplex, SpernerCube.G, boxComplementaritySpernerCube,
        zeroBoxComplementarityProblem] using vertices.2.1
    · intro first second heq
      apply rl_inj_of_complete cube.n vertices.1 vertices.2
      exact congrArg Fin.val heq⟩
  invFun endpoint := by
    let vertices : Fin (cube.n + 1) → cube.G :=
      fun index coordinate ↦ endpoint.1 index coordinate
    refine ⟨vertices, ?_⟩
    have hsimplex : simplex cube cube.n vertices := by
      simpa only [simplex, SpernerCube.G, boxComplementaritySpernerCube,
        zeroBoxComplementarityProblem] using endpoint.2.1
    rw [complete_simplex_iff cube.n vertices hsimplex]
    intro label hlabel
    let target : Fin (cube.n + 1) :=
      ⟨label, Nat.lt_succ_of_le hlabel⟩
    have hsurjective : Function.Surjective (fun index ↦
        (SpernerCube.toKuhnCubeBoundaryLabeling cube).label
          (vertices index)) := by
      apply ((Fintype.bijective_iff_injective_and_card _).2
        ⟨?_, rfl⟩).2
      intro first second heq
      apply endpoint.2.2
      exact heq
    obtain ⟨index, hindex⟩ := hsurjective target
    exact ⟨index, congrArg Fin.val hindex⟩
  left_inv vertices := by
    apply Subtype.ext
    rfl
  right_inv endpoint := by
    apply Subtype.ext
    funext index coordinate
    rfl

/-- Canonical coordinate-floor lifting identifies coarse box endpoints with
the floor-pulled external endpoints on the refined grid. -/
def boxComplementarityEndpointEquivFloorPullbackExternal
    (problem : BoxComplementarityProblem (Fin n))
    (p k : ℕ) (hp : 0 < p) (hk : 0 < k) :
    KuhnEndpointLabeledSimplex problem p hp ≃
      KuhnExternalEndpointSimplex
        (boxComplementarityFloorPullbackBoundaryLabeling
          problem p k hp hk) (Nat.mul_pos hp hk) :=
  (completeSimplexEquivKuhnEndpointLabeledSimplex problem p hp).symm |>.trans
    ((completeSimplexFloorEquiv
      (boxComplementaritySpernerCube problem p hp) k hk).symm.trans
        (completeSimplexEquivKuhnExternalEndpointSimplex
          (floorPullbackSpernerCube
            (boxComplementaritySpernerCube problem p hp) k hk)
          (Nat.mul_pos hp hk)))

theorem boxComplementarityEndpointEquivFloorPullbackExternal_apply
    (problem : BoxComplementarityProblem (Fin n))
    (p k : ℕ) (hp : 0 < p) (hk : 0 < k)
    (endpoint : KuhnEndpointLabeledSimplex problem p hp) :
    (boxComplementarityEndpointEquivFloorPullbackExternal
      problem p k hp hk endpoint).1 =
        kuhnFloorSimplexLift
          (floorPullbackSpernerCube
            (boxComplementaritySpernerCube problem p hp) k hk)
          (boxComplementaritySpernerCube problem p hp) k rfl rfl hk
          endpoint.1 endpoint.2.1 := by
  rfl

/-- The canonical floor lift preserves the literal geometric determinant and
label orientation, hence the endpoint signed weight. -/
theorem boxComplementarityEndpointEquivFloorPullbackExternal_signedWeight
    (problem : BoxComplementarityProblem (Fin n))
    (p k : ℕ) (hp : 0 < p) (hk : 0 < k)
    (endpoint : KuhnEndpointLabeledSimplex problem p hp) :
  (boxComplementarityEndpointEquivFloorPullbackExternal
      problem p k hp hk endpoint).signedWeight = endpoint.signedWeight := by
  rw [KuhnExternalEndpointSimplex.signedWeight,
    KuhnEndpointLabeledSimplex.signedWeight,
    boxComplementarityEndpointEquivFloorPullbackExternal_apply]
  apply congrArg₂ (fun geometric labels : ℤ ↦ geometric * labels)
  · convert kuhnFloorSimplexLift_determinant_eq
      (boxComplementaritySpernerCube problem p hp) k hk
        endpoint.1 endpoint.2.1 using 1 <;>
      apply congrArg OrientedSimplexFacet.determinant <;>
      funext vertex coordinate <;> rfl
  · apply congrArg SignedSimplexLabel.orientation
    funext vertex
    rw [boxComplementarityFloorPullbackBoundaryLabeling_label]
    apply congrArg (boxComplementarityFinLabel problem p)
    exact kuhnFloorVertex_kuhnFloorSimplexLift
      (floorPullbackSpernerCube
        (boxComplementaritySpernerCube problem p hp) k hk)
      (boxComplementaritySpernerCube problem p hp) k rfl rfl hk
        endpoint.1 endpoint.2.1 vertex

private theorem one_div_refined_le_one_div
    (p k : ℕ) (hp : 0 < p) (hk : 0 < k) :
    1 / ((p * k : ℕ) : ℝ) ≤ 1 / (p : ℝ) := by
  apply one_div_le_one_div_of_le (Nat.cast_pos.mpr hp)
  exact_mod_cast calc
    p = p * 1 := by omega
    _ ≤ p * k := Nat.mul_le_mul_left p (Nat.one_le_iff_ne_zero.2 hk.ne')

/-- A cleared actual sample and any displayed nearby point have the same
open-region membership. -/
theorem floorRefinementPrismFace_sample_mem_iff_nearby_of_cleared
    (problem : BoxComplementarityProblem (Fin n))
    (p k : ℕ) (hp : 0 < p) (hk : 0 < k)
    (region : Set (UnitCube (Fin n))) (hopen : IsOpen region) (radius : ℝ)
    (hcleared : ¬HasFloorRefinementPrismFaceSampleIn problem
      (Metric.cthickening radius (frontier region)) p k)
    (face : KuhnPrismFace n (p * k) (Nat.mul_pos hp hk)
      (boxComplementarityFloorRefinementPrism problem p k hp hk).label)
    (index : Fin (n + 1)) (point : UnitCube (Fin n))
    (hdist : dist
      (boxComplementarityFloorRefinementLabelSamplePoint p k (face.1 index))
      point ≤ radius) :
    boxComplementarityFloorRefinementLabelSamplePoint p k (face.1 index) ∈
        region ↔ point ∈ region := by
  let sample :=
    boxComplementarityFloorRefinementLabelSamplePoint p k (face.1 index)
  have hself : dist sample sample ≤ radius := by
    rw [dist_self]
    exact dist_nonneg.trans hdist
  constructor
  · intro hsample
    by_contra hpoint
    exact hcleared ⟨hp, hk, face, index,
      mem_cthickening_frontier_of_unitCube_endpoints
        region hopen sample sample point radius
          hsample hpoint hself hdist⟩
  · intro hpoint
    by_contra hsample
    exact hcleared ⟨hp, hk, face, index,
      mem_cthickening_frontier_of_unitCube_endpoints
        region hopen sample point sample radius
          hpoint hsample hdist hself⟩

/-- Cleared mixed samples make the fine-grid base selection agree across
every actual cell-face incidence. -/
theorem floorRefinementPrismFace_parent_base_mem_iff_of_cleared
    (problem : BoxComplementarityProblem (Fin n))
    (p k : ℕ) (hp : 0 < p) (hk : 0 < k)
    (region : Set (UnitCube (Fin n))) (hopen : IsOpen region) (radius : ℝ)
    (hmesh : 2 / (p : ℝ) ≤ radius)
    (hcleared : ¬HasFloorRefinementPrismFaceSampleIn problem
      (Metric.cthickening radius (frontier region)) p k)
    (face : KuhnPrismFace n (p * k) (Nat.mul_pos hp hk)
      (boxComplementarityFloorRefinementPrism problem p k hp hk).label)
    (cell : KuhnPrismCell n (p * k) (Nat.mul_pos hp hk))
    (hincident : kuhnPrismIncident cell face) :
    boxComplementarityGridPoint (p * k) (Fin.init (cell.1 0)) ∈ region ↔
      boxComplementarityGridPoint (p * k) (Fin.init (face.1 0)) ∈ region := by
  let sample :=
    boxComplementarityFloorRefinementLabelSamplePoint p k (face.1 0)
  let facePoint :=
    boxComplementarityGridPoint (p * k) (Fin.init (face.1 0))
  let cellPoint :=
    boxComplementarityGridPoint (p * k) (Fin.init (cell.1 0))
  have hsampleFace : dist sample facePoint ≤ radius :=
    (dist_floorRefinementLabelSamplePoint_fine_le_one_div
      p k hp hk (face.1 0)).trans (by
        have honeNonnegative : 0 ≤ 1 / (p : ℝ) := by positivity
        have : 1 / (p : ℝ) ≤ 2 / (p : ℝ) := by
          calc
            1 / (p : ℝ) ≤ 1 / (p : ℝ) + 1 / (p : ℝ) :=
              le_add_of_nonneg_right honeNonnegative
            _ = 2 / (p : ℝ) := by ring
        exact this.trans hmesh)
  have hfaceCell : dist facePoint cellPoint ≤ 1 / ((p * k : ℕ) : ℝ) := by
    change dist
      (Fin.init (boxComplementarityGridPoint (p * k) (face.1 0)))
      (Fin.init (boxComplementarityGridPoint (p * k) (cell.1 0))) ≤ _
    exact dist_prismFace_parent_spatial_vertices_le_one_div
      face cell hincident 0 0
  have hsampleCell : dist sample cellPoint ≤ radius := by
    calc
      dist sample cellPoint ≤
          dist sample facePoint + dist facePoint cellPoint := dist_triangle _ _ _
      _ ≤ 1 / (p : ℝ) + 1 / ((p * k : ℕ) : ℝ) :=
        add_le_add
          (dist_floorRefinementLabelSamplePoint_fine_le_one_div
            p k hp hk (face.1 0)) hfaceCell
      _ ≤ 2 / (p : ℝ) := by
        have hrefined := one_div_refined_le_one_div p k hp hk
        calc
          1 / (p : ℝ) + 1 / ((p * k : ℕ) : ℝ) ≤
              1 / (p : ℝ) + 1 / (p : ℝ) :=
            add_le_add_right hrefined _
          _ = 2 / (p : ℝ) := by ring
      _ ≤ radius := hmesh
  have hface := floorRefinementPrismFace_sample_mem_iff_nearby_of_cleared
    problem p k hp hk region hopen radius hcleared face 0 facePoint hsampleFace
  have hcell := floorRefinementPrismFace_sample_mem_iff_nearby_of_cleared
    problem p k hp hk region hopen radius hcleared face 0 cellPoint hsampleCell
  exact hcell.symm.trans hface

/-- Actual sample clearance supplies the incident-compatible fine-grid
selection required by the generic weighted prism identity. -/
theorem boxComplementarityFloorRefinementPrism_endpointWeightedSum_eq_of_cleared
    (problem : BoxComplementarityProblem (Fin n))
    (p k : ℕ) (hp : 0 < p) (hk : 0 < k)
    (region : Set (UnitCube (Fin n))) (hopen : IsOpen region) (radius : ℝ)
    (hmesh : 2 / (p : ℝ) ≤ radius)
    (hcleared : ¬HasFloorRefinementPrismFaceSampleIn problem
      (Metric.cthickening radius (frontier region)) p k) :
    (∑ endpoint : KuhnExternalEndpointSimplex
        (boxComplementarityFloorPullbackBoundaryLabeling problem p k hp hk)
          (Nat.mul_pos hp hk),
      (if boxComplementarityGridPoint (p * k) (endpoint.1 0) ∈ region
        then (1 : ℤ) else 0) * endpoint.signedWeight) =
    ∑ endpoint : KuhnExternalEndpointSimplex
        (boxComplementarityKuhnCubeBoundaryLabeling
          problem (p * k) (Nat.mul_pos hp hk)) (Nat.mul_pos hp hk),
      (if boxComplementarityGridPoint (p * k) (endpoint.1 0) ∈ region
        then (1 : ℤ) else 0) * endpoint.signedWeight := by
  let left := boxComplementarityFloorPullbackBoundaryLabeling
    problem p k hp hk
  let right := boxComplementarityKuhnCubeBoundaryLabeling
    problem (p * k) (Nat.mul_pos hp hk)
  let selection := fun vertex : Fin n → Fin (p * k + 1) ↦
    if boxComplementarityGridPoint (p * k) vertex ∈ region
    then (1 : ℤ) else 0
  have htransport := externalCubeLabelPrism_endpointWeightedSum_eq
    (Nat.mul_pos hp hk) left right selection (by
      intro cell face hincident
      apply if_congr _ rfl rfl
      exact floorRefinementPrismFace_parent_base_mem_iff_of_cleared
        problem p k hp hk region hopen radius hmesh hcleared
          face cell hincident)
  exact htransport

/-- The actual left prism face corresponding to a coarse endpoint through
the canonical floor lift. -/
def boxComplementarityFloorRefinementLeftFace
    (problem : BoxComplementarityProblem (Fin n))
    (p k : ℕ) (hp : 0 < p) (hk : 0 < k)
    (endpoint : KuhnEndpointLabeledSimplex problem p hp) :
    KuhnPrismFace n (p * k) (Nat.mul_pos hp hk)
      (boxComplementarityFloorRefinementPrism problem p k hp hk).label :=
  (externalCubeLabelPrismLeftEndEquiv (Nat.mul_pos hp hk)
    (boxComplementarityFloorPullbackBoundaryLabeling problem p k hp hk)
    (boxComplementarityKuhnCubeBoundaryLabeling
      problem (p * k) (Nat.mul_pos hp hk))).symm
      (boxComplementarityEndpointEquivFloorPullbackExternal
        problem p k hp hk endpoint) |>.1

/-- The actual right prism face corresponding to a fine box endpoint. -/
def boxComplementarityFloorRefinementRightFace
    (problem : BoxComplementarityProblem (Fin n))
    (p k : ℕ) (hp : 0 < p) (hk : 0 < k)
    (endpoint : KuhnEndpointLabeledSimplex
      problem (p * k) (Nat.mul_pos hp hk)) :
    KuhnPrismFace n (p * k) (Nat.mul_pos hp hk)
      (boxComplementarityFloorRefinementPrism problem p k hp hk).label :=
  (externalCubeLabelPrismRightEndEquiv (Nat.mul_pos hp hk)
    (boxComplementarityFloorPullbackBoundaryLabeling problem p k hp hk)
    (boxComplementarityKuhnCubeBoundaryLabeling
      problem (p * k) (Nat.mul_pos hp hk))).symm
      (kuhnEndpointLabeledSimplexEquivExternal
        problem (p * k) (Nat.mul_pos hp hk) endpoint) |>.1

theorem boxComplementarityFloorRefinementLeftFace_spatial
    (problem : BoxComplementarityProblem (Fin n))
    (p k : ℕ) (hp : 0 < p) (hk : 0 < k)
    (endpoint : KuhnEndpointLabeledSimplex problem p hp)
    (index : Fin (n + 1)) :
    Fin.init ((boxComplementarityFloorRefinementLeftFace
      problem p k hp hk endpoint).1 index) =
        (boxComplementarityEndpointEquivFloorPullbackExternal
          problem p k hp hk endpoint).1 index := by
  let left := boxComplementarityFloorPullbackBoundaryLabeling
    problem p k hp hk
  let right := boxComplementarityKuhnCubeBoundaryLabeling
    problem (p * k) (Nat.mul_pos hp hk)
  let lifted := boxComplementarityEndpointEquivFloorPullbackExternal
    problem p k hp hk endpoint
  let equivalence := externalCubeLabelPrismLeftEndEquiv
    (Nat.mul_pos hp hk) left right
  have h := congrFun
    (congrArg Subtype.val (equivalence.apply_symm_apply lifted)) index
  exact h

theorem boxComplementarityFloorRefinementRightFace_spatial
    (problem : BoxComplementarityProblem (Fin n))
    (p k : ℕ) (hp : 0 < p) (hk : 0 < k)
    (endpoint : KuhnEndpointLabeledSimplex
      problem (p * k) (Nat.mul_pos hp hk))
    (index : Fin (n + 1)) :
    Fin.init ((boxComplementarityFloorRefinementRightFace
      problem p k hp hk endpoint).1 index) = endpoint.1 index := by
  let left := boxComplementarityFloorPullbackBoundaryLabeling
    problem p k hp hk
  let right := boxComplementarityKuhnCubeBoundaryLabeling
    problem (p * k) (Nat.mul_pos hp hk)
  let external := kuhnEndpointLabeledSimplexEquivExternal
    problem (p * k) (Nat.mul_pos hp hk) endpoint
  let equivalence := externalCubeLabelPrismRightEndEquiv
    (Nat.mul_pos hp hk) left right
  have h := congrFun
    (congrArg Subtype.val (equivalence.apply_symm_apply external)) index
  exact h

theorem boxComplementarityFloorRefinementLeftFace_parameter
    (problem : BoxComplementarityProblem (Fin n))
    (p k : ℕ) (hp : 0 < p) (hk : 0 < k)
    (endpoint : KuhnEndpointLabeledSimplex problem p hp)
    (index : Fin (n + 1)) :
    (boxComplementarityFloorRefinementLeftFace
      problem p k hp hk endpoint).1 index (Fin.last n) = 0 := by
  let left := boxComplementarityFloorPullbackBoundaryLabeling
    problem p k hp hk
  let right := boxComplementarityKuhnCubeBoundaryLabeling
    problem (p * k) (Nat.mul_pos hp hk)
  let lifted := boxComplementarityEndpointEquivFloorPullbackExternal
    problem p k hp hk endpoint
  exact ((externalCubeLabelPrismLeftEndEquiv
    (Nat.mul_pos hp hk) left right).symm lifted).2 index

theorem boxComplementarityFloorRefinementRightFace_parameter_ne_zero
    (problem : BoxComplementarityProblem (Fin n))
    (p k : ℕ) (hp : 0 < p) (hk : 0 < k)
    (endpoint : KuhnEndpointLabeledSimplex
      problem (p * k) (Nat.mul_pos hp hk))
    (index : Fin (n + 1)) :
    (boxComplementarityFloorRefinementRightFace
      problem p k hp hk endpoint).1 index (Fin.last n) ≠ 0 := by
  let left := boxComplementarityFloorPullbackBoundaryLabeling
    problem p k hp hk
  let right := boxComplementarityKuhnCubeBoundaryLabeling
    problem (p * k) (Nat.mul_pos hp hk)
  let external := kuhnEndpointLabeledSimplexEquivExternal
    problem (p * k) (Nat.mul_pos hp hk) endpoint
  have htop : ((boxComplementarityFloorRefinementRightFace
      problem p k hp hk endpoint).1 index (Fin.last n)).1 = p * k := by
    exact ((externalCubeLabelPrismRightEndEquiv
      (Nat.mul_pos hp hk) left right).symm external).2 index
  intro heq
  have hzero := congrArg Fin.val heq
  simp only [Fin.val_zero] at hzero
  exact (Nat.mul_pos hp hk).ne' (htop.symm.trans hzero)

theorem boxComplementarityFloorRefinementLeftFace_sample
    (problem : BoxComplementarityProblem (Fin n))
    (p k : ℕ) (hp : 0 < p) (hk : 0 < k)
    (endpoint : KuhnEndpointLabeledSimplex problem p hp)
    (index : Fin (n + 1)) :
    boxComplementarityFloorRefinementLabelSamplePoint p k
      ((boxComplementarityFloorRefinementLeftFace
        problem p k hp hk endpoint).1 index) =
      boxComplementarityGridPoint p (endpoint.1 index) := by
  unfold boxComplementarityFloorRefinementLabelSamplePoint
  split_ifs with hparameter
  · apply congrArg (boxComplementarityGridPoint p)
    funext who
    have hspatial := congrFun
      (boxComplementarityFloorRefinementLeftFace_spatial
        problem p k hp hk endpoint index) who
    change
      (boxComplementarityFloorRefinementLeftFace
        problem p k hp hk endpoint).1 index who.castSucc =
          (boxComplementarityEndpointEquivFloorPullbackExternal
            problem p k hp hk endpoint).1 index who at hspatial
    rw [hspatial,
      boxComplementarityEndpointEquivFloorPullbackExternal_apply]
    have hfloor := kuhnFloorVertex_kuhnFloorSimplexLift
      (floorPullbackSpernerCube
        (boxComplementaritySpernerCube problem p hp) k hk)
      (boxComplementaritySpernerCube problem p hp) k rfl rfl hk
        endpoint.1 endpoint.2.1 index
    exact congrFun hfloor who
  · exact (hparameter (boxComplementarityFloorRefinementLeftFace_parameter
      problem p k hp hk endpoint index)).elim

theorem boxComplementarityFloorRefinementRightFace_sample
    (problem : BoxComplementarityProblem (Fin n))
    (p k : ℕ) (hp : 0 < p) (hk : 0 < k)
    (endpoint : KuhnEndpointLabeledSimplex
      problem (p * k) (Nat.mul_pos hp hk))
    (index : Fin (n + 1)) :
    boxComplementarityFloorRefinementLabelSamplePoint p k
      ((boxComplementarityFloorRefinementRightFace
        problem p k hp hk endpoint).1 index) =
      boxComplementarityGridPoint (p * k) (endpoint.1 index) := by
  unfold boxComplementarityFloorRefinementLabelSamplePoint
  split_ifs with hparameter
  · exact (boxComplementarityFloorRefinementRightFace_parameter_ne_zero
      problem p k hp hk endpoint index hparameter).elim
  · exact congrArg (boxComplementarityGridPoint (p * k))
      (boxComplementarityFloorRefinementRightFace_spatial
        problem p k hp hk endpoint index)

private theorem one_div_le_three_div
    (p : ℕ) (hp : 0 < p) :
    1 / (p : ℝ) ≤ 3 / (p : ℝ) := by
  have honeNonnegative : 0 ≤ 1 / (p : ℝ) := by positivity
  calc
    1 / (p : ℝ) ≤
        1 / (p : ℝ) + (1 / (p : ℝ) + 1 / (p : ℝ)) :=
      le_add_of_nonneg_right (add_nonneg honeNonnegative honeNonnegative)
    _ = 3 / (p : ℝ) := by ring

/-- With the actual mixed samples cleared from a three-coarse-mesh collar,
the existing anchor-selected signed count is preserved by factor refinement. -/
theorem boxComplementarityLocalSignedCount_floorRefinement_eq_of_cleared
    (problem : BoxComplementarityProblem (Fin n))
    (p k : ℕ) (hp : 0 < p) (hk : 0 < k)
    (region : Set (UnitCube (Fin n))) (hopen : IsOpen region) (radius : ℝ)
    (hmesh : 3 / (p : ℝ) ≤ radius)
    (hcleared : ¬HasFloorRefinementPrismFaceSampleIn problem
      (Metric.cthickening radius (frontier region)) p k) :
    boxComplementarityLocalSignedCount problem p hp region =
      boxComplementarityLocalSignedCount
        problem (p * k) (Nat.mul_pos hp hk) region := by
  have honeMesh : 1 / (p : ℝ) ≤ radius :=
    (one_div_le_three_div p hp).trans hmesh
  have htwoMesh : 2 / (p : ℝ) ≤ radius := by
    have honeNonnegative : 0 ≤ 1 / (p : ℝ) := by positivity
    calc
      2 / (p : ℝ) ≤ 3 / (p : ℝ) := by
        rw [show 2 / (p : ℝ) =
          1 / (p : ℝ) + 1 / (p : ℝ) by ring]
        rw [show 3 / (p : ℝ) =
          1 / (p : ℝ) + 1 / (p : ℝ) + 1 / (p : ℝ) by ring]
        exact le_add_of_nonneg_right honeNonnegative
      _ ≤ radius := hmesh
  have hcoarseAgrees
      (endpoint : KuhnEndpointLabeledSimplex problem p hp)
      (first second : Fin (n + 1)) :
      boxComplementarityGridPoint p (endpoint.1 first) ∈ region ↔
        boxComplementarityGridPoint p (endpoint.1 second) ∈ region := by
    let face := boxComplementarityFloorRefinementLeftFace
      problem p k hp hk endpoint
    have hnear := floorRefinementPrismFace_sample_mem_iff_nearby_of_cleared
      problem p k hp hk region hopen radius hcleared face first
        (boxComplementarityFloorRefinementLabelSamplePoint
          p k (face.1 second))
        ((dist_floorRefinementPrismFace_labelSamplePoints_le_three_div
          problem p k hp hk face first second).trans hmesh)
    convert hnear using 1
    all_goals first | rfl |
      (simp only [face, boxComplementarityFloorRefinementLeftFace_sample]; rfl)
  have hfineAgrees
      (endpoint : KuhnEndpointLabeledSimplex
        problem (p * k) (Nat.mul_pos hp hk))
      (first second : Fin (n + 1)) :
      boxComplementarityGridPoint (p * k) (endpoint.1 first) ∈ region ↔
        boxComplementarityGridPoint (p * k) (endpoint.1 second) ∈ region := by
    let face := boxComplementarityFloorRefinementRightFace
      problem p k hp hk endpoint
    have hnear := floorRefinementPrismFace_sample_mem_iff_nearby_of_cleared
      problem p k hp hk region hopen radius hcleared face first
        (boxComplementarityFloorRefinementLabelSamplePoint
          p k (face.1 second))
        ((dist_floorRefinementPrismFace_labelSamplePoints_le_three_div
          problem p k hp hk face first second).trans hmesh)
    convert hnear using 1
    all_goals first | rfl |
      (simp only [face, boxComplementarityFloorRefinementRightFace_sample]; rfl)
  have hleftSelection
      (endpoint : KuhnEndpointLabeledSimplex problem p hp) :
      boxComplementarityGridPoint p (endpoint.1 0) ∈ region ↔
        boxComplementarityGridPoint (p * k)
          ((boxComplementarityEndpointEquivFloorPullbackExternal
            problem p k hp hk endpoint).1 0) ∈ region := by
    let face := boxComplementarityFloorRefinementLeftFace
      problem p k hp hk endpoint
    have hdistance := dist_floorRefinementLabelSamplePoint_fine_le_one_div
      p k hp hk (face.1 0)
    have hspatial := boxComplementarityFloorRefinementLeftFace_spatial
      problem p k hp hk endpoint 0
    have hdistance' : dist
        (boxComplementarityFloorRefinementLabelSamplePoint p k (face.1 0))
        (boxComplementarityGridPoint (p * k)
          ((boxComplementarityEndpointEquivFloorPullbackExternal
            problem p k hp hk endpoint).1 0)) ≤ radius := by
      rw [← hspatial]
      exact hdistance.trans honeMesh
    have hnear := floorRefinementPrismFace_sample_mem_iff_nearby_of_cleared
      problem p k hp hk region hopen radius hcleared face 0 _ hdistance'
    convert hnear using 1
    all_goals first | rfl |
      (simp only [face, boxComplementarityFloorRefinementLeftFace_sample]; rfl)
  rw [boxComplementarityLocalSignedCount_eq_endpoint_base_sum
      problem p hp region hcoarseAgrees,
    boxComplementarityLocalSignedCount_eq_endpoint_base_sum
      problem (p * k) (Nat.mul_pos hp hk) region hfineAgrees]
  have hleft :
      (∑ endpoint : KuhnEndpointLabeledSimplex problem p hp,
        if boxComplementarityGridPoint p (endpoint.1 0) ∈ region
        then endpoint.signedWeight else 0) =
      ∑ endpoint : KuhnExternalEndpointSimplex
          (boxComplementarityFloorPullbackBoundaryLabeling
            problem p k hp hk) (Nat.mul_pos hp hk),
        (if boxComplementarityGridPoint (p * k) (endpoint.1 0) ∈ region
          then (1 : ℤ) else 0) * endpoint.signedWeight := by
    apply Fintype.sum_equiv
      (boxComplementarityEndpointEquivFloorPullbackExternal
        problem p k hp hk)
    intro endpoint
    rw [boxComplementarityEndpointEquivFloorPullbackExternal_signedWeight]
    rw [if_congr (hleftSelection endpoint) rfl rfl]
    simp only [ite_mul, one_mul, zero_mul]
  have hright :
      (∑ endpoint : KuhnEndpointLabeledSimplex
          problem (p * k) (Nat.mul_pos hp hk),
        if boxComplementarityGridPoint (p * k) (endpoint.1 0) ∈ region
        then endpoint.signedWeight else 0) =
      ∑ endpoint : KuhnExternalEndpointSimplex
          (boxComplementarityKuhnCubeBoundaryLabeling
            problem (p * k) (Nat.mul_pos hp hk)) (Nat.mul_pos hp hk),
        (if boxComplementarityGridPoint (p * k) (endpoint.1 0) ∈ region
          then (1 : ℤ) else 0) * endpoint.signedWeight := by
    apply Fintype.sum_equiv
      (kuhnEndpointLabeledSimplexEquivExternal
        problem (p * k) (Nat.mul_pos hp hk))
    intro endpoint
    rw [kuhnEndpointLabeledSimplexEquivExternal_signedWeight]
    have hvertices :
        (kuhnEndpointLabeledSimplexEquivExternal
          problem (p * k) (Nat.mul_pos hp hk) endpoint).1 = endpoint.1 := rfl
    have hpoint : boxComplementarityGridPoint (p * k)
        ((kuhnEndpointLabeledSimplexEquivExternal
          problem (p * k) (Nat.mul_pos hp hk) endpoint).1 0) =
        boxComplementarityGridPoint (p * k) (endpoint.1 0) :=
      congrArg (fun vertices ↦
        boxComplementarityGridPoint (p * k) (vertices 0)) hvertices
    have hmembership :
        boxComplementarityGridPoint (p * k) (endpoint.1 0) ∈ region ↔
        boxComplementarityGridPoint (p * k)
          ((kuhnEndpointLabeledSimplexEquivExternal
            problem (p * k) (Nat.mul_pos hp hk) endpoint).1 0) ∈ region := by
      rw [hpoint]
      exact Iff.rfl
    by_cases hexternal : boxComplementarityGridPoint (p * k)
        ((kuhnEndpointLabeledSimplexEquivExternal
          problem (p * k) (Nat.mul_pos hp hk) endpoint).1 0) ∈ region
    · rw [if_pos (hmembership.mpr hexternal), if_pos hexternal, one_mul]
    · have hbase : boxComplementarityGridPoint (p * k)
          (endpoint.1 0) ∉ region := fun h ↦ hexternal (hmembership.mp h)
      rw [if_neg hbase, if_neg hexternal, zero_mul]
  exact hleft.trans
    ((boxComplementarityFloorRefinementPrism_endpointWeightedSum_eq_of_cleared
      problem p k hp hk region hopen radius htwoMesh hcleared).trans hright.symm)

/-- One threshold works for every positive refinement factor: beyond it, the
existing local signed count at `p` equals the count at `p * k`. -/
theorem BoxComplementarityProblem.eventually_localSignedCount_floorRefinement_eq
    (problem : BoxComplementarityProblem (Fin n))
    (region : Set (UnitCube (Fin n)))
    (hisolating : problem.IsIsolating region) :
    ∃ threshold, ∀ p k, threshold ≤ p → ∀ hp : 0 < p, ∀ hk : 0 < k,
      boxComplementarityLocalSignedCount problem p hp region =
        boxComplementarityLocalSignedCount
          problem (p * k) (Nat.mul_pos hp hk) region := by
  obtain ⟨radius, hradius, collarThreshold, hcleared⟩ :=
    problem.exists_isolatingFrontierCollar_eventually_floorRefinementCleared
      region hisolating
  have hpReal : Tendsto (fun p : ℕ ↦ (p : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  have hinverse : Tendsto (fun p : ℕ ↦ (p : ℝ)⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp hpReal
  have hthree : Tendsto (fun _ : ℕ ↦ (3 : ℝ)) atTop (nhds 3) :=
    tendsto_const_nhds
  have hmeshZero : Tendsto (fun p : ℕ ↦ 3 / (p : ℝ)) atTop (nhds 0) := by
    simpa only [div_eq_mul_inv, mul_zero] using hthree.mul hinverse
  obtain ⟨meshThreshold, hmesh⟩ :=
    eventually_atTop.1 (hmeshZero.eventually (eventually_lt_nhds hradius))
  refine ⟨max collarThreshold meshThreshold, ?_⟩
  intro p k hpFine hp hk
  exact boxComplementarityLocalSignedCount_floorRefinement_eq_of_cleared
    problem p k hp hk region hisolating.1 radius
      (hmesh p ((le_max_right _ _).trans hpFine)).le
      (hcleared p k ((le_max_left _ _).trans hpFine))

/-- Consequently the existing anchor-selected integer count is independent
of any two sufficiently fine positive resolutions. -/
theorem BoxComplementarityProblem.eventually_localSignedCount_eq
    (problem : BoxComplementarityProblem (Fin n))
    (region : Set (UnitCube (Fin n)))
    (hisolating : problem.IsIsolating region) :
    ∃ threshold, ∀ p q, threshold ≤ p → threshold ≤ q →
      ∀ hp : 0 < p, ∀ hq : 0 < q,
        boxComplementarityLocalSignedCount problem p hp region =
          boxComplementarityLocalSignedCount problem q hq region := by
  obtain ⟨threshold, hrefinement⟩ :=
    problem.eventually_localSignedCount_floorRefinement_eq region hisolating
  refine ⟨threshold, ?_⟩
  intro p q hpFine hqFine hp hq
  have hpq := hrefinement p q hpFine hp hq
  have hqp := hrefinement q p hqFine hq hp
  exact hpq.trans (by
    simpa only [Nat.mul_comm] using hqp.symm)

/-- On the whole cube, the existing floor comparison works starting at mesh one. -/
theorem boxComplementarityLocalSignedCount_univ_eq_resolution_one
    (problem : BoxComplementarityProblem (Fin n)) (p : ℕ) (hp : 0 < p) :
    boxComplementarityLocalSignedCount problem p hp univ =
      boxComplementarityLocalSignedCount problem 1 (by omega) univ := by
  have h := boxComplementarityLocalSignedCount_floorRefinement_eq_of_cleared
    problem 1 p (by omega) hp univ isOpen_univ 3 (by norm_num) (by
      simp [HasFloorRefinementPrismFaceSampleIn])
  simpa only [one_mul] using h.symm

end Math
