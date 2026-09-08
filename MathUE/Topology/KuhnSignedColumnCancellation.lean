import MathUE.Topology.KuhnSignedIncidence
import MathUE.Topology.KuhnSharedFaceOrientation

/-!
# Integer cancellation in actual Kuhn incidence columns

Distinct parents of one complete face have opposite signed weights. The
pinned exact parent count then makes every nonboundary face column vanish.
No parent existence, cardinality, or double-counting theorem is reproved.
-/

noncomputable section

namespace Math.KuhnSimplex

open Classical OrientedSimplexFacet

variable {cube : SpernerCube} {dimension : ℕ}
  (hdimension : dimension + 1 = cube.n) (label : cube.G → Fin (dimension + 1))

/-- Two distinct actual parents have opposite signed weights at their common face. -/
theorem signedIncidence_add_eq_zero_of_distinct_parents
    (first second : Cell cube) (face : CompleteFace cube dimension label)
    (hfirst : Incident first face) (hsecond : Incident second face) (hne : first ≠ second) :
    signedIncidence hdimension label first face +
      signedIncidence hdimension label second face = 0 := by
  have hvertices : first.1 ≠ second.1 := fun h => hne (Subtype.ext h)
  obtain ⟨firstIndex, secondIndex, hfirstFace, hsecondFace, hcancel⟩ :=
    KuhnSharedFace.exists_sharedFace_signed_determinant_cancellation
      cube hdimension face.1 first.1 second.1 hfirst hsecond hvertices
  rw [signedIncidence_eq_of_face_eq_delete hdimension label first face firstIndex hfirstFace,
    signedIncidence_eq_of_face_eq_delete hdimension label second face secondIndex hsecondFace]
  have h := congrArg
    (fun value : ℤ => value * SignedSimplexLabel.orientation (fun vertex => label (face.1 vertex)))
    hcancel
  simp only [add_mul, zero_mul] at h
  convert h using 1
  ring

/-- A finite column sum restricts to actual incident parents, with zero elsewhere. -/
theorem sum_signedIncidence_cells_eq_incident_sum
    (face : CompleteFace cube dimension label) :
    (∑ cell : Cell cube, signedIncidence hdimension label cell face) =
      ∑ cell ∈ Finset.univ.filter (fun cell : Cell cube => Incident cell face),
        signedIncidence hdimension label cell face := by
  symm
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro cell _ hnot
  have hincident : ¬ Incident cell face := by simpa only [Finset.mem_filter,
    Finset.mem_univ, true_and] using hnot
  simp only [signedIncidence, dif_neg hincident]

/-- Every actual nonboundary face has zero integer incidence column. -/
theorem sum_signedIncidence_cells_eq_zero_of_not_boundary
    (face : CompleteFace cube dimension label) (hboundary : ¬ is_boundary_face cube face.1) :
    (∑ cell : Cell cube, signedIncidence hdimension label cell face) = 0 := by
  let parents := Finset.univ.filter (fun cell : Cell cube => Incident cell face)
  have hcount : parents.card = 1 ∨ parents.card = 2 := by
    dsimp only [parents]
    rw [face.incidentCell_card_eq_parent_card]
    exact @parent_count cube dimension hdimension face.1 face.2.1
  have hnotone : parents.card ≠ 1 := by
    intro hone
    apply hboundary
    rw [is_boundary_face, Fintype.existsUnique_iff_card_one]
    rw [← face.incidentCell_card_eq_parent_card]
    exact hone
  have htwo : parents.card = 2 := hcount.resolve_left hnotone
  obtain ⟨first, second, hne, hparents⟩ := Finset.card_eq_two.mp htwo
  have hfirst : Incident first face := by
    have hmem : first ∈ parents := by rw [hparents]; simp
    exact (Finset.mem_filter.mp hmem).2
  have hsecond : Incident second face := by
    have hmem : second ∈ parents := by rw [hparents]; simp
    exact (Finset.mem_filter.mp hmem).2
  rw [sum_signedIncidence_cells_eq_incident_sum]
  change (∑ cell ∈ parents, signedIncidence hdimension label cell face) = 0
  rw [hparents, Finset.sum_pair hne]
  exact signedIncidence_add_eq_zero_of_distinct_parents hdimension label
    first second face hfirst hsecond hne

end Math.KuhnSimplex
