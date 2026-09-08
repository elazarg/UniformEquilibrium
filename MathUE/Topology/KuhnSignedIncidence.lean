import MathUE.Topology.KuhnSimplexIncidence
import MathUE.Topology.SignedSimplexLabelBoundary
import MathUE.Topology.OrientedSimplexFacetDeterminant

/-!
# Integer weights of actual ordered-Kuhn incidences

The existing complete-deletion equivalence supplies the unique literal
omission for an incident face. Its geometric and label determinants define
the signed weight. The existing integer deletion-boundary identity then
transports to the actual incident-face sum.
-/

noncomputable section

namespace Math.KuhnSimplex

open Classical OrientedSimplexFacet

variable {cube : SpernerCube} {dimension : ℕ}
  (hdimension : dimension + 1 = cube.n) (label : cube.G → Fin (dimension + 1))

/-- The existing incidence equivalence supplies its literal complete deletion. -/
def Cell.incidentDeletion (cell : Cell cube) (face : CompleteFace cube dimension label)
    (hincident : Incident cell face) :
    {index // CompleteDeletion hdimension label cell index} :=
  (cell.completeDeletionEquivIncidentFace hdimension label).symm ⟨face, hincident⟩

/-- The selected actual deletion recovers the supplied face, not only its range. -/
theorem Cell.deletionFace_incidentDeletion (cell : Cell cube)
    (face : CompleteFace cube dimension label) (hincident : Incident cell face) :
    cell.deletionFace hdimension label
      (cell.incidentDeletion hdimension label face hincident) = face :=
  congrArg Subtype.val
    ((cell.completeDeletionEquivIncidentFace hdimension label).apply_symm_apply
      ⟨face, hincident⟩)

/-- Integer signed incidence is zero off actual incidence. -/
def signedIncidence (cell : Cell cube) (face : CompleteFace cube dimension label) : ℤ :=
  if hincident : Incident cell face then
    determinant (fun vertex coordinate => ((cell.1 vertex coordinate).val : ℤ)) *
      (-1) ^ (cell.incidentDeletion hdimension label face hincident).1.val *
        SignedSimplexLabel.orientation (fun vertex => label (face.1 vertex))
  else 0

/-- The incidence weight uses the literal omission supplied by the existing equivalence. -/
theorem signedIncidence_deletionFace (cell : Cell cube)
    (omitted : {index // CompleteDeletion hdimension label cell index}) :
    signedIncidence hdimension label cell (cell.deletionFace hdimension label omitted) =
      determinant (fun vertex coordinate => ((cell.1 vertex coordinate).val : ℤ)) *
        (-1) ^ omitted.1.val * SignedSimplexLabel.orientation
          (fun vertex =>
            label (@delete_vertex cube dimension hdimension omitted.1 cell.1 vertex)) := by
  have hincident := cell.deletionFace_incident hdimension label omitted
  have hinverse : cell.incidentDeletion hdimension label
      (cell.deletionFace hdimension label omitted) hincident = omitted :=
    (cell.completeDeletionEquivIncidentFace hdimension label).symm_apply_apply omitted
  simp only [signedIncidence, dif_pos hincident, hinverse]
  rfl

/-- Any literal deletion equality identifies the same signed incidence weight. -/
theorem signedIncidence_eq_of_face_eq_delete (cell : Cell cube)
    (face : CompleteFace cube dimension label) (omitted : Fin (cube.n + 1))
    (hface : face.1 = @delete_vertex cube dimension hdimension omitted cell.1) :
    signedIncidence hdimension label cell face =
      determinant (fun vertex coordinate => ((cell.1 vertex coordinate).val : ℤ)) *
        (-1) ^ omitted.val *
          SignedSimplexLabel.orientation (fun vertex => label (face.1 vertex)) := by
  have hcomplete : CompleteDeletion hdimension label cell omitted := by
    intro first second heq
    apply face.2.2
    simpa only [hface] using heq
  have hequal : cell.deletionFace hdimension label ⟨omitted, hcomplete⟩ = face :=
    Subtype.ext hface.symm
  rw [← hequal]
  exact signedIncidence_deletionFace hdimension label cell ⟨omitted, hcomplete⟩

/-- The integer deletion identity transports through the actual incidence equivalence. -/
theorem sum_signedIncidence_incidentFaces_eq_zero (cell : Cell cube) :
    (∑ face : {face : CompleteFace cube dimension label // Incident cell face},
      signedIncidence hdimension label cell face.1) = 0 := by
  have hequiv := Fintype.sum_equiv
    (cell.completeDeletionEquivIncidentFace hdimension label)
    (fun omitted => signedIncidence hdimension label cell
      (cell.deletionFace hdimension label omitted))
    (fun face => signedIncidence hdimension label cell face.1) (fun _ => rfl)
  rw [← hequiv]
  simp_rw [signedIncidence_deletionFace]
  rcases cube with ⟨ambient, resolution, cubeLabel, hcubeLabel⟩
  cases hdimension
  let labels : Fin (dimension + 2) → Fin (dimension + 1) := fun vertex => label (cell.1 vertex)
  have hsum : (∑ omitted : {index // CompleteDeletion rfl label cell index},
      SignedSimplexLabel.deletionWeight labels omitted.1) = 0 := by
    rw [← Finset.sum_subtype (Finset.univ.filter (CompleteDeletion rfl label cell))
      (by intro index; simp) (SignedSimplexLabel.deletionWeight labels)]
    convert SignedSimplexLabel.sum_complete_deletionWeight_eq_zero labels using 1
    congr 1
    ext index
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, CompleteDeletion,
      delete_vertex, insertIndex_eq_succAbove_cast, Fin.cast_refl, id_eq, labels]
  have hterm (omitted : {index // CompleteDeletion rfl label cell index}) :
      (-1 : ℤ) ^ omitted.1.val * SignedSimplexLabel.orientation
        (fun vertex => label (@delete_vertex _ dimension rfl omitted.1 cell.1 vertex)) =
      SignedSimplexLabel.deletionWeight labels omitted.1 := by
    simp only [SignedSimplexLabel.deletionWeight, labels, delete_vertex,
      insertIndex_eq_succAbove_cast, Fin.cast_refl, id_eq]
  simp_rw [mul_assoc, hterm]
  rw [← Finset.mul_sum, hsum, mul_zero]

/-- The full finite face sum is zero; nonincident faces contribute zero by definition. -/
theorem sum_signedIncidence_faces_eq_zero (cell : Cell cube) :
    (∑ face : CompleteFace cube dimension label,
      signedIncidence hdimension label cell face) = 0 := by
  have hsum := sum_signedIncidence_incidentFaces_eq_zero hdimension label cell
  rw [← Finset.sum_subtype (Finset.univ.filter (Incident cell))
    (by intro face; simp) (signedIncidence hdimension label cell)] at hsum
  rw [Finset.sum_filter] at hsum
  convert hsum using 1
  apply Finset.sum_congr rfl
  intro face _
  by_cases hincident : Incident cell face <;> simp [signedIncidence, hincident]

end Math.KuhnSimplex
