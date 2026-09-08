import MathUE.Topology.KuhnSimplexGeometry

/-!
# Actual finite incidence of ordered Kuhn simplices

The cell, complete-face, deletion, and parent equivalences are the generic
cube form of the existing concrete prism incidence. They retain literal
vertices and deletion indices. No incidence cardinality or chain algebra is
reproved here.
-/

noncomputable section

namespace Math.KuhnSimplex

open Classical

/-- The pinned dimension-indexed insertion is the ordinary order-preserving
deletion embedding after the explicit dimension cast. -/
theorem insertIndex_eq_succAbove_cast
    (cube : SpernerCube) {dimension : ℕ} (hdimension : dimension + 1 = cube.n)
    (omitted : Fin (cube.n + 1)) (kept : Fin (dimension + 1)) :
    @insert_index cube dimension hdimension omitted kept =
      omitted.succAbove (Fin.cast hdimension kept) := by
  apply Fin.ext
  by_cases hlt : kept.val < omitted.val
  · simp [insert_index, Fin.succAbove, hlt, Fin.lt_def]
  · simp [insert_index, Fin.succAbove, hlt, Fin.lt_def]

/-- A literal top-dimensional ordered Kuhn simplex. -/
def Cell (cube : SpernerCube) :=
  {vertices : Fin (cube.n + 1) → cube.G // simplex cube cube.n vertices}

/-- A literal ordered face with an injective external finite label sequence. -/
def CompleteFace (cube : SpernerCube) (dimension : ℕ)
    (label : cube.G → Fin (dimension + 1)) :=
  {vertices : Fin (dimension + 1) → cube.G // simplex cube dimension vertices ∧
    Function.Injective fun index => label (vertices index)}

instance cellFinite (cube : SpernerCube) : Finite (Cell cube) :=
  Finite.of_injective (fun cell => cell.1) Subtype.val_injective

instance cellFintype (cube : SpernerCube) : Fintype (Cell cube) := Fintype.ofFinite _

instance completeFaceFinite (cube : SpernerCube) (dimension : ℕ)
    (label : cube.G → Fin (dimension + 1)) : Finite (CompleteFace cube dimension label) :=
  Finite.of_injective (fun face => face.1) Subtype.val_injective

instance completeFaceFintype (cube : SpernerCube) (dimension : ℕ)
    (label : cube.G → Fin (dimension + 1)) : Fintype (CompleteFace cube dimension label) :=
  Fintype.ofFinite _

/-- Incidence is the pinned actual face relation, not supplied combinatorial data. -/
def Incident {cube : SpernerCube} {dimension : ℕ}
    {label : cube.G → Fin (dimension + 1)} (cell : Cell cube)
    (face : CompleteFace cube dimension label) : Prop := is_face cube face.1 cell.1

/-- Complete deletion retains the pinned deletion map and its dimension witness. -/
def CompleteDeletion {cube : SpernerCube} {dimension : ℕ}
    (hdimension : dimension + 1 = cube.n) (label : cube.G → Fin (dimension + 1))
    (cell : Cell cube) (omitted : Fin (cube.n + 1)) : Prop :=
  Function.Injective fun kept =>
    label (@delete_vertex cube dimension hdimension omitted cell.1 kept)

/-- Delete a vertex whose remaining labels are complete. -/
def Cell.deletionFace {cube : SpernerCube} {dimension : ℕ}
    (hdimension : dimension + 1 = cube.n) (label : cube.G → Fin (dimension + 1))
    (cell : Cell cube) (omitted : {index // CompleteDeletion hdimension label cell index}) :
    CompleteFace cube dimension label where
  val := @delete_vertex cube dimension hdimension omitted.1 cell.1
  property := ⟨@delete_vertex_simplex cube dimension hdimension cell.1 cell.2 omitted.1,
    omitted.2⟩

/-- A deletion face is incident to its originating cell. -/
theorem Cell.deletionFace_incident {cube : SpernerCube} {dimension : ℕ}
    (hdimension : dimension + 1 = cube.n) (label : cube.G → Fin (dimension + 1))
    (cell : Cell cube) (omitted : {index // CompleteDeletion hdimension label cell index}) :
    Incident cell (cell.deletionFace hdimension label omitted) :=
  @delete_vertex_is_face cube dimension hdimension cell.1 cell.2 omitted.1

/-- Complete deletions of an actual cell are exactly its incident complete faces. -/
def Cell.completeDeletionEquivIncidentFace {cube : SpernerCube} {dimension : ℕ}
    (hdimension : dimension + 1 = cube.n) (label : cube.G → Fin (dimension + 1))
    (cell : Cell cube) :
    {index // CompleteDeletion hdimension label cell index} ≃
      {face : CompleteFace cube dimension label // Incident cell face} := by
  let forward : {index // CompleteDeletion hdimension label cell index} →
      {face : CompleteFace cube dimension label // Incident cell face} :=
    fun omitted => ⟨cell.deletionFace hdimension label omitted,
      cell.deletionFace_incident hdimension label omitted⟩
  refine Equiv.ofBijective forward ⟨?_, ?_⟩
  · intro first second heq
    apply Subtype.ext
    apply @delete_vertex_inj cube dimension hdimension cell.1 cell.2
    exact congrArg (fun face => face.1.1) heq
  · rintro ⟨face, hface⟩
    obtain ⟨omitted, homitted⟩ :=
      (@child_simplex_char cube dimension hdimension face.1 cell.1 cell.2).mp hface
    have hcomplete : CompleteDeletion hdimension label cell omitted := by
      intro first second heq
      apply face.2.2
      simpa only [homitted] using heq
    let selected : {index // CompleteDeletion hdimension label cell index} :=
      ⟨omitted, hcomplete⟩
    refine ⟨selected, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    exact homitted.symm

/-- Incident cells are literally the pinned parents, retaining their simplex proof. -/
def CompleteFace.incidentCellEquivParent {cube : SpernerCube} {dimension : ℕ}
    {label : cube.G → Fin (dimension + 1)} (face : CompleteFace cube dimension label) :
    {cell : Cell cube // Incident cell face} ≃
      {vertices : Fin (cube.n + 1) → cube.G // is_face cube face.1 vertices} where
  toFun cell := ⟨cell.1.1, cell.2⟩
  invFun parent := ⟨⟨parent.1, parent.2.2.1⟩, parent.2⟩
  left_inv := by rintro ⟨⟨vertices, hvertices⟩, hincident⟩; rfl
  right_inv := by rintro ⟨vertices, hincident⟩; rfl

/-- Actual incident-cell cardinality is the pinned parent cardinality. -/
theorem CompleteFace.incidentCell_card_eq_parent_card
    {cube : SpernerCube} {dimension : ℕ} {label : cube.G → Fin (dimension + 1)}
    (face : CompleteFace cube dimension label) :
    (Finset.univ.filter fun cell : Cell cube => Incident cell face).card =
      (Finset.univ.filter fun vertices : Fin (cube.n + 1) → cube.G =>
        is_face cube face.1 vertices).card := by
  classical
  simpa only [Fintype.card_subtype] using
    Fintype.card_congr face.incidentCellEquivParent

end Math.KuhnSimplex
