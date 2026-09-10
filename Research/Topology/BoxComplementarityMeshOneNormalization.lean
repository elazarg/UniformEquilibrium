import Research.Topology.BoxComplementarityStabilizedLocalDegree
import Mathlib.LinearAlgebra.Matrix.Block

/-!
# Whole-cube normalization of the actual signed Kuhn count

The sole complete mesh-one simplex is the reverse-coordinate corner chain.
Its geometric-times-label weight is `(-1)^n`. Existing exact floor transport
then supplies this value at every positive mesh and for the raw stabilized
degree. The public local degree includes the explicit dimension-dependent
calibration and has whole-cube value one. No ambient Brouwer adapter or
invertible-affine local comparison is asserted.
-/

noncomputable section

namespace Math

open Classical Set

variable {n : ℕ}

/-- At mesh one, a coordinate carrying its own label is the upper endpoint. -/
theorem boxComplementarityReducedLabel_one_coordinate_eq_one
    (problem : BoxComplementarityProblem (Fin n))
    (vertex : Fin n → Fin 2) (who : Fin n)
    (hlabel : boxComplementarityReducedLabel problem 1 vertex = who.val) :
    vertex who = 1 := by
  have hne := boxComplementarityReducedLabel_ne_of_eq_zero problem 1 vertex who
  have hnonzero : vertex who ≠ 0 := fun hzero => hne hzero hlabel
  apply Fin.ext
  have hbound := (vertex who).isLt
  have hpositive : (vertex who).val ≠ 0 := fun hzero => hnonzero (Fin.ext hzero)
  change (vertex who).val = 1
  omega

/-- Mesh-one labels are the least upper-endpoint coordinate, or the extra label. -/
theorem boxComplementarityReducedLabel_one_eq_iff
    (problem : BoxComplementarityProblem (Fin n))
    (vertex : Fin n → Fin 2) (label : Fin (n + 1)) :
    boxComplementarityReducedLabel problem 1 vertex = label.val ↔
      (∀ who : Fin n, who.val < label.val → vertex who = 0) ∧
      (∀ who : Fin n, who.val = label.val → vertex who = 1) := by
  constructor
  · intro hlabel
    constructor
    · intro who hlt
      apply Fin.ext
      by_contra hne
      have hone : (vertex who).val = 1 := by have := (vertex who).isLt; omega
      have hle := boxComplementarityReducedLabel_le_of_eq_last
        problem 1 (by omega) vertex who hone
      rw [hlabel] at hle
      change (vertex who).val ≠ 0 at hne
      omega
    · intro who heq
      exact boxComplementarityReducedLabel_one_coordinate_eq_one
        problem vertex who (hlabel.trans heq.symm)
  · rintro ⟨hzero, hone⟩
    have hbound := (boxComplementarityReducedLabel_properties problem 1 vertex).1
    have hle : boxComplementarityReducedLabel problem 1 vertex ≤ label.val := by
      by_cases hlt : label.val < n
      · exact boxComplementarityReducedLabel_le_of_eq_last problem 1 (by omega)
          vertex ⟨label.val, hlt⟩ (congrArg Fin.val (hone ⟨label.val, hlt⟩ rfl))
      · omega
    apply le_antisymm hle
    by_contra hnot
    have hlt : boxComplementarityReducedLabel problem 1 vertex < label.val := by omega
    let who : Fin n := ⟨boxComplementarityReducedLabel problem 1 vertex, by omega⟩
    have hcoord := boxComplementarityReducedLabel_one_coordinate_eq_one
      problem vertex who rfl
    have hcoordZero := hzero who hlt
    rw [hcoordZero] at hcoord
    exact zero_ne_one hcoord

/-- Reverse-coordinate corner chain of the mesh-one cube. -/
def boxComplementarityMeshOneCornerChain (n : ℕ) : Fin (n + 1) → Fin n → Fin 2 :=
  fun index who => if n ≤ who.val + index.val then 1 else 0

/-- The actual mesh-one labels of the corner chain are in reverse order. -/
theorem boxComplementarityFinLabel_meshOneCornerChain
    (problem : BoxComplementarityProblem (Fin n)) (index : Fin (n + 1)) :
    boxComplementarityFinLabel problem 1
      (boxComplementarityMeshOneCornerChain n index) = Fin.rev index := by
  apply Fin.ext
  apply (boxComplementarityReducedLabel_one_eq_iff problem _ _).2
  constructor
  · intro who hlt
    have hindex := index.isLt
    simp only [Fin.val_rev] at hlt
    unfold boxComplementarityMeshOneCornerChain
    rw [if_neg (by omega)]
  · intro who heq
    have hindex := index.isLt
    simp only [Fin.val_rev] at heq
    unfold boxComplementarityMeshOneCornerChain
    rw [if_pos (by omega)]

/-- Along a mesh-one simplex, the actual finite labels are antitone. -/
theorem boxComplementarityFinLabel_antitone_of_meshOneSimplex
    (problem : BoxComplementarityProblem (Fin n))
    (vertices : Fin (n + 1) → Fin n → Fin 2)
    (hsimplex : simplex (boxComplementaritySpernerCube problem 1 (by omega)) n vertices) :
    Antitone (fun index => boxComplementarityFinLabel problem 1 (vertices index)) := by
  intro first second hle
  change boxComplementarityReducedLabel problem 1 (vertices second) ≤
    boxComplementarityReducedLabel problem 1 (vertices first)
  by_cases hlt : boxComplementarityReducedLabel problem 1 (vertices first) < n
  · let who : Fin n := ⟨boxComplementarityReducedLabel problem 1 (vertices first), hlt⟩
    have hone := boxComplementarityReducedLabel_one_coordinate_eq_one
      problem (vertices first) who rfl
    have hmono := spernerSimplex_val_le_of_le hsimplex hle who
    rw [hone] at hmono
    have htop : (vertices second who).val = 1 := by
      have := (vertices second who).isLt
      change 1 ≤ (vertices second who).val at hmono
      omega
    exact boxComplementarityReducedLabel_le_of_eq_last
      problem 1 (by omega) (vertices second) who htop
  · have hbound := (boxComplementarityReducedLabel_properties
      problem 1 (vertices second)).1
    omega

/-- Completeness forces the mesh-one labels into the full reverse order. -/
theorem boxComplementarityFinLabel_eq_rev_of_meshOneCompleteSimplex
    (problem : BoxComplementarityProblem (Fin n))
    (vertices : Fin (n + 1) → Fin n → Fin 2)
    (hcomplete : complete_simplex
      (boxComplementaritySpernerCube problem 1 (by omega)) n vertices)
    (index : Fin (n + 1)) :
    boxComplementarityFinLabel problem 1 (vertices index) = Fin.rev index := by
  have hinjective := (boxComplementarity_completeSimplex_iff_finLabel_injective
    problem 1 (by omega) vertices).1 hcomplete |>.2
  have hstrict := (boxComplementarityFinLabel_antitone_of_meshOneSimplex
    problem vertices hcomplete.1).strictAnti_of_injective hinjective
  let f : Fin (n + 1) → ℕ :=
    fun j => (Fin.rev (boxComplementarityFinLabel problem 1 (vertices j))).val
  have hf : StrictMono f := Fin.val_strictMono.comp (Fin.rev_strictAnti.comp hstrict)
  have hlow := le_apply_of_strictMono_fin hf index
  have hhigh := apply_add_le_last_of_strictMono_fin hf index
  have hlast : f (Fin.last n) < n + 1 :=
    (Fin.rev (boxComplementarityFinLabel problem 1 (vertices (Fin.last n)))).isLt
  have hindex : f index = index.val := by have := index.isLt; omega
  have hrev : Fin.rev (boxComplementarityFinLabel problem 1 (vertices index)) = index :=
    Fin.ext hindex
  exact (Fin.rev_eq_iff).1 hrev

/-- The literal reverse-coordinate chain is the only complete mesh-one tuple. -/
theorem eq_meshOneCornerChain_of_completeSimplex
    (problem : BoxComplementarityProblem (Fin n))
    (vertices : Fin (n + 1) → Fin n → Fin 2)
    (hcomplete : complete_simplex
      (boxComplementaritySpernerCube problem 1 (by omega)) n vertices) :
    vertices = boxComplementarityMeshOneCornerChain n := by
  funext index who
  have hlabel := boxComplementarityFinLabel_eq_rev_of_meshOneCompleteSimplex
    problem vertices hcomplete index
  have hproperties := (boxComplementarityReducedLabel_one_eq_iff
    problem (vertices index) (Fin.rev index)).1 (congrArg Fin.val hlabel)
  unfold boxComplementarityMeshOneCornerChain
  split_ifs with hle
  · let carrier : Fin (n + 1) := ⟨n - who.val, by omega⟩
    have hcarrierLabel := boxComplementarityFinLabel_eq_rev_of_meshOneCompleteSimplex
      problem vertices hcomplete carrier
    have hcarrierValue : boxComplementarityReducedLabel problem 1 (vertices carrier) =
        who.val := by
      have hvalue := congrArg Fin.val hcarrierLabel
      simp only [boxComplementarityFinLabel_val, Fin.val_rev] at hvalue
      have hcarrierVal : carrier.val = n - who.val := rfl
      rw [hcarrierVal] at hvalue
      have := who.isLt
      omega
    have hone := boxComplementarityReducedLabel_one_coordinate_eq_one
      problem (vertices carrier) who hcarrierValue
    have horder : carrier ≤ index := by change n - who.val ≤ index.val; omega
    have hmono := spernerSimplex_val_le_of_le hcomplete.1 horder who
    rw [hone] at hmono
    apply Fin.ext
    have := (vertices index who).isLt
    change 1 ≤ (vertices index who).val at hmono
    change (vertices index who).val = 1
    omega
  · apply hproperties.1 who
    simp only [Fin.val_rev]
    have := index.isLt
    omega

/-- Existence is supplied by the existing cubical Sperner theorem. -/
theorem completeSimplex_meshOneCornerChain
    (problem : BoxComplementarityProblem (Fin n)) :
    complete_simplex (boxComplementaritySpernerCube problem 1 (by omega)) n
      (boxComplementarityMeshOneCornerChain n) := by
  obtain ⟨vertices, hcomplete⟩ := exists_boxComplementarity_completeSimplex problem 1 (by omega)
  rwa [eq_meshOneCornerChain_of_completeSimplex problem vertices hcomplete] at hcomplete

private theorem meshOneCornerChain_rev_intValue (index : Fin (n + 1)) (who : Fin n) :
    ((boxComplementarityMeshOneCornerChain n (Fin.rev index) who).val : ℤ) =
      if index.val ≤ who.val then 1 else 0 := by
  unfold boxComplementarityMeshOneCornerChain
  have hindex := index.isLt
  simp only [Fin.val_rev]
  split_ifs <;> simp_all <;> omega

private theorem meshOneLabelOrderedMatrix_det :
    OrientedSimplexFacet.determinant
      (fun index : Fin (n + 1) => fun who : Fin n =>
        if index.val ≤ who.val then (1 : ℤ) else 0) = (-1) ^ n := by
  let matrix : Matrix (Fin (n + 1)) (Fin (n + 1)) ℤ :=
    fun index => Fin.cons 1 (fun who => if index.val ≤ who.val then 1 else 0)
  let upper : Matrix (Fin n) (Fin n) ℤ :=
    fun row column => if row.val ≤ column.val then 1 else 0
  have hlast : matrix (Fin.last n) = Fin.cons 1 (fun _ => 0) := by
    funext coordinate
    cases coordinate using Fin.cases with
    | zero => rfl
    | succ who =>
        change (if n ≤ who.val then (1 : ℤ) else 0) = 0
        exact if_neg (Nat.not_le.mpr who.isLt)
  have hminor : matrix.submatrix (Fin.last n).succAbove (0 : Fin (n + 1)).succAbove =
      upper := by
    ext row column
    simp [matrix, upper]
  have htriangular : upper.BlockTriangular id := by
    intro row column hlt
    exact if_neg (by change column.val < row.val at hlt; omega)
  have hdetUpper : upper.det = 1 := by
    rw [Matrix.det_of_upperTriangular htriangular]
    simp [upper]
  change matrix.det = _
  rw [Matrix.det_succ_row matrix (Fin.last n), Fin.sum_univ_succ]
  simp only [hlast, Fin.cons_zero, Fin.cons_succ, Fin.val_zero, Fin.val_last,
    add_zero, mul_one, mul_zero, zero_mul, Finset.sum_const_zero, hminor, hdetUpper]

/-- The actual signed weight of the sole mesh-one complete simplex. -/
theorem boxComplementarityCompleteSimplexSignedWeight_meshOneCornerChain
    (problem : BoxComplementarityProblem (Fin n)) :
    boxComplementarityCompleteSimplexSignedWeight problem 1 (by omega)
      (boxComplementarityMeshOneCornerChain n) = (-1) ^ n := by
  rw [boxComplementarityCompleteSimplexSignedWeight_eq problem 1 (by omega) _
    (completeSimplex_meshOneCornerChain problem)]
  change OrientedSimplexFacet.determinant
      (fun index who => ((boxComplementarityMeshOneCornerChain n index who).val : ℤ)) *
      SignedSimplexLabel.orientation (fun index => boxComplementarityFinLabel
        problem 1 (boxComplementarityMeshOneCornerChain n index)) = _
  simp only [boxComplementarityFinLabel_meshOneCornerChain]
  rw [show (Fin.rev : Fin (n + 1) → Fin (n + 1)) = Fin.revPerm by rfl,
    SignedSimplexLabel.orientation_equiv, mul_comm]
  have hperm := Matrix.det_permute (R := ℤ) (Fin.revPerm (n := n + 1))
    (fun index => Fin.cons 1
      (fun who => ((boxComplementarityMeshOneCornerChain n index who).val : ℤ)))
  simp only [Int.cast_id] at hperm
  rw [OrientedSimplexFacet.determinant, ← hperm]
  change OrientedSimplexFacet.determinant
      (fun index who =>
        ((boxComplementarityMeshOneCornerChain n (Fin.rev index) who).val : ℤ)) = _
  simp only [meshOneCornerChain_rev_intValue]
  exact meshOneLabelOrderedMatrix_det

/-- The anchor-selected whole-cube Finset at mesh one is the literal singleton. -/
theorem boxComplementarityLocalCompleteSimplices_one_univ
    (problem : BoxComplementarityProblem (Fin n)) :
    boxComplementarityLocalCompleteSimplices problem 1 (by omega) univ =
      ({boxComplementarityMeshOneCornerChain n} : Finset (Fin (n + 1) → Fin n → Fin 2)) := by
  ext vertices
  simp only [boxComplementarityLocalCompleteSimplices, Finset.mem_filter,
    Finset.mem_univ, true_and, completeSimplexAnchorIn_univ_iff]
  constructor
  · intro hcomplete
    exact Finset.mem_singleton.mpr
      (eq_meshOneCornerChain_of_completeSimplex problem vertices hcomplete)
  · intro hmem
    have heq := Finset.mem_singleton.mp hmem
    rw [heq]
    exact completeSimplex_meshOneCornerChain problem

/-- Exact signed normalization of the actual mesh-one whole-cube count. -/
theorem boxComplementarityLocalSignedCount_one_univ
    (problem : BoxComplementarityProblem (Fin n)) :
    boxComplementarityLocalSignedCount problem 1 (by omega) univ = (-1) ^ n := by
  rw [boxComplementarityLocalSignedCount, boxComplementarityLocalCompleteSimplices_one_univ]
  change (∑ vertices ∈
    ({boxComplementarityMeshOneCornerChain n} : Finset (Fin (n + 1) → Fin n → Fin 2)),
      boxComplementarityCompleteSimplexSignedWeight problem 1 (by omega) vertices) = _
  rw [Finset.sum_singleton, boxComplementarityCompleteSimplexSignedWeight_meshOneCornerChain]

/-- Every positive mesh has the same explicitly signed whole-cube normalization. -/
theorem boxComplementarityLocalSignedCount_univ_eq_neg_one_pow
    (problem : BoxComplementarityProblem (Fin n)) (p : ℕ) (hp : 0 < p) :
    boxComplementarityLocalSignedCount problem p hp univ = (-1) ^ n := by
  rw [boxComplementarityLocalSignedCount_univ_eq_resolution_one,
    boxComplementarityLocalSignedCount_one_univ]

/-- The raw stabilized count retains the geometric-times-label orientation. -/
theorem BoxComplementarityProblem.rawLocalDegree_univ_eq_neg_one_pow
    (problem : BoxComplementarityProblem (Fin n)) :
    problem.rawLocalDegree univ (by simp [IsIsolating]) = (-1) ^ n := by
  rw [problem.rawLocalDegree_univ_eq_resolution_one,
    boxComplementarityLocalSignedCount_one_univ]

/-- The whole-cube-normalized complementarity degree is one in every dimension. -/
theorem BoxComplementarityProblem.localDegree_univ_eq_one
    (problem : BoxComplementarityProblem (Fin n)) :
    problem.localDegree univ (by simp [IsIsolating]) = 1 := by
  rw [localDegree, rawLocalDegree_univ_eq_neg_one_pow, ← mul_pow]
  simp

end Math

