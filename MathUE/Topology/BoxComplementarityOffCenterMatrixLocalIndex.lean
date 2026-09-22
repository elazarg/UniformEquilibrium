import MathUE.Topology.BoxComplementarityCenteredMatrixLocalIndex
import MathUE.Topology.BoxComplementaritySolutionExcision

/-!
# Off-center affine index on the fixed central region

An affine root lying strictly in the central region can move to the cube
center through that same region. Nonsingularity excludes all other interior
zeros and derives isolation throughout this explicit homotopy. Its integer
degree is therefore the determinant sign already computed at the center.
The statement includes dimension zero and compares no different charts.
-/

noncomputable section

namespace Math

open Classical Set

variable {n : ℕ}

/-- A literal affine gain field with an arbitrary displayed root. -/
def offCenterMatrixProblem (matrix : Matrix (Fin n) (Fin n) ℝ) (root : Fin n → ℝ) :
    BoxComplementarityProblem (Fin n) where
  gain point := -matrix.mulVec ((fun who => (point who : ℝ)) - root)
  continuous_gain who := by
    have hvector : Continuous (fun point : UnitCube (Fin n) =>
        (fun coordinate => (point coordinate : ℝ)) - root) :=
      (continuous_pi fun coordinate => (continuous_apply coordinate).subtype_val).sub
        continuous_const
    exact ((continuous_apply who).comp (continuous_const.matrix_mulVec hvector)).neg

/-- A nonsingular affine gain can vanish only at its displayed root. -/
theorem offCenterMatrixProblem_eq_root_of_gain_eq_zero
    (matrix : Matrix (Fin n) (Fin n) ℝ) (hnonsingular : matrix.det ≠ 0)
    (root : Fin n → ℝ) (point : UnitCube (Fin n))
    (hzero : (offCenterMatrixProblem matrix root).gain point = 0) :
    ∀ who, (point who : ℝ) = root who := by
  have hinjective : Function.Injective matrix.mulVec :=
    Matrix.mulVec_injective_iff_isUnit.mpr
      ((Matrix.isUnit_iff_isUnit_det matrix).mpr (isUnit_iff_ne_zero.mpr hnonsingular))
  change -matrix.mulVec ((fun who => (point who : ℝ)) - root) = 0 at hzero
  have hvector := hinjective
    ((neg_eq_zero.mp hzero).trans (Matrix.mulVec_zero matrix).symm)
  exact fun who => congrFun (sub_eq_zero.mp hvector) who

/-- Any displayed root strictly in the central region gives actual isolation there. -/
theorem isIsolating_offCenterMatrix_centralRegion
    (matrix : Matrix (Fin n) (Fin n) ℝ) (hnonsingular : matrix.det ≠ 0)
    (root : Fin n → ℝ) (hroot : ∀ who, 1 / 4 < root who ∧ root who < 3 / 4) :
    (offCenterMatrixProblem matrix root).IsIsolating (diagonalCentralRegion n) := by
  refine ⟨isOpen_diagonalCentralRegion, Set.eq_empty_iff_forall_notMem.mpr ?_⟩
  rintro point ⟨hsolution, hfrontier⟩
  have hbounds := coordinate_bounds_of_mem_closure_diagonalCentralRegion
    (frontier_subset_closure hfrontier)
  have hinterior (who : Fin n) : 0 < (point who : ℝ) ∧ (point who : ℝ) < 1 := by
    have h := hbounds who
    constructor <;> linarith
  have hzero := (BoxComplementarityProblem.isSolution_iff_gain_eq_zero_of_coordinateInterior
    (offCenterMatrixProblem matrix root) point hinterior).mp hsolution
  have hpoint := offCenterMatrixProblem_eq_root_of_gain_eq_zero
    matrix hnonsingular root point hzero
  have hmem : point ∈ diagonalCentralRegion n := by
    intro who
    rw [hpoint who]
    exact hroot who
  apply hfrontier.2
  rwa [isOpen_diagonalCentralRegion.interior_eq]

/-- A continuous root path supplies the actual jointly continuous affine family. -/
theorem isContinuous_offCenterMatrixFamily
    (matrix : Matrix (Fin n) (Fin n) ℝ)
    (roots : Icc (0 : ℝ) 1 → Fin n → ℝ) (hroots : Continuous roots) :
    IsContinuousBoxComplementarityFamily (Fin n)
      (fun parameter => offCenterMatrixProblem matrix (roots parameter)) := by
  intro who
  have hvector : Continuous (fun data : Icc (0 : ℝ) 1 × UnitCube (Fin n) =>
      (fun coordinate => (data.2 coordinate : ℝ)) - roots data.1) :=
    (continuous_pi fun coordinate =>
      ((continuous_apply coordinate).comp continuous_snd).subtype_val).sub
        (hroots.comp continuous_fst)
  exact ((continuous_apply who).comp (continuous_const.matrix_mulVec hvector)).neg

/-- The off-center nonsingular affine model has determinant-sign degree on the
same central counting region whenever its root belongs to that region. -/
theorem localDegree_offCenterMatrix_eq_sign_det
    (matrix : Matrix (Fin n) (Fin n) ℝ) (hnonsingular : matrix.det ≠ 0)
    (root : Fin n → ℝ) (hroot : ∀ who, 1 / 4 < root who ∧ root who < 3 / 4) :
    (offCenterMatrixProblem matrix root).localDegree (diagonalCentralRegion n)
      (isIsolating_offCenterMatrix_centralRegion matrix hnonsingular root hroot) =
        (SignType.sign matrix.det : ℤ) := by
  let roots : Icc (0 : ℝ) 1 → Fin n → ℝ := fun parameter who =>
    (1 - (parameter : ℝ)) * root who + (parameter : ℝ) * (1 / 2)
  have hcontinuous : Continuous roots := by
    exact continuous_pi fun who =>
      ((continuous_const.sub continuous_subtype_val).mul continuous_const).add
        (continuous_subtype_val.mul continuous_const)
  have hinside (parameter : Icc (0 : ℝ) 1) (who : Fin n) :
      1 / 4 < roots parameter who ∧ roots parameter who < 3 / 4 := by
    simpa only [roots, smul_eq_mul, Set.mem_Ioo] using
      (convex_Ioo (𝕜 := ℝ) (1 / 4 : ℝ) (3 / 4)) (hroot who)
        (by norm_num : (1 / 2 : ℝ) ∈ Ioo (1 / 4) (3 / 4))
        (sub_nonneg.mpr parameter.property.2) parameter.property.1 (sub_add_cancel _ _)
  have hfamily := isContinuous_offCenterMatrixFamily matrix roots hcontinuous
  have hisolating := fun parameter =>
    isIsolating_offCenterMatrix_centralRegion matrix hnonsingular
      (roots parameter) (hinside parameter)
  have hdegree := hfamily.localDegree_endpoints_eq (diagonalCentralRegion n) hisolating
  have hfirst : offCenterMatrixProblem matrix (roots 0) =
      offCenterMatrixProblem matrix root := by
    congr 1
    funext who
    simp [roots]
  have hlast : offCenterMatrixProblem matrix (roots 1) = centeredMatrixProblem matrix := by
    apply BoxComplementarityProblem.ext
    funext point who
    simp [offCenterMatrixProblem, roots, centeredMatrixProblem]
    rfl
  have hequal :
      (offCenterMatrixProblem matrix root).localDegree (diagonalCentralRegion n)
        (isIsolating_offCenterMatrix_centralRegion matrix hnonsingular root hroot) =
      (centeredMatrixProblem matrix).localDegree (diagonalCentralRegion n)
        (isIsolating_centeredMatrix_centralRegion matrix hnonsingular) := by
    simpa only [hfirst, hlast] using hdegree
  exact hequal.trans (localDegree_centeredMatrix_eq_sign_det matrix hnonsingular)

/-- An interior complementarity solution of the nonsingular affine model is
the displayed root, as an actual point of the reference cube. -/
theorem eq_root_of_isSolution_offCenterMatrix
    (matrix : Matrix (Fin n) (Fin n) ℝ) (hnonsingular : matrix.det ≠ 0)
    (root point : UnitCube (Fin n))
    (hsolution : (offCenterMatrixProblem matrix (fun who => (root who : ℝ))).IsSolution point)
    (hinterior : ∀ who, 0 < (point who : ℝ) ∧ (point who : ℝ) < 1) :
    point = root := by
  have hzero := (BoxComplementarityProblem.isSolution_iff_gain_eq_zero_of_coordinateInterior
    (offCenterMatrixProblem matrix (fun who => (root who : ℝ))) point hinterior).mp hsolution
  have hequal := offCenterMatrixProblem_eq_root_of_gain_eq_zero
    matrix hnonsingular (fun who => (root who : ℝ)) point hzero
  funext who
  exact Subtype.ext (hequal who)

/-- Any open neighborhood of the root whose closure lies in the coordinate
interior is isolating for the actual affine problem. -/
theorem isIsolating_offCenterMatrix_of_closureInterior
    (matrix : Matrix (Fin n) (Fin n) ℝ) (hnonsingular : matrix.det ≠ 0)
    (root : UnitCube (Fin n)) (region : Set (UnitCube (Fin n)))
    (hopen : IsOpen region) (hroot : root ∈ region)
    (hclosure : ∀ point ∈ closure region,
      ∀ who, 0 < (point who : ℝ) ∧ (point who : ℝ) < 1) :
    (offCenterMatrixProblem matrix (fun who => (root who : ℝ))).IsIsolating region := by
  refine ⟨hopen, Set.eq_empty_iff_forall_notMem.mpr ?_⟩
  rintro point ⟨hsolution, hfrontier⟩
  have hequal := eq_root_of_isSolution_offCenterMatrix matrix hnonsingular root point
    hsolution (hclosure point (frontier_subset_closure hfrontier))
  apply hfrontier.2
  rw [hopen.interior_eq, hequal]
  exact hroot

/-- The determinant-sign index holds on every displayed open root neighborhood
with coordinate-interior closure. The root remains in the central region for
the previously computed common-region comparison. -/
theorem localDegree_offCenterMatrix_region_eq_sign_det
    (matrix : Matrix (Fin n) (Fin n) ℝ) (hnonsingular : matrix.det ≠ 0)
    (root : UnitCube (Fin n)) (hcentral : root ∈ diagonalCentralRegion n)
    (region : Set (UnitCube (Fin n))) (hopen : IsOpen region) (hroot : root ∈ region)
    (hclosure : ∀ point ∈ closure region,
      ∀ who, 0 < (point who : ℝ) ∧ (point who : ℝ) < 1) :
    (offCenterMatrixProblem matrix (fun who => (root who : ℝ))).localDegree region
      (isIsolating_offCenterMatrix_of_closureInterior
        matrix hnonsingular root region hopen hroot hclosure) =
        (SignType.sign matrix.det : ℤ) := by
  let problem := offCenterMatrixProblem matrix (fun who => (root who : ℝ))
  have hisolating := isIsolating_offCenterMatrix_of_closureInterior
    matrix hnonsingular root region hopen hroot hclosure
  have hcentralIsolating := isIsolating_offCenterMatrix_centralRegion
    matrix hnonsingular (fun who => (root who : ℝ)) hcentral
  have hequal : problem.solutionsIn region =
      problem.solutionsIn (diagonalCentralRegion n) := by
    ext point
    change (problem.IsSolution point ∧ point ∈ region) ↔
      (problem.IsSolution point ∧ point ∈ diagonalCentralRegion n)
    constructor
    · rintro ⟨hsolution, hregion⟩
      have heq := eq_root_of_isSolution_offCenterMatrix matrix hnonsingular root point
        hsolution (hclosure point (subset_closure hregion))
      exact ⟨hsolution, heq.symm ▸ hcentral⟩
    · rintro ⟨hsolution, hregion⟩
      have hinterior (who : Fin n) : 0 < (point who : ℝ) ∧ (point who : ℝ) < 1 := by
        have h := hregion who
        constructor <;> linarith
      have heq := eq_root_of_isSolution_offCenterMatrix
        matrix hnonsingular root point hsolution hinterior
      exact ⟨hsolution, heq.symm ▸ hroot⟩
  exact (problem.localDegree_eq_of_solutionsIn_eq region (diagonalCentralRegion n)
    hisolating hcentralIsolating hequal).trans
      (localDegree_offCenterMatrix_eq_sign_det
        matrix hnonsingular (fun who => (root who : ℝ)) hcentral)

end Math
