import MathUE.LinearProgramming.LocalAffine
import MathUE.Topology.BoxComplementarityAffineLocalIndex

/-!
# Integer local index of a strictly complementary LCP root

The actual minimum map is affine on a constructed small closed box around
the root. Its selected-row matrix has the active principal determinant.
The affine count therefore computes its integer local degree in the
displayed chart and inner box. No arbitrary-chart comparison or sum of
indices over different root-centered charts is asserted here.
-/

noncomputable section

namespace Math.LinearProgramming

open Set Math.Topology

variable {n : ℕ}

/-- The actual ambient minimum map in a displayed root-centered positive chart. -/
def lcpMinBoxProblem (matrix : Matrix (Fin n) (Fin n) ℝ) (offset root : Fin n → ℝ)
    (radius : ℝ) (hradius : 0 < radius) : BoxComplementarityProblem (Fin n) :=
  BoxComplementarityProblem.ofAmbientMap
    (fun who => root who - radius) (fun who => root who + radius)
    (affineRootBox_width root hradius) (lcpMinMap matrix offset)
    (continuous_lcpMinMap matrix offset).continuousOn

/-- A strictly complementary root with nonsingular active principal matrix
has a constructed isolating box with local index equal to its determinant sign. -/
theorem IsStandardLCPSolution.exists_box_localDegree_eq_sign_det
    {matrix : Matrix (Fin n) (Fin n) ℝ} {offset root : Fin n → ℝ}
    (hroot : IsStandardLCPSolution matrix offset root)
    (hstrict : ∀ who, root who = 0 → 0 < lcpResidual matrix offset root who)
    (hnonsingular : (matrix.toSquareBlockProp (fun who => 0 < root who)).det ≠ 0) :
    ∃ (radius : ℝ) (hradius : 0 < radius),
      ∃ hisolating : (lcpMinBoxProblem matrix offset root radius hradius).IsIsolating
        (rectangularCubePoint (fun who => root who - radius)
          (fun who => root who + radius) ⁻¹' affineRootRegion root radius),
        (lcpMinBoxProblem matrix offset root radius hradius).localDegree
          (rectangularCubePoint (fun who => root who - radius)
            (fun who => root who + radius) ⁻¹' affineRootRegion root radius) hisolating =
          (SignType.sign (matrix.toSquareBlockProp (fun who => 0 < root who)).det : ℤ) := by
  obtain ⟨radius, hradius, haffine⟩ :=
    hroot.exists_box_lcpMinMap_eq_selectedMatrix hstrict
  have hmatrix : (lcpSelectedMatrix matrix root).det ≠ 0 := by
    intro hzero
    exact hnonsingular ((det_lcpSelectedMatrix matrix root).symm.trans hzero)
  have hproblem : lcpMinBoxProblem matrix offset root radius hradius =
      affineRootProblem (lcpSelectedMatrix matrix root) root radius hradius := by
    apply BoxComplementarityProblem.ext
    funext point who
    change -lcpMinMap matrix offset
        (rectangularCubePoint (fun coordinate => root coordinate - radius)
          (fun coordinate => root coordinate + radius) point) who = _
    rw [haffine _ (rectangularCubePoint_mem_Icc (affineRootBox_width root hradius) point)]
    rfl
  have hisolating : (lcpMinBoxProblem matrix offset root radius hradius).IsIsolating
      (rectangularCubePoint (fun who => root who - radius)
        (fun who => root who + radius) ⁻¹' affineRootRegion root radius) := by
    rw [hproblem]
    exact isIsolating_affineRootProblem _ hmatrix root radius hradius
  refine ⟨radius, hradius, hisolating, ?_⟩
  have hdegree := (localDegree_affineRootProblem_eq_sign_det
    (lcpSelectedMatrix matrix root) hmatrix root radius hradius).trans
      (congrArg (fun value : ℝ => (SignType.sign value : ℤ))
        (det_lcpSelectedMatrix matrix root))
  simpa only [hproblem] using hdegree

end Math.LinearProgramming
