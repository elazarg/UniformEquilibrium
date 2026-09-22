import MathUE.LinearProgramming.LocalDegree
import MathUE.Topology.BoxComplementarityOffCenterMatrixLocalIndex

/-!
# Strict LCP local indices in one fixed scalar chart

The scalar chart center and radius stay fixed. At any strictly complementary
LCP root whose cube representative is in the central region, local affinity
produces equality with a positive scaling of the off-center affine model.
A small ball with closure inside that equality neighborhood and the central
region supplies actual isolation. Frontier replacement computes the local
index of the literal minimum map in the original fixed chart.

Different roots may use different small balls, but the complementarity
problem itself is the same. No arbitrary-chart independence is asserted.
-/

noncomputable section

namespace Math.LinearProgramming

open Set Filter Math.Topology
open scoped _root_.Topology

variable {n : ℕ}

/-- Differences in one scalar chart have its literal positive width factor. -/
theorem rectangularCubePoint_scalar_sub (center : Fin n → ℝ) (radius : ℝ)
    (point root : UnitCube (Fin n)) :
    rectangularCubePoint (fun who => center who - radius)
        (fun who => center who + radius) point -
      rectangularCubePoint (fun who => center who - radius)
        (fun who => center who + radius) root =
      (2 * radius) • ((fun who => (point who : ℝ)) - fun who => (root who : ℝ)) := by
  funext who
  dsimp [rectangularCubePoint, rectangularPoint]
  ring

/-- A strictly complementary root in the central part of a fixed scalar chart
has a constructed isolating ball whose actual minimum-map index is the sign
of its active principal determinant. -/
theorem exists_ball_lcpMinBoxProblem_localDegree_eq_sign_det
    (matrix : Matrix (Fin n) (Fin n) ℝ) (offset center : Fin n → ℝ)
    (radius : ℝ) (hradius : 0 < radius)
    (root : UnitCube (Fin n)) (hcentral : root ∈ diagonalCentralRegion n)
    (hroot : IsStandardLCPSolution matrix offset
      (rectangularCubePoint (fun who => center who - radius)
        (fun who => center who + radius) root))
    (hstrict : ∀ who,
      rectangularCubePoint (fun coordinate => center coordinate - radius)
        (fun coordinate => center coordinate + radius) root who = 0 →
      0 < lcpResidual matrix offset
        (rectangularCubePoint (fun coordinate => center coordinate - radius)
          (fun coordinate => center coordinate + radius) root) who)
    (hnonsingular : (matrix.toSquareBlockProp (fun who => 0 <
      rectangularCubePoint (fun coordinate => center coordinate - radius)
        (fun coordinate => center coordinate + radius) root who)).det ≠ 0) :
    ∃ (ballRadius : ℝ) (_hballRadius : 0 < ballRadius),
      ∃ hisolating : (lcpMinBoxProblem matrix offset center radius hradius).IsIsolating
        (Metric.ball root ballRadius),
        (lcpMinBoxProblem matrix offset center radius hradius).solutionsIn
          (Metric.ball root ballRadius) = {root} ∧
        (lcpMinBoxProblem matrix offset center radius hradius).localDegree
          (Metric.ball root ballRadius) hisolating =
            (SignType.sign (matrix.toSquareBlockProp (fun who => 0 <
              rectangularCubePoint (fun coordinate => center coordinate - radius)
                (fun coordinate => center coordinate + radius) root who)).det : ℤ) := by
  let chart := rectangularCubePoint (fun who => center who - radius)
    (fun who => center who + radius)
  let ambientRoot := chart root
  let selected := lcpSelectedMatrix matrix ambientRoot
  let actual := lcpMinBoxProblem matrix offset center radius hradius
  let base := offCenterMatrixProblem selected (fun who => (root who : ℝ))
  let affine := base.scaleGain (2 * radius)
  have hselected : selected.det ≠ 0 := by
    intro hzero
    exact hnonsingular ((det_lcpSelectedMatrix matrix ambientRoot).symm.trans hzero)
  have hscale : 0 < 2 * radius := mul_pos (by norm_num) hradius
  have hchart : Continuous chart := continuous_rectangularCubePoint _ _
  have hnear : ∀ᶠ point in 𝓝 root, lcpMinMap matrix offset (chart point) =
      selected.mulVec (chart point - ambientRoot) :=
    (hchart.continuousAt : ContinuousAt chart root).eventually
      (hroot.eventually_lcpMinMap_eq_selectedMatrix hstrict)
  have hgain : ∀ᶠ point in 𝓝 root, affine.gain point = actual.gain point := by
    filter_upwards [hnear] with point hpoint
    funext who
    change (2 * radius) * -(selected.mulVec
      ((fun coordinate => (point coordinate : ℝ)) - fun coordinate => (root coordinate : ℝ)))
        who = -lcpMinMap matrix offset (chart point) who
    rw [hpoint]
    change _ = -(selected.mulVec (chart point - chart root)) who
    rw [rectangularCubePoint_scalar_sub, Matrix.mulVec_smul]
    simp only [Pi.smul_apply, smul_eq_mul, mul_neg]
  have hneighborhood : {point | affine.gain point = actual.gain point} ∩
      diagonalCentralRegion n ∈ 𝓝 root :=
    Filter.inter_mem hgain (isOpen_diagonalCentralRegion.mem_nhds hcentral)
  obtain ⟨epsilon, hepsilon, hball⟩ := Metric.mem_nhds_iff.mp hneighborhood
  let region := Metric.ball root (epsilon / 2)
  have hclosure (point : UnitCube (Fin n)) (hpoint : point ∈ closure region) :
      affine.gain point = actual.gain point ∧ point ∈ diagonalCentralRegion n :=
    hball (Metric.closedBall_subset_ball (half_lt_self hepsilon)
      (Metric.closure_ball_subset_closedBall hpoint))
  have hinterior (point : UnitCube (Fin n)) (hpoint : point ∈ closure region)
      (who : Fin n) : 0 < (point who : ℝ) ∧ (point who : ℝ) < 1 := by
    have h := (hclosure point hpoint).2 who
    constructor <;> linarith
  have hrootRegion : root ∈ region := Metric.mem_ball_self (half_pos hepsilon)
  have hbase := isIsolating_offCenterMatrix_of_closureInterior
    selected hselected root region Metric.isOpen_ball hrootRegion hinterior
  have haffine : affine.IsIsolating region :=
    (base.isIsolating_scaleGain_iff hscale region).mpr hbase
  have hfrontier : EqOn affine.gain actual.gain (frontier region) :=
    fun point hpoint => (hclosure point (frontier_subset_closure hpoint)).1
  have hactual := affine.isIsolating_of_gain_eqOn_frontier actual region haffine hfrontier
  have hbaseDegree := localDegree_offCenterMatrix_region_eq_sign_det selected hselected
    root hcentral region Metric.isOpen_ball hrootRegion hinterior
  have haffineDegree := (base.localDegree_scaleGain hscale region hbase).trans hbaseDegree
  have hactualDegree :=
    (affine.localDegree_eq_of_gain_eqOn_frontier actual region haffine hfrontier).symm.trans
      haffineDegree
  have hsolutions : actual.solutionsIn region = {root} := by
    ext point
    change (actual.IsSolution point ∧ point ∈ region) ↔ point = root
    constructor
    · rintro ⟨hsolution, hregion⟩
      have hpointGain := (hclosure point (subset_closure hregion)).1
      have hsolutionAffine : affine.IsSolution point := by
        simpa only [BoxComplementarityProblem.IsSolution, hpointGain] using hsolution
      have hsolutionBase := (base.isSolution_scaleGain_iff hscale point).mp hsolutionAffine
      exact eq_root_of_isSolution_offCenterMatrix selected hselected root point
        hsolutionBase (hinterior point (subset_closure hregion))
    · rintro rfl
      refine ⟨?_, hrootRegion⟩
      apply actual.isSolution_of_gain_eq_zero
      have hmin := (lcpMinMap_eq_zero_iff matrix offset ambientRoot).mpr hroot
      change -lcpMinMap matrix offset ambientRoot = 0
      rw [hmin, neg_zero]
  refine ⟨epsilon / 2, half_pos hepsilon, hactual, hsolutions, ?_⟩
  exact hactualDegree.trans
    (congrArg (fun value : ℝ => (SignType.sign value : ℤ))
      (det_lcpSelectedMatrix matrix ambientRoot))

end Math.LinearProgramming
