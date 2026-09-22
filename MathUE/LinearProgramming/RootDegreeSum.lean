import MathUE.LinearProgramming.FiniteSolutions
import MathUE.LinearProgramming.CommonChartLocalDegree
import MathUE.Topology.BoxComplementarityFiniteAdditivity
import Mathlib.Topology.Separation.Hausdorff

/-!
# The actual minimum-map degree as a sum over its selected LCP roots

Only solutions selected by the displayed isolating region are required to be
central, strictly complementary, and active-principal nonsingular. Centrality
converts actual box complementarity to a vanishing minimum map. Nonsingular
LCP roots are finite even if other, singular roots exist elsewhere.

Finite Hausdorff separation and shrinking construct disjoint singleton-root
balls. Excision preserves their computed local indices, and finite additivity
then gives the determinant-sign sum in the original fixed scalar chart.
No assertion identifies box-boundary solutions with LCP roots.
-/

noncomputable section

namespace Math.LinearProgramming

open Set Filter Math.Topology
open scoped _root_.Topology

variable {n : ℕ}

private theorem exists_smaller_singleton_ball
    (problem : BoxComplementarityProblem (Fin n))
    (root : UnitCube (Fin n)) (radius : ℝ) (hradius : 0 < radius)
    (hisolating : problem.IsIsolating (Metric.ball root radius))
    (hsingleton : problem.solutionsIn (Metric.ball root radius) = {root})
    (neighborhood : Set (UnitCube (Fin n)))
    (hopen : IsOpen neighborhood) (hroot : root ∈ neighborhood) :
    ∃ (smaller : ℝ) (_hsmaller : 0 < smaller),
      ∃ hsmall : problem.IsIsolating (Metric.ball root smaller),
        Metric.ball root smaller ⊆ neighborhood ∧
        problem.solutionsIn (Metric.ball root smaller) = {root} ∧
        problem.localDegree (Metric.ball root smaller) hsmall =
          problem.localDegree (Metric.ball root radius) hisolating := by
  have hneighborhood : Metric.ball root radius ∩ neighborhood ∈ 𝓝 root :=
    (Metric.isOpen_ball.inter hopen).mem_nhds ⟨Metric.mem_ball_self hradius, hroot⟩
  obtain ⟨epsilon, hepsilon, hball⟩ := Metric.mem_nhds_iff.mp hneighborhood
  let small := Metric.ball root (epsilon / 2)
  have hclosure : closure small ⊆ Metric.ball root radius ∩ neighborhood :=
    fun _ hpoint => hball (Metric.closedBall_subset_ball (half_lt_self hepsilon)
      (Metric.closure_ball_subset_closedBall hpoint))
  have hrootSmall : root ∈ small := Metric.mem_ball_self (half_pos hepsilon)
  have hunique (point : UnitCube (Fin n)) (hsolution : point ∈ problem.solutionSet)
      (hpoint : point ∈ closure small) : point = root := by
    have hmem : point ∈ problem.solutionsIn (Metric.ball root radius) :=
      ⟨hsolution, (hclosure hpoint).1⟩
    rw [hsingleton] at hmem
    exact hmem
  have hsmall : problem.IsIsolating small := by
    refine ⟨Metric.isOpen_ball, Set.eq_empty_iff_forall_notMem.mpr ?_⟩
    rintro point ⟨hsolution, hfrontier⟩
    have hequal := hunique point hsolution (frontier_subset_closure hfrontier)
    subst point
    have hopenSmall : IsOpen small := Metric.isOpen_ball
    exact hfrontier.2 (by simpa only [hopenSmall.interior_eq] using hrootSmall)
  have hsmallSolutions : problem.solutionsIn small = {root} := by
    ext point
    constructor
    · rintro ⟨hsolution, hpoint⟩
      exact hunique point hsolution (subset_closure hpoint)
    · intro hequal
      have hrootSolution : root ∈ problem.solutionSet := by
        have hmem : root ∈ problem.solutionsIn (Metric.ball root radius) := by
          rw [hsingleton]
          exact Set.mem_singleton root
        exact hmem.1
      exact ⟨hequal.symm ▸ hrootSolution, hequal.symm ▸ hrootSmall⟩
  refine ⟨epsilon / 2, half_pos hepsilon, hsmall,
    fun _ hpoint => (hclosure (subset_closure hpoint)).2, hsmallSolutions, ?_⟩
  exact problem.localDegree_eq_of_solutionsIn_eq _ _ hsmall hisolating
    (hsmallSolutions.trans hsingleton.symm)

/-- The degree on an isolating region is the sum of the active determinant
signs over precisely its actual selected roots. Regularity is required only
there; finiteness, the root enumeration, and all local isolation are derived. -/
theorem exists_finset_lcpMinBoxProblem_localDegree_eq_sum_sign_det
    (matrix : Matrix (Fin n) (Fin n) ℝ) (offset center : Fin n → ℝ)
    (radius : ℝ) (hradius : 0 < radius)
    (region : Set (UnitCube (Fin n)))
    (hisolating : (lcpMinBoxProblem matrix offset center radius hradius).IsIsolating region)
    (hcentral : ∀ root ∈
      (lcpMinBoxProblem matrix offset center radius hradius).solutionsIn region,
      root ∈ diagonalCentralRegion n)
    (hstrict : ∀ root ∈
      (lcpMinBoxProblem matrix offset center radius hradius).solutionsIn region, ∀ who,
      rectangularCubePoint (fun coordinate => center coordinate - radius)
        (fun coordinate => center coordinate + radius) root who = 0 →
      0 < lcpResidual matrix offset
        (rectangularCubePoint (fun coordinate => center coordinate - radius)
          (fun coordinate => center coordinate + radius) root) who)
    (hnonsingular : ∀ root ∈
      (lcpMinBoxProblem matrix offset center radius hradius).solutionsIn region,
      (matrix.toSquareBlockProp (fun who => 0 <
        rectangularCubePoint (fun coordinate => center coordinate - radius)
          (fun coordinate => center coordinate + radius) root who)).det ≠ 0) :
    ∃ roots : Finset (UnitCube (Fin n)),
      (↑roots : Set (UnitCube (Fin n))) =
        (lcpMinBoxProblem matrix offset center radius hradius).solutionsIn region ∧
      (lcpMinBoxProblem matrix offset center radius hradius).localDegree region hisolating =
        ∑ root ∈ roots, (SignType.sign (matrix.toSquareBlockProp (fun who => 0 <
          rectangularCubePoint (fun coordinate => center coordinate - radius)
            (fun coordinate => center coordinate + radius) root who)).det : ℤ) := by
  classical
  let actual := lcpMinBoxProblem matrix offset center radius hradius
  let chart := rectangularCubePoint (fun who => center who - radius)
    (fun who => center who + radius)
  let selected := actual.solutionsIn region
  have hsource (root : UnitCube (Fin n)) (hroot : root ∈ selected) :
      IsStandardLCPSolution matrix offset (chart root) := by
    have hinterior (who : Fin n) : 0 < (root who : ℝ) ∧ (root who : ℝ) < 1 := by
      have h := hcentral root hroot who
      constructor <;> linarith
    have hzero := (actual.isSolution_iff_gain_eq_zero_of_coordinateInterior
      root hinterior).mp hroot.1
    apply (lcpMinMap_eq_zero_iff matrix offset (chart root)).mp
    change -lcpMinMap matrix offset (chart root) = 0 at hzero
    exact neg_eq_zero.mp hzero
  have hchart : Function.Injective chart := by
    intro first second hequal
    funext who
    apply Subtype.ext
    have hcoordinate := congrFun hequal who
    dsimp [chart, rectangularCubePoint, rectangularPoint] at hcoordinate
    have hwidth : center who + radius - (center who - radius) ≠ 0 := by linarith
    exact mul_left_cancel₀ hwidth (add_left_cancel hcoordinate)
  have hmaps : Set.MapsTo chart selected
      {root | IsStandardLCPSolution matrix offset root ∧
        (matrix.toSquareBlockProp (fun who => 0 < root who)).det ≠ 0} :=
    fun root hroot => ⟨hsource root hroot, hnonsingular root hroot⟩
  have hfinite : selected.Finite :=
    Set.Finite.of_injOn hmaps
      hchart.injOn (finite_nonsingularStandardLCPSolutions matrix offset)
  let roots := hfinite.toFinset
  have hroots : (↑roots : Set (UnitCube (Fin n))) = selected := hfinite.coe_toFinset
  have hmem (root : roots) : (root : UnitCube (Fin n)) ∈ selected := by
    rw [← hroots]
    exact root.property
  obtain ⟨separated, hseparated, hdisjoint⟩ := hfinite.t2_separation
  have hlocal (root : roots) :
      ∃ (ballRadius : ℝ) (_hballRadius : 0 < ballRadius),
        ∃ hball : actual.IsIsolating (Metric.ball (root : UnitCube (Fin n)) ballRadius),
          Metric.ball (root : UnitCube (Fin n)) ballRadius ⊆ separated root ∧
          actual.solutionsIn (Metric.ball (root : UnitCube (Fin n)) ballRadius) =
            {(root : UnitCube (Fin n))} ∧
          actual.localDegree (Metric.ball (root : UnitCube (Fin n)) ballRadius) hball =
            (SignType.sign (matrix.toSquareBlockProp (fun who => 0 < chart root who)).det :
              ℤ) := by
    obtain ⟨oldRadius, holdRadius, hold, holdSolutions, holdDegree⟩ :=
      exists_ball_lcpMinBoxProblem_localDegree_eq_sign_det matrix offset center radius
        hradius root (hcentral root (hmem root)) (hsource root (hmem root))
        (hstrict root (hmem root)) (hnonsingular root (hmem root))
    obtain ⟨smallRadius, hsmallRadius, hsmall, hsubset, hsolutions, hdegree⟩ :=
      exists_smaller_singleton_ball actual root oldRadius holdRadius hold holdSolutions
        (separated root) (hseparated root).2 (hseparated root).1
    exact ⟨smallRadius, hsmallRadius, hsmall, hsubset, hsolutions,
      hdegree.trans holdDegree⟩
  choose ballRadius hballRadius hball hsubset hsolutions hdegree using hlocal
  let balls (root : roots) := Metric.ball (root : UnitCube (Fin n)) (ballRadius root)
  have hpairwise : Pairwise fun first second => Disjoint (balls first) (balls second) := by
    intro first second hne
    exact (hdisjoint (hmem first) (hmem second)
      (fun hequal => hne (Subtype.ext hequal))).mono (hsubset first) (hsubset second)
  have hunion := actual.isIsolating_iUnion balls hball
  have hunionSolutions : actual.solutionsIn (⋃ root, balls root) = selected := by
    ext point
    constructor
    · rintro ⟨hsolution, hpoint⟩
      obtain ⟨root, hpoint⟩ := Set.mem_iUnion.mp hpoint
      have hlocalMem : point ∈ actual.solutionsIn (balls root) := ⟨hsolution, hpoint⟩
      rw [hsolutions root] at hlocalMem
      exact hlocalMem.symm ▸ hmem root
    · intro hpoint
      have hpointRoots : point ∈ roots := by
        rw [← hroots] at hpoint
        exact hpoint
      let root : roots := ⟨point, hpointRoots⟩
      refine ⟨hpoint.1, Set.mem_iUnion.mpr ⟨root, ?_⟩⟩
      exact Metric.mem_ball_self (hballRadius root)
  refine ⟨roots, hroots, ?_⟩
  calc
    actual.localDegree region hisolating =
        actual.localDegree (⋃ root, balls root) hunion :=
      actual.localDegree_eq_of_solutionsIn_eq _ _ hisolating hunion hunionSolutions.symm
    _ = ∑ root : roots, actual.localDegree (balls root) (hball root) :=
      actual.localDegree_iUnion_of_pairwiseDisjoint balls hball hpairwise
    _ = ∑ root : roots,
        (SignType.sign (matrix.toSquareBlockProp (fun who => 0 < chart root who)).det : ℤ) :=
      Finset.sum_congr rfl (fun root _ => hdegree root)
    _ = ∑ root ∈ roots,
        (SignType.sign (matrix.toSquareBlockProp (fun who => 0 < chart root who)).det : ℤ) :=
      Finset.sum_coe_sort roots (fun root : UnitCube (Fin n) =>
        (SignType.sign (matrix.toSquareBlockProp (fun who => 0 < chart root who)).det : ℤ))

end Math.LinearProgramming
