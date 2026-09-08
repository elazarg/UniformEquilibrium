import MathUE.Topology.FiniteUnitCubeFrontier
import Research.Topology.BoxComplementarityPrismCluster

/-!
# Actual prism parent changes force a complete face into the frontier collar

The pinned face relation retains every shared vertex as an actual vertex of
each parent. The existing simplex mesh estimate bounds its distance from
either parent's selected vertex. Opposite region membership therefore puts
the shared vertex in a closed frontier collar of one mesh width.
-/

noncomputable section

namespace Math

open Filter Set Topology

variable {n p : ℕ} {hp : 0 < p}
  {label : (kuhnPrismGeometryCube n p hp).G → Fin (n + 1)}

/-- A shared face vertex is within one spatial mesh width of every actual parent vertex. -/
theorem dist_prismFace_parent_spatial_vertices_le_one_div
    (face : KuhnPrismFace n p hp label) (cell : KuhnPrismCell n p hp)
    (hincident : kuhnPrismIncident cell face)
    (faceIndex : Fin (n + 1)) (cellIndex : Fin (n + 2)) :
    dist (Fin.init (boxComplementarityGridPoint p (face.1 faceIndex)))
      (Fin.init (boxComplementarityGridPoint p (cell.1 cellIndex))) ≤ 1 / (p : ℝ) := by
  obtain ⟨parentIndex, hparentIndex⟩ := hincident.2.2 ⟨faceIndex, rfl⟩
  change dist (boxComplementarityGridPoint p (Fin.init (face.1 faceIndex)))
    (boxComplementarityGridPoint p (Fin.init (cell.1 cellIndex))) ≤ 1 / (p : ℝ)
  rw [← hparentIndex]
  apply dist_boxComplementarityGridPoint_le_one_div p hp
  intro coordinate
  exact ⟨le_add_one_of_simplex _ cell.1 cell.2 parentIndex cellIndex coordinate.castSucc,
    le_add_one_of_simplex _ cell.1 cell.2 cellIndex parentIndex coordinate.castSucc⟩

/-- Opposite membership of actual parent vertices puts every shared face vertex in the collar. -/
theorem prismFace_vertex_mem_frontierCollar_of_parent_membership
    (region : Set (UnitCube (Fin n))) (hopen : IsOpen region)
    (face : KuhnPrismFace n p hp label) (first second : KuhnPrismCell n p hp)
    (hfirstIncident : kuhnPrismIncident first face)
    (hsecondIncident : kuhnPrismIncident second face)
    (firstIndex secondIndex : Fin (n + 2))
    (hfirst : Fin.init (boxComplementarityGridPoint p (first.1 firstIndex)) ∈ region)
    (hsecond : Fin.init (boxComplementarityGridPoint p (second.1 secondIndex)) ∉ region)
    (faceIndex : Fin (n + 1)) :
    Fin.init (boxComplementarityGridPoint p (face.1 faceIndex)) ∈
      Metric.cthickening (1 / (p : ℝ)) (frontier region) := by
  exact mem_cthickening_frontier_of_unitCube_endpoints region hopen _ _ _ _ hfirst hsecond
    (dist_prismFace_parent_spatial_vertices_le_one_div face first hfirstIncident
      faceIndex firstIndex)
    (dist_prismFace_parent_spatial_vertices_le_one_div face second hsecondIncident
      faceIndex secondIndex)

/-- Once the actual complete-face collar is cleared, incident parent base selections agree. -/
theorem prismFace_parent_base_mem_iff_of_cleared_collar
    (family : Set.Icc (0 : ℝ) 1 → BoxComplementarityProblem (Fin n))
    (region : Set (UnitCube (Fin n))) (hopen : IsOpen region)
    (radius : ℝ) (hmesh : 1 / (p : ℝ) ≤ radius)
    (hcleared : ¬HasFamilyPrismFaceVertexIn family
      (Metric.cthickening radius (frontier region)) p)
    (face : KuhnPrismFace n p hp (boxComplementarityFamilyPrismLabeling family p hp).label)
    (first second : KuhnPrismCell n p hp)
    (hfirstIncident : kuhnPrismIncident first face)
    (hsecondIncident : kuhnPrismIncident second face) :
    Fin.init (boxComplementarityGridPoint p (first.1 0)) ∈ region ↔
      Fin.init (boxComplementarityGridPoint p (second.1 0)) ∈ region := by
  have himpossible (inside outside : KuhnPrismCell n p hp)
      (hinsideIncident : kuhnPrismIncident inside face)
      (houtsideIncident : kuhnPrismIncident outside face)
      (hinside : Fin.init (boxComplementarityGridPoint p (inside.1 0)) ∈ region)
      (houtside : Fin.init (boxComplementarityGridPoint p (outside.1 0)) ∉ region) : False := by
    apply hcleared
    refine ⟨hp, face, 0, ?_⟩
    exact Metric.cthickening_mono hmesh _
      (prismFace_vertex_mem_frontierCollar_of_parent_membership region hopen face inside outside
        hinsideIncident houtsideIncident 0 0 hinside houtside 0)
  constructor
  · intro hfirst
    by_contra hsecond
    exact himpossible first second hfirstIncident hsecondIncident hfirst hsecond
  · intro hsecond
    by_contra hfirst
    exact himpossible second first hsecondIncident hfirstIncident hsecond hfirst

/-- For a literal jointly continuous family isolated by one region, all incident parents
of every sufficiently fine complete face have the same base-point region selection. -/
theorem IsContinuousBoxComplementarityFamily.eventually_prismFace_parent_base_mem_iff
    {family : Set.Icc (0 : ℝ) 1 → BoxComplementarityProblem (Fin n)}
    (hcontinuous : IsContinuousBoxComplementarityFamily (Fin n) family)
    (region : Set (UnitCube (Fin n)))
    (hisolating : ∀ parameter, (family parameter).IsIsolating region) :
    ∃ threshold, ∀ resolution, threshold ≤ resolution → ∀ hpositive : 0 < resolution,
      ∀ face : KuhnPrismFace n resolution hpositive
          (boxComplementarityFamilyPrismLabeling family resolution hpositive).label,
        ∀ first second : KuhnPrismCell n resolution hpositive,
          kuhnPrismIncident first face → kuhnPrismIncident second face →
            (Fin.init (boxComplementarityGridPoint resolution (first.1 0)) ∈ region ↔
              Fin.init (boxComplementarityGridPoint resolution (second.1 0)) ∈ region) := by
  obtain ⟨radius, hradius, threshold, hcleared⟩ :=
    hcontinuous.exists_isolatingFrontierCollar_eventually_prismCleared region hisolating
  have hmeshZero : Tendsto (fun resolution : ℕ => 1 / (resolution : ℝ)) atTop (nhds 0) := by
    simpa only [one_div, Function.comp_def] using
      tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  obtain ⟨meshThreshold, hmesh⟩ :=
    eventually_atTop.1 (hmeshZero.eventually (eventually_lt_nhds hradius))
  refine ⟨max threshold meshThreshold, ?_⟩
  intro resolution hresolution hpositive face first second hfirst hsecond
  exact prismFace_parent_base_mem_iff_of_cleared_collar family region (hisolating 0).1 radius
    (hmesh resolution ((le_max_right _ _).trans hresolution)).le
    (hcleared resolution ((le_max_left _ _).trans hresolution)) face first second hfirst hsecond

end Math
