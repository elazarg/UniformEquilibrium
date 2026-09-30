import UniformEquilibrium.Quitting.Stationary.GuardedCrossedResponseEscape
import UniformEquilibrium.Quitting.Stationary.GuardedCrossedResponseRawMatrix

/-!
# Total nonzero crossed degree in one explicit signed chart

The isolating exterior selects exactly all nonzero fixed points of the
literal crossed map. Its degree is the whole-cube-normalized integer degree
in the explicit `[-2,2]` chart, not an asserted chart-independent Brouwer
degree. No finiteness or regularity of the nonzero fixed points is needed.
-/

noncomputable section

namespace GameTheory

open Set _root_.Math _root_.Math.Topology _root_.Math.LinearProgramming

variable {n : ℕ}

/-- The complete nonzero fixed-point set of the actual crossed auxiliary map. -/
def quittingCrossedNonzeroFixedPointSet
    (reward : {S : Finset (Fin n) // S.Nonempty} → Payoff (Fin n))
    (first second : Fin n) (height : ℝ) : Set (Fin n → ℝ) :=
  {source | source ≠ 0 ∧ quittingCrossedClippedMap reward first second height source = source}

/-- The open origin neighborhood in the explicit signed global chart. -/
def quittingCrossedGlobalOriginRegion (radius : ℝ) : Set (UnitCube (Fin n)) :=
  quittingCrossedGlobalChart ⁻¹' Metric.ball 0 radius

/-- Global chart solutions are exactly the literal crossed fixed points,
including any fixed points at the auxiliary strategy-box boundary. -/
theorem quittingCrossedGlobalProblem_isSolution_iff_fixedPoint
    (reward : {S : Finset (Fin n) // S.Nonempty} → Payoff (Fin n))
    (first second : Fin n) (height : ℝ) (hheight : 0 ≤ height) (hheightOne : height ≤ 1)
    (point : UnitCube (Fin n)) :
    (quittingCrossedGlobalProblem reward first second height).IsSolution point ↔
      quittingCrossedClippedMap reward first second height (quittingCrossedGlobalChart point) =
        quittingCrossedGlobalChart point := by
  have hmap := (continuous_quittingCrossedClippedMap reward first second height).continuousOn
    (s := Icc (fun _ : Fin n => (-2 : ℝ)) (fun _ => (2 : ℝ)))
  have hself := quittingCrossedClippedMap_mapsTo_globalRectangle
    reward first second height hheight hheightOne
  exact (BoxComplementarityProblem.isSolution_of_selfMap_iff
    (fun _ : Fin n => -2) (fun _ => 2) (by intro; norm_num)
    (quittingCrossedClippedMap reward first second height) hmap hself point).trans eq_comm

private theorem image_globalChart_nonzeroFixedPointSet
    (reward : {S : Finset (Fin n) // S.Nonempty} → Payoff (Fin n))
    (first second : Fin n) (height : ℝ) (hheight : 0 ≤ height) (hheightOne : height ≤ 1) :
    quittingCrossedGlobalChart ''
        (quittingCrossedGlobalChart ⁻¹'
          quittingCrossedNonzeroFixedPointSet reward first second height) =
      quittingCrossedNonzeroFixedPointSet reward first second height := by
  apply Set.Subset.antisymm
  · rintro source ⟨point, hpoint, rfl⟩
    exact hpoint
  · intro source hsource
    have hbox := quittingCrossedClippedMap_fixed_mem_box
      reward first second height hheight source hsource.2
    have hupper (who : Fin n) : source who ≤ 1 := by
      have hceiling : quittingCrossedCeiling first second height who ≤ 1 := by
        unfold quittingCrossedCeiling
        split_ifs <;> linarith
      exact (hbox who).2.trans hceiling
    let point : UnitCube (Fin n) := fun who =>
      ⟨(source who + 2) / 4, by constructor <;> linarith [(hbox who).1, hupper who]⟩
    have hchart : quittingCrossedGlobalChart point = source := by
      funext who
      dsimp [quittingCrossedGlobalChart, rectangularCubePoint, rectangularPoint, point]
      ring
    exact ⟨point, by simpa only [mem_preimage, hchart] using hsource, hchart⟩

/-- A single radius isolates the actual ambient origin, computes its local
index, and gives degree `1−κ(PΓ)` to an open exterior selecting the entire
nonzero fixed-point set. All degree statements use the fixed `[-2,2]` chart. -/
theorem exists_globalCrossed_entireNonzeroSet_degree_eq_one_sub_r0Degree
    (reward : {S : Finset (Fin n) // S.Nonempty} → Payoff (Fin n))
    (first second : Fin n) (height : ℝ) (hheight : 0 < height) (hheightOne : height ≤ 1)
    (hR0 : IsR0Matrix (quittingCrossedSingletonMatrix reward first second)) :
    ∃ radius : ℝ, 0 < radius ∧ radius < 1 ∧
      (∀ source : Fin n → ℝ, ‖source‖ ≤ radius →
        quittingCrossedClippedMap reward first second height source = source → source = 0) ∧
      ∃ horigin : (quittingCrossedGlobalProblem reward first second height).IsIsolating
          (quittingCrossedGlobalOriginRegion radius),
      ∃ houtside : (quittingCrossedGlobalProblem reward first second height).IsIsolating
          (closure (quittingCrossedGlobalOriginRegion radius))ᶜ,
        (quittingCrossedGlobalProblem reward first second height).localDegree
            (quittingCrossedGlobalOriginRegion radius) horigin =
          r0Degree (quittingCrossedSingletonMatrix reward first second) hR0 ∧
        (quittingCrossedGlobalProblem reward first second height).solutionsIn
            (closure (quittingCrossedGlobalOriginRegion radius))ᶜ =
          quittingCrossedGlobalChart ⁻¹'
            quittingCrossedNonzeroFixedPointSet reward first second height ∧
        quittingCrossedGlobalChart ''
            (quittingCrossedGlobalProblem reward first second height).solutionsIn
              (closure (quittingCrossedGlobalOriginRegion radius))ᶜ =
          quittingCrossedNonzeroFixedPointSet reward first second height ∧
        (quittingCrossedGlobalProblem reward first second height).localDegree
            (closure (quittingCrossedGlobalOriginRegion radius))ᶜ houtside =
          1 - r0Degree (quittingCrossedSingletonMatrix reward first second) hR0 := by
  obtain ⟨radius, hradius, hsmall, hisolation, horigin, hdegree⟩ :=
    exists_globalCrossed_originIsolation_localDegree_eq_r0Degree
      reward first second height hheight hR0
  let actual := quittingCrossedGlobalProblem reward first second height
  let region : Set (UnitCube (Fin n)) := quittingCrossedGlobalOriginRegion radius
  let houtside := actual.isIsolating_compl_closure region horigin
  have hclosureSmall (point : UnitCube (Fin n)) (hpoint : point ∈ closure region) :
      ‖quittingCrossedGlobalChart point‖ ≤ radius := by
    have hclosed : IsClosed (quittingCrossedGlobalChart ⁻¹'
        Metric.closedBall (0 : Fin n → ℝ) radius) :=
      Metric.isClosed_closedBall.preimage
        (continuous_rectangularCubePoint (fun _ : Fin n => -2) (fun _ => 2))
    have hsubset : region ⊆ quittingCrossedGlobalChart ⁻¹'
        Metric.closedBall (0 : Fin n → ℝ) radius := by
      intro source hsource
      exact Metric.ball_subset_closedBall hsource
    have hmem := closure_minimal hsubset hclosed hpoint
    simpa only [mem_preimage, Metric.mem_closedBall, dist_zero_right] using hmem
  have hselected : actual.solutionsIn (closure region)ᶜ =
      quittingCrossedGlobalChart ⁻¹'
        quittingCrossedNonzeroFixedPointSet reward first second height := by
    ext point
    change (actual.IsSolution point ∧ point ∉ closure region) ↔
      quittingCrossedGlobalChart point ≠ 0 ∧
        quittingCrossedClippedMap reward first second height (quittingCrossedGlobalChart point) =
          quittingCrossedGlobalChart point
    rw [quittingCrossedGlobalProblem_isSolution_iff_fixedPoint
      reward first second height hheight.le hheightOne point]
    constructor
    · rintro ⟨hfixed, hout⟩
      refine ⟨?_, hfixed⟩
      intro hzero
      apply hout
      apply subset_closure
      change dist (quittingCrossedGlobalChart point) 0 < radius
      simpa only [hzero, dist_self] using hradius
    · rintro ⟨hnonzero, hfixed⟩
      refine ⟨hfixed, ?_⟩
      intro hclosure
      exact hnonzero (hisolation _ (hclosureSmall point hclosure) hfixed)
  refine ⟨radius, hradius, hsmall, hisolation, horigin, houtside, hdegree, hselected, ?_, ?_⟩
  · rw [hselected]
    exact image_globalChart_nonzeroFixedPointSet
      reward first second height hheight.le hheightOne
  · have hlocal : actual.localDegree region horigin =
        r0Degree (quittingCrossedSingletonMatrix reward first second) hR0 := hdegree
    exact (actual.localDegree_compl_closure region horigin).trans
      (congrArg (fun index : ℤ => 1 - index) hlocal)

/-- A positive full singleton determinant and strictly positive inverse give
total nonzero degree two in the same explicit chart, without any raw guards
or assumptions on the number or regularity of nonzero roots. -/
theorem exists_globalCrossed_entireNonzeroSet_degree_two_of_positiveInverse
    (reward : {S : Finset (Fin n) // S.Nonempty} → Payoff (Fin n))
    (first second : Fin n) (hdistinct : first ≠ second)
    (height : ℝ) (hheight : 0 < height) (hheightOne : height ≤ 1)
    (hdet : 0 < (QuittingLCPClassification.quittingSingletonMatrix reward).det)
    (hinverse : ∀ row column,
      0 < (QuittingLCPClassification.quittingSingletonMatrix reward)⁻¹ row column) :
    ∃ radius : ℝ, 0 < radius ∧ radius < 1 ∧
      (∀ source : Fin n → ℝ, ‖source‖ ≤ radius →
        quittingCrossedClippedMap reward first second height source = source → source = 0) ∧
      ∃ houtside : (quittingCrossedGlobalProblem reward first second height).IsIsolating
          (closure (quittingCrossedGlobalOriginRegion radius))ᶜ,
        (quittingCrossedGlobalProblem reward first second height).solutionsIn
            (closure (quittingCrossedGlobalOriginRegion radius))ᶜ =
          quittingCrossedGlobalChart ⁻¹'
            quittingCrossedNonzeroFixedPointSet reward first second height ∧
        quittingCrossedGlobalChart ''
            (quittingCrossedGlobalProblem reward first second height).solutionsIn
              (closure (quittingCrossedGlobalOriginRegion radius))ᶜ =
          quittingCrossedNonzeroFixedPointSet reward first second height ∧
        (quittingCrossedGlobalProblem reward first second height).localDegree
            (closure (quittingCrossedGlobalOriginRegion radius))ᶜ houtside = 2 := by
  obtain ⟨hR0, hindex⟩ := quittingCrossedSingletonMatrix_r0_degree_neg_one_of_positiveInverse
    reward first second hdistinct hdet hinverse
  obtain ⟨radius, hradius, hsmall, hisolation, horigin, houtside,
      -, hselected, himage, hdegree⟩ :=
    exists_globalCrossed_entireNonzeroSet_degree_eq_one_sub_r0Degree
      reward first second height hheight hheightOne hR0
  refine ⟨radius, hradius, hsmall, hisolation, houtside, hselected, himage, ?_⟩
  rw [hdegree, hindex]
  norm_num

end GameTheory
