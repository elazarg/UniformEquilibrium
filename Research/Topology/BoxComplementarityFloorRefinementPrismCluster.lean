import Research.Topology.BoxComplementarityFloorRefinementPrism
import Research.Topology.BoxComplementarityPrismCluster

/-! # Mixed floor-refinement prism-face clusters -/

noncomputable section

namespace Math

open Classical Filter Set Topology

variable {n : ℕ}

/-- The spatial point at which one mixed prism label is actually sampled:
the rounded coarse point on the left end and the fine point elsewhere. -/
def boxComplementarityFloorRefinementLabelSamplePoint
    (p k : ℕ) (vertex : Fin (n + 1) → Fin (p * k + 1)) :
    UnitCube (Fin n) :=
  if vertex (Fin.last n) = 0 then
    boxComplementarityGridPoint p
      (fun who ↦ kuhnFloorCoordinate p k (vertex who.castSucc))
  else
    boxComplementarityGridPoint (p * k) (Fin.init vertex)

theorem boxComplementarityFloorRefinementPrism_label_of_parameter_eq_zero
    (problem : BoxComplementarityProblem (Fin n))
    (p k : ℕ) (hp : 0 < p) (hk : 0 < k)
    (vertex : (kuhnPrismGeometryCube n (p * k) (Nat.mul_pos hp hk)).G)
    (hparameter : vertex (Fin.last n) = 0) :
    (boxComplementarityFloorRefinementPrism problem p k hp hk).label vertex =
      boxComplementarityFinLabel problem p
        (fun who ↦ kuhnFloorCoordinate p k (vertex who.castSucc)) := by
  rw [boxComplementarityFloorRefinementPrism, externalCubeLabelPrism]
  simp only [hparameter, if_pos]
  exact boxComplementarityFloorPullbackBoundaryLabeling_label problem p k hp hk _

theorem boxComplementarityFloorRefinementPrism_label_of_parameter_ne_zero
    (problem : BoxComplementarityProblem (Fin n))
    (p k : ℕ) (hp : 0 < p) (hk : 0 < k)
    (vertex : (kuhnPrismGeometryCube n (p * k) (Nat.mul_pos hp hk)).G)
    (hparameter : vertex (Fin.last n) ≠ 0) :
    (boxComplementarityFloorRefinementPrism problem p k hp hk).label vertex =
      boxComplementarityFinLabel problem (p * k) (Fin.init vertex) := by
  rw [boxComplementarityFloorRefinementPrism, externalCubeLabelPrism]
  simp only [hparameter, if_false]
  rfl

/-- Every mixed label sample is within one coarse mesh width of its literal
fine-grid spatial point. -/
theorem dist_floorRefinementLabelSamplePoint_fine_le_one_div
    (p k : ℕ) (hp : 0 < p) (hk : 0 < k)
    (vertex : Fin (n + 1) → Fin (p * k + 1)) :
    dist (boxComplementarityFloorRefinementLabelSamplePoint p k vertex)
      (boxComplementarityGridPoint (p * k) (Fin.init vertex)) ≤
        1 / (p : ℝ) := by
  unfold boxComplementarityFloorRefinementLabelSamplePoint
  split_ifs with hparameter
  · rw [dist_comm]
    simpa only [Fin.init] using
      dist_boxComplementarityGridPoint_kuhnFloor_le_one_div
        p k hp hk (Fin.init vertex)
  · simp

/-- Fine spatial vertices of one mixed prism face are at most one fine mesh
width apart. -/
theorem dist_floorRefinementPrismFace_fineVertices_le_one_div
    (problem : BoxComplementarityProblem (Fin n))
    (p k : ℕ) (hp : 0 < p) (hk : 0 < k)
    (face : KuhnPrismFace n (p * k) (Nat.mul_pos hp hk)
      (boxComplementarityFloorRefinementPrism problem p k hp hk).label)
    (first second : Fin (n + 1)) :
    dist (boxComplementarityGridPoint (p * k) (Fin.init (face.1 first)))
      (boxComplementarityGridPoint (p * k) (Fin.init (face.1 second))) ≤
        1 / ((p * k : ℕ) : ℝ) := by
  apply dist_boxComplementarityGridPoint_le_one_div (p * k) (Nat.mul_pos hp hk)
  intro who
  exact ⟨le_add_one_of_simplex _ face.1 face.2.1 first second who.castSucc,
    le_add_one_of_simplex _ face.1 face.2.1 second first who.castSucc⟩

private theorem one_div_mul_le_one_div_left
    (p k : ℕ) (hp : 0 < p) (hk : 0 < k) :
    1 / (p * k : ℝ) ≤ 1 / (p : ℝ) := by
  apply one_div_le_one_div_of_le (Nat.cast_pos.mpr hp)
  exact_mod_cast calc
    p = p * 1 := by omega
    _ ≤ p * k := Nat.mul_le_mul_left p (Nat.one_le_iff_ne_zero.2 hk.ne')

/-- Any two label-sampling points of one complete mixed face are within three
coarse mesh widths, uniformly in the positive refinement factor. -/
theorem dist_floorRefinementPrismFace_labelSamplePoints_le_three_div
    (problem : BoxComplementarityProblem (Fin n))
    (p k : ℕ) (hp : 0 < p) (hk : 0 < k)
    (face : KuhnPrismFace n (p * k) (Nat.mul_pos hp hk)
      (boxComplementarityFloorRefinementPrism problem p k hp hk).label)
    (first second : Fin (n + 1)) :
    dist (boxComplementarityFloorRefinementLabelSamplePoint p k (face.1 first))
      (boxComplementarityFloorRefinementLabelSamplePoint p k (face.1 second)) ≤
        3 / (p : ℝ) := by
  calc
    dist (boxComplementarityFloorRefinementLabelSamplePoint p k (face.1 first))
        (boxComplementarityFloorRefinementLabelSamplePoint p k (face.1 second)) ≤
      dist (boxComplementarityFloorRefinementLabelSamplePoint p k (face.1 first))
          (boxComplementarityGridPoint (p * k) (Fin.init (face.1 first))) +
        dist (boxComplementarityGridPoint (p * k) (Fin.init (face.1 first)))
          (boxComplementarityFloorRefinementLabelSamplePoint p k
            (face.1 second)) := dist_triangle _ _ _
    _ ≤ 1 / (p : ℝ) +
        (dist (boxComplementarityGridPoint (p * k) (Fin.init (face.1 first)))
            (boxComplementarityGridPoint (p * k) (Fin.init (face.1 second))) +
          dist (boxComplementarityGridPoint (p * k) (Fin.init (face.1 second)))
            (boxComplementarityFloorRefinementLabelSamplePoint p k
              (face.1 second))) := by
      apply add_le_add
      · exact dist_floorRefinementLabelSamplePoint_fine_le_one_div
          p k hp hk (face.1 first)
      · exact dist_triangle _ _ _
    _ ≤ 1 / (p : ℝ) + (1 / (p * k : ℝ) + 1 / (p : ℝ)) := by
      have hlast := dist_floorRefinementLabelSamplePoint_fine_le_one_div
        p k hp hk (face.1 second)
      rw [dist_comm] at hlast
      have hmiddle := dist_floorRefinementPrismFace_fineVertices_le_one_div
        problem p k hp hk face first second
      rw [Nat.cast_mul] at hmiddle
      exact add_le_add_right (add_le_add hmiddle hlast) _
    _ ≤ 1 / (p : ℝ) + (1 / (p : ℝ) + 1 / (p : ℝ)) := by
      exact add_le_add_right
        (add_le_add (one_div_mul_le_one_div_left p k hp hk) le_rfl) _
    _ = 3 / (p : ℝ) := by ring

/-- A dimension-labeled mixed vertex has nonnegative coordinate-times-gain
at the point where its label was sampled. -/
theorem mul_gain_nonneg_of_floorRefinementPrism_label_eq_dimension
    (problem : BoxComplementarityProblem (Fin n))
    (p k : ℕ) (hp : 0 < p) (hk : 0 < k)
    (vertex : (kuhnPrismGeometryCube n (p * k) (Nat.mul_pos hp hk)).G)
    (hlabel : (boxComplementarityFloorRefinementPrism
      problem p k hp hk).label vertex = Fin.last n)
    (who : Fin n) :
    0 ≤ (boxComplementarityFloorRefinementLabelSamplePoint p k vertex who : ℝ) *
      problem.gain
        (boxComplementarityFloorRefinementLabelSamplePoint p k vertex) who := by
  by_cases hparameter : vertex (Fin.last n) = 0
  · rw [boxComplementarityFloorRefinementPrism_label_of_parameter_eq_zero
      problem p k hp hk vertex hparameter] at hlabel
    have hlabelValue := congrArg Fin.val hlabel
    simp only [boxComplementarityFinLabel_val, Fin.val_last] at hlabelValue
    have hsample : boxComplementarityFloorRefinementLabelSamplePoint p k vertex =
        boxComplementarityGridPoint p
          (fun index ↦ kuhnFloorCoordinate p k (vertex index.castSucc)) := by
      exact if_pos hparameter
    rw [hsample]
    exact mul_gain_nonneg_of_reducedLabel_eq_dimension problem p _ hlabelValue who
  · rw [boxComplementarityFloorRefinementPrism_label_of_parameter_ne_zero
      problem p k hp hk vertex hparameter] at hlabel
    have hlabelValue := congrArg Fin.val hlabel
    simp only [boxComplementarityFinLabel_val, Fin.val_last] at hlabelValue
    have hsample : boxComplementarityFloorRefinementLabelSamplePoint p k vertex =
        boxComplementarityGridPoint (p * k) (Fin.init vertex) := by
      exact if_neg hparameter
    rw [hsample]
    exact mul_gain_nonneg_of_reducedLabel_eq_dimension
      problem (p * k) _ hlabelValue who

/-- A coordinate-labeled mixed vertex has nonpositive complementary-coordinate
times gain at the point where its label was sampled. -/
theorem one_sub_mul_gain_nonpos_of_floorRefinementPrism_label_eq_coordinate
    (problem : BoxComplementarityProblem (Fin n))
    (p k : ℕ) (hp : 0 < p) (hk : 0 < k)
    (vertex : (kuhnPrismGeometryCube n (p * k) (Nat.mul_pos hp hk)).G)
    (who : Fin n)
    (hlabel : (boxComplementarityFloorRefinementPrism
      problem p k hp hk).label vertex = who.castSucc) :
    (1 - (boxComplementarityFloorRefinementLabelSamplePoint p k vertex who : ℝ)) *
      problem.gain
        (boxComplementarityFloorRefinementLabelSamplePoint p k vertex) who ≤ 0 := by
  by_cases hparameter : vertex (Fin.last n) = 0
  · rw [boxComplementarityFloorRefinementPrism_label_of_parameter_eq_zero
      problem p k hp hk vertex hparameter] at hlabel
    have hlabelValue := congrArg Fin.val hlabel
    simp only [boxComplementarityFinLabel_val, Fin.val_castSucc] at hlabelValue
    have hsample : boxComplementarityFloorRefinementLabelSamplePoint p k vertex =
        boxComplementarityGridPoint p
          (fun index ↦ kuhnFloorCoordinate p k (vertex index.castSucc)) := by
      exact if_pos hparameter
    rw [hsample]
    exact one_sub_mul_gain_nonpos_of_reducedLabel_eq_coordinate
      problem p _ who hlabelValue
  · rw [boxComplementarityFloorRefinementPrism_label_of_parameter_ne_zero
      problem p k hp hk vertex hparameter] at hlabel
    have hlabelValue := congrArg Fin.val hlabel
    simp only [boxComplementarityFinLabel_val, Fin.val_castSucc] at hlabelValue
    have hsample : boxComplementarityFloorRefinementLabelSamplePoint p k vertex =
        boxComplementarityGridPoint (p * k) (Fin.init vertex) := by
      exact if_neg hparameter
    rw [hsample]
    exact one_sub_mul_gain_nonpos_of_reducedLabel_eq_coordinate
      problem (p * k) _ who hlabelValue

/-- Convergence of one label-sampling point on each complete mixed face
transports to any other selection, uniformly over varying positive factors. -/
theorem tendsto_floorRefinementPrismFace_labelSamplePoint_of_selected
    (problem : BoxComplementarityProblem (Fin n))
    (p k : ℕ → ℕ) (hp : ∀ time, 0 < p time) (hk : ∀ time, 0 < k time)
    (hpTop : Tendsto p atTop atTop)
    (faces : ∀ time, KuhnPrismFace n (p time * k time)
      (Nat.mul_pos (hp time) (hk time))
      (boxComplementarityFloorRefinementPrism
        problem (p time) (k time) (hp time) (hk time)).label)
    (selected other : ℕ → Fin (n + 1)) {limit : UnitCube (Fin n)}
    (hselected : Tendsto (fun time ↦
      boxComplementarityFloorRefinementLabelSamplePoint
        (p time) (k time) ((faces time).1 (selected time)))
      atTop (nhds limit)) :
    Tendsto (fun time ↦ boxComplementarityFloorRefinementLabelSamplePoint
      (p time) (k time) ((faces time).1 (other time)))
      atTop (nhds limit) := by
  have hpReal : Tendsto (fun time ↦ (p time : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hpTop
  have hinverse : Tendsto (fun time ↦ (p time : ℝ)⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp hpReal
  have hthree : Tendsto (fun _ : ℕ ↦ (3 : ℝ)) atTop (nhds 3) :=
    tendsto_const_nhds
  have hmesh : Tendsto (fun time ↦ 3 / (p time : ℝ)) atTop (nhds 0) := by
    simpa only [div_eq_mul_inv, mul_zero] using
      hthree.mul hinverse
  apply hselected.congr_dist
  apply squeeze_zero' (Eventually.of_forall fun _ ↦ dist_nonneg)
    (Eventually.of_forall fun time ↦ ?_) hmesh
  exact dist_floorRefinementPrismFace_labelSamplePoints_le_three_div
    problem (p time) (k time) (hp time) (hk time) (faces time)
      (selected time) (other time)

/-- A cluster of actual label-sampling points on complete floor-refinement
faces is an actual solution of the fixed problem, even when factors vary. -/
theorem BoxComplementarityProblem.isSolution_of_floorRefinementPrismFace_sample_tendsto
    (problem : BoxComplementarityProblem (Fin n))
    (p k : ℕ → ℕ) (hp : ∀ time, 0 < p time) (hk : ∀ time, 0 < k time)
    (hpTop : Tendsto p atTop atTop)
    (faces : ∀ time, KuhnPrismFace n (p time * k time)
      (Nat.mul_pos (hp time) (hk time))
      (boxComplementarityFloorRefinementPrism
        problem (p time) (k time) (hp time) (hk time)).label)
    (selected : ℕ → Fin (n + 1)) {limit : UnitCube (Fin n)}
    (hselected : Tendsto (fun time ↦
      boxComplementarityFloorRefinementLabelSamplePoint
        (p time) (k time) ((faces time).1 (selected time)))
      atTop (nhds limit)) :
    problem.IsSolution limit := by
  have hsurjective : ∀ time, Function.Surjective (fun index ↦
      (boxComplementarityFloorRefinementPrism
        problem (p time) (k time) (hp time) (hk time)).label
          ((faces time).1 index)) := fun time ↦
    ((Fintype.bijective_iff_injective_and_card _).2
      ⟨(faces time).2.2, rfl⟩).2
  choose anchor hanchorLabel using fun time ↦
    hsurjective time (Fin.last n)
  rw [problem.isSolution_iff_mul_gain]
  intro who
  choose coordinate hcoordinateLabel using fun time ↦
    hsurjective time who.castSucc
  have hanchor :=
    tendsto_floorRefinementPrismFace_labelSamplePoint_of_selected
      problem p k hp hk hpTop faces selected anchor hselected
  have hcoordinate :=
    tendsto_floorRefinementPrismFace_labelSamplePoint_of_selected
      problem p k hp hk hpTop faces selected coordinate hselected
  have hcoordinateContinuous : Continuous
      (fun point : UnitCube (Fin n) ↦ (point who : ℝ)) :=
    continuous_subtype_val.comp (continuous_apply who)
  constructor
  · apply ge_of_tendsto
      ((hcoordinateContinuous.mul (problem.continuous_gain who)).tendsto limit
        |>.comp hanchor)
    apply Eventually.of_forall
    intro time
    exact mul_gain_nonneg_of_floorRefinementPrism_label_eq_dimension
      problem (p time) (k time) (hp time) (hk time)
        ((faces time).1 (anchor time)) (hanchorLabel time) who
  · apply le_of_tendsto
      (((continuous_const.sub hcoordinateContinuous).mul
        (problem.continuous_gain who)).tendsto limit |>.comp hcoordinate)
    apply Eventually.of_forall
    intro time
    exact one_sub_mul_gain_nonpos_of_floorRefinementPrism_label_eq_coordinate
      problem (p time) (k time) (hp time) (hk time)
        ((faces time).1 (coordinate time)) who (hcoordinateLabel time)

/-- Some actual label-sampling point of a complete floor-refinement face lies
in the displayed spatial target. -/
def HasFloorRefinementPrismFaceSampleIn
    (problem : BoxComplementarityProblem (Fin n))
    (target : Set (UnitCube (Fin n))) (p k : ℕ) : Prop :=
  ∃ hp : 0 < p, ∃ hk : 0 < k,
    ∃ face : KuhnPrismFace n (p * k) (Nat.mul_pos hp hk)
      (boxComplementarityFloorRefinementPrism problem p k hp hk).label,
      ∃ index : Fin (n + 1),
        boxComplementarityFloorRefinementLabelSamplePoint
          p k (face.1 index) ∈ target

/-- A compact set disjoint from the solution set is eventually cleared of all
actual samples on complete floor-refinement faces, uniformly over positive
refinement factors. -/
theorem BoxComplementarityProblem.eventually_no_floorRefinementPrismFaceSampleIn_of_compact
    (problem : BoxComplementarityProblem (Fin n))
    (target : Set (UnitCube (Fin n))) (hcompact : IsCompact target)
    (hdisjoint : Disjoint target problem.solutionSet) :
    ∃ threshold, ∀ p k, threshold ≤ p →
      ¬HasFloorRefinementPrismFaceSampleIn problem target p k := by
  by_contra hfailure
  push Not at hfailure
  choose p k hlower hwitness using hfailure
  choose hp hk faces selected hselected using hwitness
  have hpTop : Tendsto p atTop atTop := by
    rw [tendsto_atTop]
    intro lower
    filter_upwards [eventually_ge_atTop lower] with time htime
    exact htime.trans (hlower time)
  obtain ⟨limit, hlimit, subseq, hsubseq, htendsto⟩ :=
    hcompact.tendsto_subseq hselected
  have hsolution :=
    problem.isSolution_of_floorRefinementPrismFace_sample_tendsto
      (p ∘ subseq) (k ∘ subseq) (fun time ↦ hp (subseq time))
      (fun time ↦ hk (subseq time)) (hpTop.comp hsubseq.tendsto_atTop)
      (fun time ↦ faces (subseq time)) (selected ∘ subseq) htendsto
  exact Set.disjoint_left.1 hdisjoint hlimit hsolution

/-- An isolating frontier has a positive compact collar containing no actual
sample from a complete floor-refinement face at every sufficiently large
coarse resolution, uniformly over positive refinement factors. -/
theorem BoxComplementarityProblem.exists_isolatingFrontierCollar_eventually_floorRefinementCleared
    (problem : BoxComplementarityProblem (Fin n))
    (region : Set (UnitCube (Fin n)))
    (hisolating : problem.IsIsolating region) :
    ∃ radius : ℝ, 0 < radius ∧
      ∃ threshold, ∀ p k, threshold ≤ p →
        ¬HasFloorRefinementPrismFaceSampleIn problem
          (Metric.cthickening radius (frontier region)) p k := by
  obtain ⟨radius, hradius, hcompact, hdisjoint⟩ :=
    problem.exists_compact_isolatingFrontierCollar region hisolating
  obtain ⟨threshold, hcleared⟩ :=
    problem.eventually_no_floorRefinementPrismFaceSampleIn_of_compact
      (Metric.cthickening radius (frontier region)) hcompact hdisjoint
  exact ⟨radius, hradius, threshold, hcleared⟩

end Math
