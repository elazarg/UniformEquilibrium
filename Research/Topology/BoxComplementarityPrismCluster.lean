import Research.Topology.BoxComplementarityFamilyCollar
import Research.Topology.BoxComplementaritySpernerSubdivisionPrism

/-!
# Actual mixed-parameter prism-face clusters

Each external label is evaluated at its own vertex's parameter coordinate.
The existing unit-mesh bound brings all of those vertices to the same limit;
joint continuity and the literal reduced-label inequalities imply that its
spatial coordinate solves the family problem at its parameter coordinate.
For one common isolating region this gives a uniform collar with no spatial
vertex of a complete mixed-time face at every sufficiently fine resolution.
-/

noncomputable section

namespace Math

open Classical Filter Set Topology

variable {n : ℕ}

/-- Parameter sampling uses the same rational grid as the spatial coordinates. -/
def boxComplementarityGridParameter (p : ℕ) (index : Fin (p + 1)) : Set.Icc (0 : ℝ) 1 :=
  boxComplementarityGridPoint p (fun _ : Fin 1 => index) 0

/-- The existing discrete prism labels, sampled from the actual continuous-parameter family. -/
def boxComplementarityFamilyPrismLabeling
    (family : Set.Icc (0 : ℝ) 1 → BoxComplementarityProblem (Fin n))
    (p : ℕ) (hp : 0 < p) : KuhnPrismSpatialBoundaryLabeling n p hp :=
  boxComplementarityDiscretePrismBoundaryLabeling p hp
    (fun index => family (boxComplementarityGridParameter p index))

/-- Any two vertices of an actual prism face remain within one full space-time mesh width. -/
theorem dist_familyPrismFace_vertices_le_one_div
    (family : Set.Icc (0 : ℝ) 1 → BoxComplementarityProblem (Fin n))
    (p : ℕ) (hp : 0 < p)
    (face : KuhnPrismFace n p hp (boxComplementarityFamilyPrismLabeling family p hp).label)
    (first second : Fin (n + 1)) :
    dist (boxComplementarityGridPoint p (face.1 first))
      (boxComplementarityGridPoint p (face.1 second)) ≤ 1 / (p : ℝ) := by
  apply dist_boxComplementarityGridPoint_le_one_div p hp
  intro who
  exact ⟨le_add_one_of_simplex _ face.1 face.2.1 first second who,
    le_add_one_of_simplex _ face.1 face.2.1 second first who⟩

/-- Convergence of one selected face vertex transports to any other selection. -/
theorem tendsto_familyPrismFace_vertex_of_selected
    (family : Set.Icc (0 : ℝ) 1 → BoxComplementarityProblem (Fin n))
    (resolution : ℕ → ℕ) (hpositive : ∀ time, 0 < resolution time)
    (hresolution : Tendsto resolution atTop atTop)
    (faces : ∀ time, KuhnPrismFace n (resolution time) (hpositive time)
      (boxComplementarityFamilyPrismLabeling family
        (resolution time) (hpositive time)).label)
    (selected other : ℕ → Fin (n + 1)) {limit : UnitCube (Fin (n + 1))}
    (hselected : Tendsto (fun time => boxComplementarityGridPoint (resolution time)
      ((faces time).1 (selected time))) atTop (nhds limit)) :
    Tendsto (fun time => boxComplementarityGridPoint (resolution time)
      ((faces time).1 (other time))) atTop (nhds limit) := by
  have hmesh : Tendsto (fun time => 1 / (resolution time : ℝ)) atTop (nhds 0) := by
    simpa only [one_div, Function.comp_def] using
      tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop.comp hresolution)
  apply hselected.congr_dist
  apply squeeze_zero' (Eventually.of_forall fun _ => dist_nonneg)
    (Eventually.of_forall fun time => ?_) hmesh
  exact dist_familyPrismFace_vertices_le_one_div family (resolution time)
    (hpositive time) (faces time) (selected time) (other time)

/-- The label-dimension vertex has nonnegative coordinate-times-gain at every coordinate. -/
theorem mul_gain_nonneg_of_reducedLabel_eq_dimension
    (problem : BoxComplementarityProblem (Fin n)) (p : ℕ)
    (vertex : Fin n → Fin (p + 1))
    (hlabel : boxComplementarityReducedLabel problem p vertex = n) (who : Fin n) :
    0 ≤ (boxComplementarityGridPoint p vertex who : ℝ) *
      problem.gain (boxComplementarityGridPoint p vertex) who := by
  by_cases hzero : (boxComplementarityGridPoint p vertex who : ℝ) = 0
  · rw [hzero, zero_mul]
  apply mul_nonneg (boxComplementarityGridPoint p vertex who).property.1
  apply le_of_not_gt
  intro hnegative
  have hviolation : problem.IsGridViolation p vertex who := Or.inl
    ⟨lt_of_le_of_ne (boxComplementarityGridPoint p vertex who).property.1 (Ne.symm hzero),
      hnegative⟩
  have hbound := (boxComplementarityReducedLabel_properties problem p vertex).2 who |>.2
    hviolation
  rw [hlabel] at hbound
  exact (Nat.not_le_of_lt who.isLt) hbound

/-- A coordinate-labeled vertex has nonpositive complementary-coordinate-times-gain. -/
theorem one_sub_mul_gain_nonpos_of_reducedLabel_eq_coordinate
    (problem : BoxComplementarityProblem (Fin n)) (p : ℕ)
    (vertex : Fin n → Fin (p + 1)) (who : Fin n)
    (hlabel : boxComplementarityReducedLabel problem p vertex = who.val) :
    (1 - (boxComplementarityGridPoint p vertex who : ℝ)) *
      problem.gain (boxComplementarityGridPoint p vertex) who ≤ 0 := by
  have hviolation := (boxComplementarityReducedLabel_properties problem p vertex).2 who |>.1
    hlabel
  rcases hviolation with hnegative | hone
  · exact mul_nonpos_of_nonneg_of_nonpos
      (sub_nonneg.mpr (boxComplementarityGridPoint p vertex who).property.2) hnegative.2.le
  · change (boxComplementarityGridPoint p vertex who : ℝ) = 1 at hone
    rw [hone, sub_self, zero_mul]

/-- A cluster of actual mixed-time complete prism faces is a solution at that same parameter. -/
theorem IsContinuousBoxComplementarityFamily.isSolution_of_prismFace_vertex_tendsto
    {family : Set.Icc (0 : ℝ) 1 → BoxComplementarityProblem (Fin n)}
    (hcontinuous : IsContinuousBoxComplementarityFamily (Fin n) family)
    (resolution : ℕ → ℕ) (hpositive : ∀ time, 0 < resolution time)
    (hresolution : Tendsto resolution atTop atTop)
    (faces : ∀ time, KuhnPrismFace n (resolution time) (hpositive time)
      (boxComplementarityFamilyPrismLabeling family
        (resolution time) (hpositive time)).label)
    (selected : ℕ → Fin (n + 1)) {limit : UnitCube (Fin (n + 1))}
    (hselected : Tendsto (fun time => boxComplementarityGridPoint (resolution time)
      ((faces time).1 (selected time))) atTop (nhds limit)) :
    (family (limit (Fin.last n))).IsSolution (Fin.init limit) := by
  have hsurjective : ∀ time, Function.Surjective (fun index =>
      (boxComplementarityFamilyPrismLabeling family (resolution time) (hpositive time)).label
        ((faces time).1 index)) := fun time =>
    ((Fintype.bijective_iff_injective_and_card _).2 ⟨(faces time).2.2, rfl⟩).2
  choose anchor hanchorLabel using fun time => hsurjective time (Fin.last n)
  rw [(family (limit (Fin.last n))).isSolution_iff_mul_gain]
  intro who
  choose coordinate hcoordinateLabel using fun time => hsurjective time who.castSucc
  have hanchor := tendsto_familyPrismFace_vertex_of_selected family resolution hpositive
    hresolution faces selected anchor hselected
  have hcoordinate := tendsto_familyPrismFace_vertex_of_selected family resolution hpositive
    hresolution faces selected coordinate hselected
  have hcoordinateContinuous : Continuous
      (fun point : UnitCube (Fin (n + 1)) => (point who.castSucc : ℝ)) :=
    continuous_subtype_val.comp (continuous_apply who.castSucc)
  have hparameterSpatial : Continuous (fun point : UnitCube (Fin (n + 1)) =>
      (point (Fin.last n), Fin.init point)) :=
    (continuous_apply (Fin.last n)).prodMk
      (continuous_pi fun index => continuous_apply index.castSucc)
  have hgain : Continuous (fun point : UnitCube (Fin (n + 1)) =>
      (family (point (Fin.last n))).gain (Fin.init point) who) :=
    (hcontinuous who).comp hparameterSpatial
  constructor
  · apply ge_of_tendsto ((hcoordinateContinuous.mul hgain).tendsto limit |>.comp hanchor)
    apply Eventually.of_forall
    intro time
    exact mul_gain_nonneg_of_reducedLabel_eq_dimension
      (family (boxComplementarityGridParameter (resolution time)
        ((faces time).1 (anchor time) (Fin.last n)))) (resolution time)
      (Fin.init ((faces time).1 (anchor time))) (congrArg Fin.val (hanchorLabel time)) who
  · apply le_of_tendsto (((continuous_const.sub hcoordinateContinuous).mul hgain).tendsto
      limit |>.comp hcoordinate)
    apply Eventually.of_forall
    intro time
    exact one_sub_mul_gain_nonpos_of_reducedLabel_eq_coordinate
      (family (boxComplementarityGridParameter (resolution time)
        ((faces time).1 (coordinate time) (Fin.last n)))) (resolution time)
      (Fin.init ((faces time).1 (coordinate time))) who
      (congrArg Fin.val (hcoordinateLabel time))

/-- An actual complete mixed-time face has a spatial grid vertex in the displayed set. -/
def HasFamilyPrismFaceVertexIn
    (family : Set.Icc (0 : ℝ) 1 → BoxComplementarityProblem (Fin n))
    (target : Set (UnitCube (Fin n))) (p : ℕ) : Prop :=
  ∃ hp : 0 < p,
    ∃ face : KuhnPrismFace n p hp (boxComplementarityFamilyPrismLabeling family p hp).label,
      ∃ index : Fin (n + 1),
        Fin.init (boxComplementarityGridPoint p (face.1 index)) ∈ target

/-- A compact spatial set avoiding every actual family solution is uniformly cleared of
mixed-time complete prism faces at every sufficiently fine positive mesh. -/
theorem IsContinuousBoxComplementarityFamily.eventually_no_prismFaceVertexIn_of_compact
    {family : Set.Icc (0 : ℝ) 1 → BoxComplementarityProblem (Fin n)}
    (hcontinuous : IsContinuousBoxComplementarityFamily (Fin n) family)
    (target : Set (UnitCube (Fin n))) (hcompact : IsCompact target)
    (hdisjoint : ∀ parameter, Disjoint target (family parameter).solutionSet) :
    ∃ threshold, ∀ p, threshold ≤ p → ¬HasFamilyPrismFaceVertexIn family target p := by
  by_contra hfailure
  push Not at hfailure
  choose resolution hlower hwitness using hfailure
  choose hpositive faces selected hselected using hwitness
  have hresolution : Tendsto resolution atTop atTop := by
    rw [tendsto_atTop]
    intro lower
    filter_upwards [eventually_ge_atTop lower] with time htime
    exact htime.trans (hlower time)
  have hspatial : Continuous (Fin.init : UnitCube (Fin (n + 1)) → UnitCube (Fin n)) :=
    continuous_pi fun index => continuous_apply index.castSucc
  have hfullCompact : IsCompact
      {point : UnitCube (Fin (n + 1)) | Fin.init point ∈ target} :=
    (hcompact.isClosed.preimage hspatial).isCompact
  obtain ⟨limit, hlimit, subseq, hsubseq, htendsto⟩ := hfullCompact.tendsto_subseq hselected
  have hsolution := hcontinuous.isSolution_of_prismFace_vertex_tendsto
    (resolution ∘ subseq) (fun time => hpositive (subseq time))
    (hresolution.comp hsubseq.tendsto_atTop) (fun time => faces (subseq time))
    (selected ∘ subseq) htendsto
  exact Set.disjoint_left.1 (hdisjoint (limit (Fin.last n))) hlimit hsolution

/-- A single isolating region for the actual continuous family has a uniform
collar containing no spatial vertex of any complete mixed-time prism face at
all sufficiently fine positive resolutions. -/
theorem IsContinuousBoxComplementarityFamily.exists_isolatingFrontierCollar_eventually_prismCleared
    {family : Set.Icc (0 : ℝ) 1 → BoxComplementarityProblem (Fin n)}
    (hcontinuous : IsContinuousBoxComplementarityFamily (Fin n) family)
    (region : Set (UnitCube (Fin n)))
    (hisolating : ∀ parameter, (family parameter).IsIsolating region) :
    ∃ radius : ℝ, 0 < radius ∧
      ∃ threshold, ∀ p, threshold ≤ p →
        ¬HasFamilyPrismFaceVertexIn family
          (Metric.cthickening radius (frontier region)) p := by
  obtain ⟨radius, hradius, hcompact, hdisjoint⟩ :=
    hcontinuous.exists_uniform_isolatingFrontierCollar region hisolating
  obtain ⟨threshold, hcleared⟩ :=
    hcontinuous.eventually_no_prismFaceVertexIn_of_compact _ hcompact hdisjoint
  exact ⟨radius, hradius, threshold, hcleared⟩

end Math
