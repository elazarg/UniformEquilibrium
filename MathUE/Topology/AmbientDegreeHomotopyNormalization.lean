import MathUE.Topology.AmbientDegree
import MathUE.Topology.BoxComplementarityAffineLocalIndex
import Mathlib.Topology.TietzeExtension

/-!
# Ambient degree homotopy and orientation normalization

The source field is continuous only on the product of the unit time interval
and the source closure. One product-space Tietze extension, not independent
slice choices, supplies the jointly continuous complementarity family.
Endpoint invariance delegates to the existing stabilized signed-count theorem.

The affine computation delegates to the existing determinant-sign local index.
In particular, the translated identity has degree one, including dimension zero.
-/

noncomputable section

namespace Math.Topology

open Set

/-- Extend the joint source field once on the closed time-space product.
No boundedness, nonemptiness, or positive dimension is needed here. -/
theorem exists_jointContinuousExtension
    {ι : Type} [Fintype ι] (region : Set (ι → ℝ))
    (field : (ℝ × (ι → ℝ)) → ι → ℝ)
    (hfield : ContinuousOn field (Icc (0 : ℝ) 1 ×ˢ closure region)) :
    ∃ extension : C(ℝ × (ι → ℝ), ι → ℝ),
      EqOn extension field (Icc (0 : ℝ) 1 ×ˢ closure region) := by
  let source : C(Icc (0 : ℝ) 1 ×ˢ closure region, ι → ℝ) :=
    ⟨(Icc (0 : ℝ) 1 ×ˢ closure region).domRestrict field, hfield.domRestrict⟩
  obtain ⟨extension, hextension⟩ :=
    ContinuousMap.exists_restrict_eq (isClosed_Icc.prod isClosed_closure) source
  refine ⟨extension, ?_⟩
  intro point hpoint
  exact congrArg
    (fun map : C(Icc (0 : ℝ) 1 ×ˢ closure region, ι → ℝ) => map ⟨point, hpoint⟩)
    hextension

/-- Joint source continuity supplies continuity of each source slice on the closure. -/
theorem continuousOn_jointField_slice
    {ι : Type} (region : Set (ι → ℝ))
    (field : (ℝ × (ι → ℝ)) → ι → ℝ)
    (hfield : ContinuousOn field (Icc (0 : ℝ) 1 ×ˢ closure region))
    (parameter : Icc (0 : ℝ) 1) :
    ContinuousOn (fun point => field ((parameter : ℝ), point)) (closure region) :=
  hfield.comp (continuous_const.prodMk continuous_id).continuousOn
    (fun _ hpoint => ⟨parameter.property, hpoint⟩)

/-- The actual pulled-back problem from a slice of one jointly continuous extension. -/
def jointAmbientProblem {n : ℕ}
    (lower upper : Fin n → ℝ) (hwidth : ∀ who, lower who < upper who)
    (extension : C(ℝ × (Fin n → ℝ), Fin n → ℝ)) (target : Fin n → ℝ)
    (parameter : Icc (0 : ℝ) 1) : Math.BoxComplementarityProblem (Fin n) :=
  Math.BoxComplementarityProblem.ofAmbientMap lower upper hwidth
    (fun point => extension ((parameter : ℝ), point) - target)
    (((extension.continuous.comp
      (continuous_const.prodMk continuous_id)).continuousOn).sub continuousOn_const)

/-- The joint extension produces a genuinely jointly continuous problem family. -/
theorem isContinuous_jointAmbientProblem {n : ℕ}
    (lower upper : Fin n → ℝ) (hwidth : ∀ who, lower who < upper who)
    (extension : C(ℝ × (Fin n → ℝ), Fin n → ℝ)) (target : Fin n → ℝ) :
    Math.IsContinuousBoxComplementarityFamily (Fin n)
      (jointAmbientProblem lower upper hwidth extension target) := by
  intro who
  have hpoint : Continuous (fun data : Icc (0 : ℝ) 1 × Math.UnitCube (Fin n) =>
      ((data.1 : ℝ), rectangularCubePoint lower upper data.2)) :=
    (continuous_subtype_val.comp continuous_fst).prodMk
      ((continuous_rectangularCubePoint lower upper).comp continuous_snd)
  exact (((continuous_apply who).comp (extension.continuous.comp hpoint)).sub
    continuous_const).neg

/-- All slices of the one extension are isolating under the literal source
frontier hypothesis. The source field itself need not extend continuously
outside its closed time-space domain. -/
theorem isIsolating_jointAmbientProblem {n : ℕ}
    (field : (ℝ × (Fin n → ℝ)) → Fin n → ℝ)
    (region : Set (Fin n → ℝ)) (target : Fin n → ℝ) (hopen : IsOpen region)
    (hfrontier : ∀ parameter : Icc (0 : ℝ) 1,
      ∀ point ∈ frontier region, field ((parameter : ℝ), point) ≠ target)
    (lower upper : Fin n → ℝ) (hwidth : ∀ who, lower who < upper who)
    (hclosure : closure region ⊆
      {point | ∀ who, lower who < point who ∧ point who < upper who})
    (extension : C(ℝ × (Fin n → ℝ), Fin n → ℝ))
    (hEqual : EqOn extension field (Icc (0 : ℝ) 1 ×ˢ closure region))
    (parameter : Icc (0 : ℝ) 1) :
    (jointAmbientProblem lower upper hwidth extension target parameter).IsIsolating
      (rectangularCubePoint lower upper ⁻¹' region) :=
  isIsolating_ambientExtension
    (fun point => field ((parameter : ℝ), point)) region target hopen (hfrontier parameter)
    lower upper hwidth hclosure (fun point => extension ((parameter : ℝ), point))
    (extension.continuous.comp (continuous_const.prodMk continuous_id)).continuousOn
    (fun _ hpoint => hEqual ⟨parameter.property, hpoint⟩)

/-- Source-local homotopy invariance of the intrinsic degree. One jointly
continuous extension supplies both endpoints and every intermediate slice. -/
theorem ambientDegree_homotopy {n : ℕ}
    (field : (ℝ × (Fin n → ℝ)) → Fin n → ℝ)
    (region : Set (Fin n → ℝ)) (target : Fin n → ℝ)
    (hopen : IsOpen region) (hbounded : Bornology.IsBounded region)
    (hfield : ContinuousOn field (Icc (0 : ℝ) 1 ×ˢ closure region))
    (hfrontier : ∀ parameter : Icc (0 : ℝ) 1,
      ∀ point ∈ frontier region, field ((parameter : ℝ), point) ≠ target) :
    ambientDegree (fun point => field (0, point)) region target hopen hbounded
      (continuousOn_jointField_slice region field hfield 0) (hfrontier 0) =
    ambientDegree (fun point => field (1, point)) region target hopen hbounded
      (continuousOn_jointField_slice region field hfield 1) (hfrontier 1) := by
  obtain ⟨extension, hEqual⟩ := exists_jointContinuousExtension region field hfield
  obtain ⟨lower, upper, hwidth, hclosure, _⟩ :=
    exists_rectangular_continuousExtension_of_isBounded region hbounded
      (fun point => field (0, point)) (continuousOn_jointField_slice region field hfield 0)
  let cubeRegion := rectangularCubePoint lower upper ⁻¹' region
  have hisolating (parameter : Icc (0 : ℝ) 1) :
      (jointAmbientProblem lower upper hwidth extension target parameter).IsIsolating
        cubeRegion :=
    isIsolating_jointAmbientProblem field region target hopen hfrontier lower upper
      hwidth hclosure extension hEqual parameter
  have hsliceEqual (parameter : Icc (0 : ℝ) 1) :
      EqOn (fun point => extension ((parameter : ℝ), point))
        (fun point => field ((parameter : ℝ), point)) (closure region) :=
    fun _ hpoint => hEqual ⟨parameter.property, hpoint⟩
  calc
    _ = (jointAmbientProblem lower upper hwidth extension target 0).localDegree
        cubeRegion (hisolating 0) :=
      ambientDegree_eq_of_extension (fun point => field (0, point)) region target
        hopen hbounded (continuousOn_jointField_slice region field hfield 0) (hfrontier 0)
        lower upper hwidth hclosure (fun point => extension (0, point))
        (extension.continuous.comp (continuous_const.prodMk continuous_id)).continuousOn
        (hsliceEqual 0)
    _ = (jointAmbientProblem lower upper hwidth extension target 1).localDegree
        cubeRegion (hisolating 1) :=
      Math.IsContinuousBoxComplementarityFamily.localDegree_endpoints_eq
        (isContinuous_jointAmbientProblem lower upper hwidth extension target)
        cubeRegion hisolating
    _ = _ :=
      (ambientDegree_eq_of_extension (fun point => field (1, point)) region target
        hopen hbounded (continuousOn_jointField_slice region field hfield 1) (hfrontier 1)
        lower upper hwidth hclosure (fun point => extension (1, point))
        (extension.continuous.comp (continuous_const.prodMk continuous_id)).continuousOn
        (hsliceEqual 1)).symm

/-- The affine counting region is an actual open source region. -/
theorem isOpen_affineRootRegion {n : ℕ} (root : Fin n → ℝ) (radius : ℝ) :
    IsOpen (Math.affineRootRegion root radius) := by
  have hopen (who : Fin n) : IsOpen {point : Fin n → ℝ |
      root who - radius / 2 < point who ∧ point who < root who + radius / 2} :=
    (isOpen_lt continuous_const (continuous_apply who)).inter
      (isOpen_lt (continuous_apply who) continuous_const)
  simpa only [Math.affineRootRegion, ofPred_forall] using isOpen_iInter_of_finite hopen

/-- The affine source region is bounded, also for empty coordinate types. -/
theorem isBounded_affineRootRegion {n : ℕ} (root : Fin n → ℝ) (radius : ℝ) :
    Bornology.IsBounded (Math.affineRootRegion root radius) := by
  have hbox : Bornology.IsBounded
      (Set.pi Set.univ (fun who => Icc (root who - radius / 2) (root who + radius / 2))) :=
    Bornology.IsBounded.pi (fun _ => Metric.isBounded_Icc _ _)
  apply hbox.subset
  intro point hpoint who _
  exact ⟨(hpoint who).1.le, (hpoint who).2.le⟩

/-- The source closure stays strictly inside the displayed larger affine chart. -/
theorem closure_affineRootRegion_subset {n : ℕ} (root : Fin n → ℝ)
    {radius : ℝ} (hradius : 0 < radius) :
    closure (Math.affineRootRegion root radius) ⊆
      {point | ∀ who, root who - radius < point who ∧ point who < root who + radius} := by
  intro point hpoint who
  have hlow : root who - radius / 2 ≤ point who := by
    have hsubset : closure (Math.affineRootRegion root radius) ⊆
        {point : Fin n → ℝ | root who - radius / 2 ≤ point who} :=
      closure_minimal (fun _ hmem => (hmem who).1.le)
        (isClosed_le continuous_const (continuous_apply who))
    exact hsubset hpoint
  have hhigh : point who ≤ root who + radius / 2 := by
    have hsubset : closure (Math.affineRootRegion root radius) ⊆
        {point : Fin n → ℝ | point who ≤ root who + radius / 2} :=
      closure_minimal (fun _ hmem => (hmem who).2.le)
        (isClosed_le (continuous_apply who) continuous_const)
    exact hsubset hpoint
  constructor <;> linarith

/-- Nonsingularity gives the actual zero-free source frontier, not a supplied
root enumeration or a regularity certificate. -/
theorem affineRootField_ne_zero_on_frontier {n : ℕ}
    (matrix : Matrix (Fin n) (Fin n) ℝ) (hnonsingular : matrix.det ≠ 0)
    (root : Fin n → ℝ) (radius : ℝ) (hradius : 0 < radius) :
    ∀ point ∈ frontier (Math.affineRootRegion root radius),
      Math.affineRootField matrix root point ≠ 0 := by
  intro point hfrontier hzero
  change matrix.mulVec (point - root) = 0 at hzero
  have hsub : point - root = 0 :=
    Matrix.mulVec_injective_of_det_ne_zero hnonsingular
      (by simpa only [Matrix.mulVec_zero] using hzero)
  have hpoint : point = root := sub_eq_zero.mp hsub
  subst point
  have hroot : root ∈ Math.affineRootRegion root radius := by
    intro who
    constructor <;> linarith
  have hinterior : root ∈ interior (Math.affineRootRegion root radius) := by
    rwa [(isOpen_affineRootRegion root radius).interior_eq]
  exact (mem_interior_iff_notMem_frontier hroot).mp hinterior hfrontier

/-- The intrinsic affine degree is exactly the existing integer determinant
sign. The backend's orientation calibration is not applied a second time. -/
theorem ambientDegree_affineRootField_eq_sign_det {n : ℕ}
    (matrix : Matrix (Fin n) (Fin n) ℝ) (hnonsingular : matrix.det ≠ 0)
    (root : Fin n → ℝ) (radius : ℝ) (hradius : 0 < radius) :
    ambientDegree (Math.affineRootField matrix root) (Math.affineRootRegion root radius) 0
      (isOpen_affineRootRegion root radius) (isBounded_affineRootRegion root radius)
      (Math.continuous_affineRootField matrix root).continuousOn
      (affineRootField_ne_zero_on_frontier matrix hnonsingular root radius hradius) =
        (SignType.sign matrix.det : ℤ) := by
  rw [ambientDegree_eq_of_extension (Math.affineRootField matrix root)
    (Math.affineRootRegion root radius) 0 (isOpen_affineRootRegion root radius)
    (isBounded_affineRootRegion root radius)
    (Math.continuous_affineRootField matrix root).continuousOn
    (affineRootField_ne_zero_on_frontier matrix hnonsingular root radius hradius)
    (fun who => root who - radius) (fun who => root who + radius)
    (Math.affineRootBox_width root hradius) (closure_affineRootRegion_subset root hradius)
    (Math.affineRootField matrix root) (Math.continuous_affineRootField matrix root).continuousOn
    (fun _ _ => rfl)]
  simpa only [sub_zero, Math.affineRootProblem] using
    Math.localDegree_affineRootProblem_eq_sign_det matrix hnonsingular root radius hradius

/-- The literal translated identity avoids zero on the source frontier. -/
theorem identityRootField_ne_zero_on_frontier {n : ℕ}
    (root : Fin n → ℝ) (radius : ℝ) (hradius : 0 < radius) :
    ∀ point ∈ frontier (Math.affineRootRegion root radius), point - root ≠ 0 := by
  simpa only [Math.affineRootField, Matrix.one_mulVec] using
    affineRootField_ne_zero_on_frontier (1 : Matrix (Fin n) (Fin n) ℝ)
      (by simp) root radius hradius

/-- The literal translated identity field has degree one, including dimension zero. -/
theorem ambientDegree_identity_eq_one {n : ℕ}
    (root : Fin n → ℝ) (radius : ℝ) (hradius : 0 < radius) :
    ambientDegree (fun point => point - root)
      (Math.affineRootRegion root radius) 0 (isOpen_affineRootRegion root radius)
      (isBounded_affineRootRegion root radius)
      (continuous_id.sub continuous_const).continuousOn
      (identityRootField_ne_zero_on_frontier root radius hradius) = 1 := by
  have hspecial :=
    ambientDegree_affineRootField_eq_sign_det (1 : Matrix (Fin n) (Fin n) ℝ)
      (by simp) root radius hradius
  have hsign : (SignType.sign (1 : Matrix (Fin n) (Fin n) ℝ).det : ℤ) = 1 := by
    simp only [Matrix.det_one, sign_one, SignType.coe_one]
  have hdegree := hspecial.trans hsign
  have hidentity : Math.affineRootField (1 : Matrix (Fin n) (Fin n) ℝ) root =
      (fun point => point - root) := by
    funext point
    exact Matrix.one_mulVec (point - root)
  simpa only [hidentity] using hdegree

end Math.Topology
