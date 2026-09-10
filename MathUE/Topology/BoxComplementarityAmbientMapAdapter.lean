import MathUE.Topology.RectangularPoincareMiranda
import MathUE.Topology.BoxComplementarityProblem

/-!
# Ambient maps in a positive rectangular chart

The gain field is literally the negative of the ambient field pulled back
through the coordinate rectangle. Continuity is needed only on that closed
rectangle. Interior complementarity solutions are exactly ambient zeros.
Isolation follows from source-owned frontier conditions; no solution-set
identity is assumed. This does not identify any degree with Brouwer degree
or prove chart independence, dilation invariance, or an affine index formula.
-/

noncomputable section

namespace Math

open Set

variable {ι : Type*} [Fintype ι]

namespace Topology

/-- The existing rectangular coordinate map restricted to the literal unit cube. -/
def rectangularCubePoint (lower upper : ι → ℝ) (point : UnitCube ι) : ι → ℝ :=
  rectangularPoint lower upper (fun who => (point who : ℝ))

theorem continuous_rectangularCubePoint (lower upper : ι → ℝ) :
    Continuous (rectangularCubePoint lower upper) :=
  (continuous_rectangularPoint lower upper).comp
    (continuous_pi fun who => continuous_subtype_val.comp (continuous_apply who))

theorem rectangularCubePoint_mem_Icc {lower upper : ι → ℝ}
    (hwidth : ∀ who, lower who < upper who) (point : UnitCube ι) :
    rectangularCubePoint lower upper point ∈ Icc lower upper :=
  rectangularPoint_mem_Icc hwidth
    ⟨fun who => (point who).property.1, fun who => (point who).property.2⟩

/-- Positive coordinate widths identify the two literal coordinate interiors. -/
theorem rectangularCubePoint_coordinateInterior_iff {lower upper : ι → ℝ}
    (hwidth : ∀ who, lower who < upper who) (point : UnitCube ι) :
    (∀ who, lower who < rectangularCubePoint lower upper point who ∧
      rectangularCubePoint lower upper point who < upper who) ↔
        ∀ who, 0 < (point who : ℝ) ∧ (point who : ℝ) < 1 := by
  constructor <;> intro hpoint who
  · have h := hpoint who
    have hw := hwidth who
    dsimp [rectangularCubePoint, rectangularPoint] at h
    constructor <;> nlinarith
  · have h := hpoint who
    have hw := hwidth who
    dsimp [rectangularCubePoint, rectangularPoint]
    constructor <;> nlinarith

end Topology

namespace BoxComplementarityProblem

open Topology

variable (lower upper : ι → ℝ) (hwidth : ∀ who, lower who < upper who)
  (field : (ι → ℝ) → ι → ℝ) (hfield : ContinuousOn field (Icc lower upper))

/-- Pull an ambient field back through a positive rectangle and negate it.
Only continuity on the closed rectangle is required. -/
def ofAmbientMap : BoxComplementarityProblem ι where
  gain point who := -field (rectangularCubePoint lower upper point) who
  continuous_gain who :=
    ((continuous_apply who).comp
      (hfield.comp_continuous (continuous_rectangularCubePoint lower upper)
        (rectangularCubePoint_mem_Icc hwidth))).neg

/-- Interior solutions of the pulled-back problem are literal ambient zeros. -/
theorem isSolution_ofAmbientMap_iff_of_coordinateInterior (point : UnitCube ι)
    (hpoint : ∀ who, 0 < (point who : ℝ) ∧ (point who : ℝ) < 1) :
    (ofAmbientMap lower upper hwidth field hfield).IsSolution point ↔
      field (rectangularCubePoint lower upper point) = 0 := by
  rw [isSolution_iff_gain_eq_zero_of_coordinateInterior _ point hpoint]
  change -field (rectangularCubePoint lower upper point) = 0 ↔ _
  exact neg_eq_zero

/-- The same correspondence stated using the source rectangle's interior. -/
theorem isSolution_ofAmbientMap_iff_of_imageInterior (point : UnitCube ι)
    (hpoint : ∀ who, lower who < rectangularCubePoint lower upper point who ∧
      rectangularCubePoint lower upper point who < upper who) :
    (ofAmbientMap lower upper hwidth field hfield).IsSolution point ↔
      field (rectangularCubePoint lower upper point) = 0 :=
  isSolution_ofAmbientMap_iff_of_coordinateInterior lower upper hwidth field hfield point
    ((rectangularCubePoint_coordinateInterior_iff hwidth point).mp hpoint)

/-- A zero-free source frontier inside the chart interior pulls back to an
isolating region. Only frontier points in the closed rectangle are relevant. -/
theorem isIsolating_ofAmbientMap_preimage (region : Set (ι → ℝ))
    (hopen : IsOpen region)
    (hinterior : ∀ point ∈ frontier region ∩ Icc lower upper,
      ∀ who, lower who < point who ∧ point who < upper who)
    (hzeroFree : ∀ point ∈ frontier region ∩ Icc lower upper, field point ≠ 0) :
    (ofAmbientMap lower upper hwidth field hfield).IsIsolating
      (rectangularCubePoint lower upper ⁻¹' region) := by
  refine ⟨hopen.preimage (continuous_rectangularCubePoint lower upper),
    Set.eq_empty_iff_forall_notMem.mpr ?_⟩
  rintro point ⟨hsolution, hfrontier⟩
  have hsource : rectangularCubePoint lower upper point ∈
      frontier region ∩ Icc lower upper :=
    ⟨(continuous_rectangularCubePoint lower upper).frontier_preimage_subset region hfrontier,
      rectangularCubePoint_mem_Icc hwidth point⟩
  exact hzeroFree _ hsource
    ((isSolution_ofAmbientMap_iff_of_imageInterior lower upper hwidth field hfield
      point (hinterior _ hsource)).mp hsolution)

/-- The usual closure-containment condition supplies the source frontier interior. -/
theorem isIsolating_ofAmbientMap_preimage_of_closure_subset (region : Set (ι → ℝ))
    (hopen : IsOpen region)
    (hclosure : closure region ⊆
      {point | ∀ who, lower who < point who ∧ point who < upper who})
    (hzeroFree : ∀ point ∈ frontier region, field point ≠ 0) :
    (ofAmbientMap lower upper hwidth field hfield).IsIsolating
      (rectangularCubePoint lower upper ⁻¹' region) :=
  isIsolating_ofAmbientMap_preimage lower upper hwidth field hfield region hopen
    (fun _ hpoint => hclosure (frontier_subset_closure hpoint.1))
    (fun point hpoint => hzeroFree point hpoint.1)

/-- Inside the chart interior, the actual selected complementarity solution
set is exactly the pulled-back ambient zero set in the source region. -/
theorem solutionsIn_ofAmbientMap_preimage_eq (region : Set (ι → ℝ))
    (hinterior : ∀ point ∈ region ∩ Icc lower upper,
      ∀ who, lower who < point who ∧ point who < upper who) :
    (ofAmbientMap lower upper hwidth field hfield).solutionsIn
        (rectangularCubePoint lower upper ⁻¹' region) =
      rectangularCubePoint lower upper ⁻¹' ({point | field point = 0} ∩ region) := by
  ext point
  change ((ofAmbientMap lower upper hwidth field hfield).IsSolution point ∧
      rectangularCubePoint lower upper point ∈ region) ↔
    field (rectangularCubePoint lower upper point) = 0 ∧
      rectangularCubePoint lower upper point ∈ region
  by_cases hregion : rectangularCubePoint lower upper point ∈ region
  · rw [isSolution_ofAmbientMap_iff_of_imageInterior lower upper hwidth field hfield point
      (hinterior _ ⟨hregion, rectangularCubePoint_mem_Icc hwidth point⟩)]
  · simp [hregion]

end BoxComplementarityProblem

end Math

