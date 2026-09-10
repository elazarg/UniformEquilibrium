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

namespace Math.Topology

open Set

variable {ι : Type*} [Fintype ι]

/-- A translated scalar dilation on the ambient coordinate space. -/
def positiveDilation (shift : ι → ℝ) (scalar : ℝ) (point : ι → ℝ) : ι → ℝ :=
  fun who => shift who + scalar * point who

omit [Fintype ι] in
theorem continuous_positiveDilation (shift : ι → ℝ) (scalar : ℝ) :
    Continuous (positiveDilation shift scalar) :=
  continuous_pi fun who => continuous_const.add
    (continuous_const.mul (continuous_apply who))

omit [Fintype ι] in
/-- Positive dilation preserves strict coordinate widths. -/
theorem positiveDilation_width (shift : ι → ℝ) {scalar : ℝ} (hscalar : 0 < scalar)
    {lower upper : ι → ℝ} (hwidth : ∀ who, lower who < upper who) :
    ∀ who, positiveDilation shift scalar lower who < positiveDilation shift scalar upper who := by
  intro who
  simpa only [positiveDilation, add_comm] using
    add_lt_add_left (mul_lt_mul_of_pos_left (hwidth who) hscalar) (shift who)

omit [Fintype ι] in
/-- The source closed box is mapped into its dilated closed box. -/
theorem positiveDilation_mem_Icc (shift : ι → ℝ) {scalar : ℝ} (hscalar : 0 < scalar)
    {lower upper point : ι → ℝ} (hpoint : point ∈ Icc lower upper) :
    positiveDilation shift scalar point ∈
      Icc (positiveDilation shift scalar lower) (positiveDilation shift scalar upper) := by
  constructor <;> intro who
  · simpa only [positiveDilation, add_comm] using
      add_le_add_left (mul_le_mul_of_nonneg_left (hpoint.1 who) hscalar.le) (shift who)
  · simpa only [positiveDilation, add_comm] using
      add_le_add_left (mul_le_mul_of_nonneg_left (hpoint.2 who) hscalar.le) (shift who)

/-- Rectangular coordinates commute exactly with simultaneous ambient dilation. -/
theorem rectangularCubePoint_positiveDilation (shift : ι → ℝ) (scalar : ℝ)
    (lower upper : ι → ℝ) (point : Math.UnitCube ι) :
    rectangularCubePoint (positiveDilation shift scalar lower)
        (positiveDilation shift scalar upper) point =
      positiveDilation shift scalar (rectangularCubePoint lower upper point) := by
  funext who
  dsimp [rectangularCubePoint, rectangularPoint, positiveDilation]
  ring

/-- The reference-cube region is unchanged when both chart and ambient region
are transported by the displayed dilation. -/
theorem rectangularCubePoint_preimage_positiveDilation (shift : ι → ℝ) (scalar : ℝ)
    (lower upper : ι → ℝ) (region : Set (ι → ℝ)) :
    rectangularCubePoint (positiveDilation shift scalar lower)
        (positiveDilation shift scalar upper) ⁻¹' region =
      rectangularCubePoint lower upper ⁻¹' (positiveDilation shift scalar ⁻¹' region) := by
  ext point
  simp only [mem_preimage, rectangularCubePoint_positiveDilation]

/-- The literal source field after coordinate dilation and inverse output scaling. -/
def dilatedAmbientField (shift : ι → ℝ) (scalar : ℝ)
    (field : (ι → ℝ) → ι → ℝ) (point : ι → ℝ) : ι → ℝ :=
  fun who => scalar⁻¹ * field (positiveDilation shift scalar point) who

omit [Fintype ι] in
theorem continuousOn_dilatedAmbientField (shift : ι → ℝ) {scalar : ℝ}
    (hscalar : 0 < scalar) (lower upper : ι → ℝ) (field : (ι → ℝ) → ι → ℝ)
    (hfield : ContinuousOn field
      (Icc (positiveDilation shift scalar lower) (positiveDilation shift scalar upper))) :
    ContinuousOn (dilatedAmbientField shift scalar field) (Icc lower upper) := by
  change ContinuousOn (fun point => scalar⁻¹ • field (positiveDilation shift scalar point))
    (Icc lower upper)
  have hconstant : ContinuousOn (fun _ : ι → ℝ => (scalar⁻¹ : ℝ)) (Icc lower upper) :=
    continuousOn_const
  exact (hconstant.smul
    (hfield.comp (continuous_positiveDilation shift scalar).continuousOn
      (fun _ hpoint => positiveDilation_mem_Icc shift hscalar hpoint)))

end Math.Topology

namespace Math.BoxComplementarityProblem

open Set Math.Topology

variable {ι : Type*} [Fintype ι]

/-- The two actual pulled-back problems differ only by positive output scaling. -/
theorem ofAmbientMap_dilatedAmbientField (shift : ι → ℝ) {scalar : ℝ}
    (hscalar : 0 < scalar) (lower upper : ι → ℝ)
    (hwidth : ∀ who, lower who < upper who) (field : (ι → ℝ) → ι → ℝ)
    (hfield : ContinuousOn field
      (Icc (positiveDilation shift scalar lower) (positiveDilation shift scalar upper))) :
    ofAmbientMap lower upper hwidth (dilatedAmbientField shift scalar field)
        (continuousOn_dilatedAmbientField shift hscalar lower upper field hfield) =
      (ofAmbientMap (positiveDilation shift scalar lower) (positiveDilation shift scalar upper)
        (positiveDilation_width shift hscalar hwidth) field hfield).scaleGain scalar⁻¹ := by
  have hgain :
      (ofAmbientMap lower upper hwidth (dilatedAmbientField shift scalar field)
        (continuousOn_dilatedAmbientField shift hscalar lower upper field hfield)).gain =
      ((ofAmbientMap (positiveDilation shift scalar lower) (positiveDilation shift scalar upper)
        (positiveDilation_width shift hscalar hwidth) field hfield).scaleGain scalar⁻¹).gain := by
    funext point who
    simp only [ofAmbientMap, dilatedAmbientField, scaleGain,
      rectangularCubePoint_positiveDilation, mul_neg]
  exact Math.BoxComplementarityProblem.ext hgain

/-- Isolation is unchanged under the simultaneous literal chart/field/region dilation. -/
theorem isIsolating_ofAmbientMap_dilation_iff (shift : ι → ℝ) {scalar : ℝ}
    (hscalar : 0 < scalar) (lower upper : ι → ℝ)
    (hwidth : ∀ who, lower who < upper who) (field : (ι → ℝ) → ι → ℝ)
    (hfield : ContinuousOn field
      (Icc (positiveDilation shift scalar lower) (positiveDilation shift scalar upper)))
    (region : Set (ι → ℝ)) :
    (ofAmbientMap lower upper hwidth (dilatedAmbientField shift scalar field)
        (continuousOn_dilatedAmbientField shift hscalar lower upper field hfield)).IsIsolating
        (rectangularCubePoint lower upper ⁻¹' (positiveDilation shift scalar ⁻¹' region)) ↔
      (ofAmbientMap (positiveDilation shift scalar lower) (positiveDilation shift scalar upper)
        (positiveDilation_width shift hscalar hwidth) field hfield).IsIsolating
        (rectangularCubePoint (positiveDilation shift scalar lower)
          (positiveDilation shift scalar upper) ⁻¹' region) := by
  rw [ofAmbientMap_dilatedAmbientField shift hscalar lower upper hwidth field hfield,
    ← rectangularCubePoint_preimage_positiveDilation]
  exact isIsolating_scaleGain_iff _ (inv_pos.mpr hscalar) _

end Math.BoxComplementarityProblem
