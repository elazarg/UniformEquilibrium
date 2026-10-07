module

public import MathUE.Complex.HolomorphicShortArc

/-! # Relative disk neighborhoods cut out by logarithmic rectangles

The elementary rectangle geometry used in Milnor §15.4 is kept separate from
Jordan separation. The bottom open edge belongs to the relative neighborhood
in the closed disk; its relative frontier consists of the other three sides,
including the bottom corners. No target complementary component is identified.
-/

public section

noncomputable section

open Complex Filter Metric Set
open scoped Topology

namespace Math.ComplexAnalysis

@[expose] def closedLogarithmicRectangle (left right height : ℝ) : Set ℂ :=
  {z | z.re ∈ Icc left right ∧ z.im ∈ Icc 0 height}

@[expose] def halfOpenLogarithmicRectangle (left right height : ℝ) : Set ℂ :=
  {z | z.re ∈ Ioo left right ∧ z.im ∈ Ico 0 height}

/-- A relatively open subset of the closed unit disk, including its bottom
circle interval. -/
@[expose] def logarithmicRectangleNeighborhood (angle left right height : ℝ) :
    Set (closedBall (0 : ℂ) 1) :=
  Subtype.val ⁻¹' (logarithmicDiskMap angle ''
    halfOpenLogarithmicRectangle left right height)

theorem norm_logarithmicDiskMap (angle : ℝ) (z : ℂ) :
    ‖logarithmicDiskMap angle z‖ = Real.exp (-z.im) := by
  simp only [logarithmicDiskMap, norm_mul, Complex.norm_exp, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, I_re, I_im, mul_zero, sub_zero,
    zero_sub, Real.exp_zero, one_mul, mul_one]

theorem logarithmicDiskMap_mem_closedBall_iff (angle : ℝ) (z : ℂ) :
    logarithmicDiskMap angle z ∈ closedBall 0 1 ↔ 0 ≤ z.im := by
  rw [mem_closedBall, dist_zero_right, norm_logarithmicDiskMap,
    Real.exp_le_one_iff, neg_nonpos]

theorem isOpenMap_logarithmicDiskMap (angle : ℝ) :
    IsOpenMap (logarithmicDiskMap angle) := by
  exact (Homeomorph.mulLeft₀ (Complex.exp ((angle : ℂ) * I))
    (Complex.exp_ne_zero _)).isOpenMap.comp
      (Complex.isOpenMap_exp.comp (Homeomorph.mulRight₀ I I_ne_zero).isOpenMap)

theorem isOpen_logarithmicRectangleNeighborhood (angle left right height : ℝ) :
    IsOpen (logarithmicRectangleNeighborhood angle left right height) := by
  have heq : logarithmicRectangleNeighborhood angle left right height =
      Subtype.val ⁻¹' (logarithmicDiskMap angle ''
        {z : ℂ | z.re ∈ Ioo left right ∧ z.im < height}) := by
    ext z
    constructor
    · rintro ⟨w, hw, he⟩
      exact ⟨w, ⟨hw.1, hw.2.2⟩, he⟩
    · rintro ⟨w, hw, he⟩
      have hw0 : 0 ≤ w.im := (logarithmicDiskMap_mem_closedBall_iff angle w).mp
        (he.symm ▸ z.property)
      exact ⟨w, ⟨hw.1, hw0, hw.2⟩, he⟩
  rw [heq]
  apply IsOpen.preimage continuous_subtype_val
  apply isOpenMap_logarithmicDiskMap
  exact (isOpen_Ioo.preimage Complex.continuous_re).inter
    (isOpen_lt Complex.continuous_im continuous_const)

theorem isCompact_closedLogarithmicRectangle (left right height : ℝ) :
    IsCompact (closedLogarithmicRectangle left right height) :=
  isCompact_Icc.reProdIm isCompact_Icc

theorem closure_halfOpenLogarithmicRectangle
    {left right height : ℝ} (hlr : left < right) (hh : 0 < height) :
    closure (halfOpenLogarithmicRectangle left right height) =
      closedLogarithmicRectangle left right height := by
  change closure (Ioo left right ×ℂ Ico 0 height) = Icc left right ×ℂ Icc 0 height
  rw [Complex.closure_reProdIm, closure_Ioo hlr.ne, closure_Ico hh.ne]

private theorem image_neighborhood (angle left right height : ℝ) :
    Subtype.val '' logarithmicRectangleNeighborhood angle left right height =
      logarithmicDiskMap angle '' halfOpenLogarithmicRectangle left right height := by
  apply image_preimage_eq_of_subset
  rintro _ ⟨z, hz, rfl⟩
  exact ⟨⟨_, (logarithmicDiskMap_mem_closedBall_iff angle z).mpr hz.2.1⟩, rfl⟩

/-- Literal ambient image of the relative closure; compactness is derived from
the closed rectangle, not assumed for a target image. -/
theorem closure_logarithmicRectangleNeighborhood
    (angle : ℝ) {left right height : ℝ} (hlr : left < right) (hh : 0 < height) :
    Subtype.val '' closure (logarithmicRectangleNeighborhood angle left right height) =
      logarithmicDiskMap angle '' closedLogarithmicRectangle left right height := by
  rw [← isClosed_closedBall.isClosedEmbedding_subtypeVal.closure_image_eq,
    image_neighborhood]
  have hc := (differentiable_logarithmicDiskMap angle).continuous
  apply Subset.antisymm
  · apply closure_minimal
    · exact image_mono (fun _ hz => ⟨⟨hz.1.1.le, hz.1.2.le⟩, hz.2.1, hz.2.2.le⟩)
    · exact ((isCompact_closedLogarithmicRectangle left right height).image hc).isClosed
  · rw [← closure_halfOpenLogarithmicRectangle hlr hh]
    exact image_closure_subset_closure_image hc

theorem boundaryPoint_mem_logarithmicRectangleNeighborhood
    (angle : ℝ) {left right height center : ℝ}
    (hc : center ∈ Ioo left right) (hh : 0 < height) :
    (⟨Complex.exp (((angle + center : ℝ) : ℂ) * I), by
      simp [mem_closedBall, Complex.norm_exp]⟩ : closedBall (0 : ℂ) 1) ∈
      logarithmicRectangleNeighborhood angle left right height := by
  refine ⟨(center : ℂ), ?_, ?_⟩
  · change center ∈ Ioo left right ∧ (0 : ℝ) ∈ Ico 0 height
    exact ⟨hc, le_rfl, hh⟩
  · simp [logarithmicDiskMap, Complex.ofReal_add, add_mul, Complex.exp_add]

/-- The scalar path traverses exactly the two vertical closed edges and the top.
In particular the bottom open edge is absent. -/
theorem rectangleArc_image_Icc {left right height : ℝ}
    (hlr : left < right) (hh : 0 < height) :
    rectangleArc left right height '' Icc (0 : ℝ) 3 =
      closedLogarithmicRectangle left right height \
        halfOpenLogarithmicRectangle left right height := by
  apply Subset.antisymm
  · rintro _ ⟨t, ht, rfl⟩
    refine ⟨rectangleArc_coordinates hlr hh ht, ?_⟩
    unfold rectangleArc halfOpenLogarithmicRectangle
    split_ifs <;> simp only [mem_ofPred_eq, Complex.add_re, Complex.add_im,
      Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      I_re, I_im, mul_one, mul_zero, sub_zero, add_zero, zero_add, mem_Ioo, mem_Ico]
    · exact fun h => (lt_irrefl left) h.1.1
    · exact fun h => (lt_irrefl height) h.2.2
    · exact fun h => (lt_irrefl right) h.1.2
  · intro z hz
    have hc := hz.1
    have hside : z.re = left ∨ z.re = right ∨ z.im = height := by
      by_contra h
      push Not at h
      exact hz.2 ⟨⟨lt_of_le_of_ne hc.1.1 h.1.symm,
        lt_of_le_of_ne hc.1.2 h.2.1⟩, hc.2.1, lt_of_le_of_ne hc.2.2 h.2.2⟩
    rcases hside with hl | hr | ht
    · refine ⟨z.im / height, ⟨div_nonneg hc.2.1 hh.le,
        (div_le_one hh).mpr hc.2.2 |>.trans (by norm_num)⟩, ?_⟩
      rw [rectangleArc, ite_eq_left ((div_le_one hh).mpr hc.2.2)]
      apply Complex.ext <;> simp [hl, mul_div_cancel₀ _ hh.ne']
    · by_cases htop : z.im = height
      · refine ⟨2, by norm_num, ?_⟩
        apply Complex.ext
        · simp only [rectangleArc, ite_eq_right (show ¬(2 : ℝ) ≤ 1 by norm_num),
            ite_eq_left le_rfl, Complex.add_re, Complex.mul_re, Complex.ofReal_re,
            Complex.ofReal_im, I_re, I_im, mul_zero, zero_mul, sub_zero, add_zero, hr]
          ring
        · simp [rectangleArc, htop]
      · have hlt : z.im / height < 1 := (div_lt_one hh).mpr
          (lt_of_le_of_ne hc.2.2 htop)
        refine ⟨3 - z.im / height, ⟨by linarith,
          by linarith [div_nonneg hc.2.1 hh.le]⟩, ?_⟩
        rw [rectangleArc, ite_eq_right (by linarith), ite_eq_right (by linarith)]
        apply Complex.ext <;> simp [hr, mul_div_cancel₀ _ hh.ne']
    · by_cases hleft : z.re = left
      · refine ⟨1, by norm_num, ?_⟩
        apply Complex.ext <;> simp [rectangleArc, hleft, ht]
      · have hpos : 0 < (z.re - left) / (right - left) :=
          div_pos (sub_pos.mpr (lt_of_le_of_ne hc.1.1 (Ne.symm hleft))) (sub_pos.mpr hlr)
        have hle : (z.re - left) / (right - left) ≤ 1 :=
          (div_le_one (sub_pos.mpr hlr)).mpr (by linarith [hc.1.2])
        refine ⟨1 + (z.re - left) / (right - left), ⟨by linarith, by linarith⟩, ?_⟩
        rw [rectangleArc, ite_eq_right (by linarith), ite_eq_left (by linarith)]
        apply Complex.ext <;> simp [ht, mul_div_cancel₀ _ (sub_ne_zero.mpr hlr.ne')]

theorem range_rectangleArc_unitInterval {left right height : ℝ}
    (hlr : left < right) (hh : 0 < height) :
    range (fun t : unitInterval => rectangleArc left right height (3 * (t : ℝ))) =
      closedLogarithmicRectangle left right height \
        halfOpenLogarithmicRectangle left right height := by
  rw [← rectangleArc_image_Icc hlr hh]
  ext z
  constructor
  · rintro ⟨t, rfl⟩
    exact ⟨3 * (t : ℝ), ⟨by linarith [t.property.1], by linarith [t.property.2]⟩, rfl⟩
  · rintro ⟨t, ht, rfl⟩
    refine ⟨⟨t / 3, by constructor <;> linarith [ht.1, ht.2]⟩, ?_⟩
    change rectangleArc left right height (3 * (t / 3)) = rectangleArc left right height t
    rw [show 3 * (t / 3) = t by ring]

/-- Exact relative frontier, mapped into the plane. No Jordan theorem is used. -/
theorem frontier_logarithmicRectangleNeighborhood
    {left right height width : ℝ} (hleft : 0 < left) (hlr : left < right)
    (hright : right < width) (hh : 0 < height) (hwidth : width < 2 * Real.pi)
    (angle : ℝ) :
    Subtype.val '' frontier (logarithmicRectangleNeighborhood angle left right height) =
      range (fun t : unitInterval => logarithmicDiskMap angle
        (rectangleArc left right height (3 * (t : ℝ)))) := by
  have hsubset : closedLogarithmicRectangle left right height ⊆
      {z : ℂ | 0 < z.re ∧ z.re < width ∧ 0 ≤ z.im} := by
    intro z hz
    exact ⟨hleft.trans_le hz.1.1, hz.1.2.trans_lt hright, hz.2.1⟩
  have hinj : InjOn (logarithmicDiskMap angle)
      (closedLogarithmicRectangle left right height) :=
    (logarithmicDiskMap_injOn_closed_upper_strip hwidth angle).mono hsubset
  rw [(isOpen_logarithmicRectangleNeighborhood angle left right height).frontier_eq,
    Set.image_sdiff Subtype.val_injective,
    closure_logarithmicRectangleNeighborhood angle hlr hh,
    image_neighborhood]
  rw [← hinj.image_sdiff_subset
    (show halfOpenLogarithmicRectangle left right height ⊆
      closedLogarithmicRectangle left right height from
      fun _ hz => ⟨⟨hz.1.1.le, hz.1.2.le⟩, hz.2.1, hz.2.2.le⟩)]
  rw [← range_rectangleArc_unitInterval hlr hh, ← range_comp]
  rfl

end Math.ComplexAnalysis
