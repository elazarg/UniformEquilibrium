module

public import MathUE.Complex.LogarithmicRectangleNeighborhood
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Analysis.SpecificLimits.Basic

/-! # Disjoint shrinking spherical image arcs

The finite-avoidance recursion in Milnor §15.4 is applied to actual source
arcs. Compact source ranges avoid the prescribed boundary point. Their images
are disjoint using injectivity in the disk, frontier separation at endpoints,
and finite endpoint exclusions. No global boundary injectivity is used.

Source: Milnor, *Dynamics in One Complex Variable*, §15.4,
https://legacy-www.math.harvard.edu/archive/118r_spring_05/docs/milnor.pdf

The results supply disjoint shrinking closed arcs and nested relatively open
source neighborhoods with their exact frontiers. They do not identify target
complementary components, rectifiable-length bounds, Jordan separation, or a
continuous extension on the whole circle.
-/

public section

noncomputable section

open Complex Filter MeasureTheory Metric Set
open scoped ENNReal Topology

namespace Math.ComplexAnalysis

/-- An actual embedded source arc straddling a disk boundary direction, with
its embedded spherical image and literal interior agreement. -/
structure EmbeddedSphericalImageArc (g : ℂ → ℂ) (angle : ℝ) where
  width : ℝ
  width_mem : width ∈ Ioo (0 : ℝ) 1
  left : ℝ
  left_mem : left ∈ Ioo (angle - width / 2) angle
  right : ℝ
  right_mem : right ∈ Ioo angle (angle + width / 2)
  first : ComplexSphere.Sphere
  last : ComplexSphere.Sphere
  source : Path (Complex.exp ((left : ℂ) * I)) (Complex.exp ((right : ℂ) * I))
  image : Path first last
  source_embedding : Topology.IsClosedEmbedding source
  image_embedding : Topology.IsClosedEmbedding image
  first_frontier : first ∈ frontier (ComplexSphere.chart '' (g '' ball 0 1))
  last_frontier : last ∈ frontier (ComplexSphere.chart '' (g '' ball 0 1))
  endpoints_ne : first ≠ last
  interior_agreement : ∀ t : unitInterval, (t : ℝ) ∈ Ioo 0 1 →
    source t ∈ ball 0 1 ∧ image t = ComplexSphere.chart (g (source t))

private theorem exp_angle_ne_of_small_difference {x y : ℝ}
    (hne : x ≠ y) (hsmall : |x - y| < 1) :
    Complex.exp ((x : ℂ) * I) ≠ Complex.exp ((y : ℂ) * I) := by
  intro heq
  have hshift : Complex.exp (((x - y : ℝ) : ℂ) * I) = Complex.exp 0 := by
    rw [Complex.ofReal_sub, sub_mul, Complex.exp_sub, heq, div_self (Complex.exp_ne_zero _)]
    simp
  have hr := abs_lt.mp hsmall
  have he := Complex.exp_inj_of_neg_pi_lt_of_le_pi
    (show -Real.pi < (((x - y : ℝ) : ℂ) * I).im by
      simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
        I_im, I_re, mul_one, mul_zero, add_zero]
      linarith [Real.pi_gt_three])
    (show (((x - y : ℝ) : ℂ) * I).im ≤ Real.pi by
      simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
        I_im, I_re, mul_one, mul_zero, add_zero]
      linarith [Real.pi_gt_three])
    (by simpa using neg_neg_of_pos Real.pi_pos)
    (by simpa using Real.pi_pos.le) hshift
  have him := congrArg Complex.im he
  simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    I_im, I_re, mul_one, mul_zero, add_zero, Complex.zero_im] at him
  exact hne (sub_eq_zero.mp him)

namespace EmbeddedSphericalImageArc

variable {g : ℂ → ℂ} {angle : ℝ}

/-- The requested boundary point is excluded from the entire closed source arc,
including both endpoints. -/
theorem boundaryPoint_not_mem_source (arc : EmbeddedSphericalImageArc g angle) :
    Complex.exp ((angle : ℂ) * I) ∉ range arc.source := by
  rintro ⟨t, ht⟩
  rcases eq_endpoints_or_mem_Ioo_of_mem_Icc t.property with h | h | h
  · have ht0 : t = 0 := Subtype.ext h
    subst t
    have hsmall : |arc.left - angle| < 1 := abs_lt.mpr ⟨by
      linarith [arc.left_mem.1, arc.width_mem.2], by linarith [arc.left_mem.2]⟩
    exact exp_angle_ne_of_small_difference arc.left_mem.2.ne hsmall
      (by simpa only [Path.source] using ht)
  · have ht1 : t = 1 := Subtype.ext h
    subst t
    have hsmall : |arc.right - angle| < 1 := abs_lt.mpr ⟨by
      linarith [arc.right_mem.1], by linarith [arc.right_mem.2, arc.width_mem.2]⟩
    exact exp_angle_ne_of_small_difference arc.right_mem.1.ne' hsmall
      (by simpa only [Path.target] using ht)
  · have hinside := (arc.interior_agreement t h).1
    have hn : ‖Complex.exp ((angle : ℂ) * I)‖ = 1 := by simp [Complex.norm_exp]
    rw [ht] at hinside
    simp only [mem_ball, dist_zero_right, hn, lt_self_iff_false] at hinside

private theorem image_mem_cases (arc : EmbeddedSphericalImageArc g angle)
    (t : unitInterval) :
    arc.image t ∈ ({arc.first, arc.last} : Set ComplexSphere.Sphere) ∨
      ∃ z ∈ ball (0 : ℂ) 1, z ∈ range arc.source ∧
        arc.image t = ComplexSphere.chart (g z) := by
  rcases eq_endpoints_or_mem_Ioo_of_mem_Icc t.property with h | h | h
  · have ht : t = 0 := Subtype.ext h
    subst t
    exact Or.inl (by simp)
  · have ht : t = 1 := Subtype.ext h
    subst t
    exact Or.inl (by simp)
  · exact Or.inr ⟨arc.source t, (arc.interior_agreement t h).1,
      mem_range_self t, (arc.interior_agreement t h).2⟩

/-- Full image ranges are disjoint, not just their open interiors. -/
theorem disjoint_image_of_disjoint_source
    (hg : DifferentiableOn ℂ g (ball 0 1)) (hinj : InjOn g (ball 0 1))
    (a b : EmbeddedSphericalImageArc g angle)
    (hs : Disjoint (range a.source) (range b.source))
    (he : Disjoint ({a.first, a.last} : Set ComplexSphere.Sphere) {b.first, b.last}) :
    Disjoint (range a.image) (range b.image) := by
  have hopenComplex : IsOpen (g '' ball 0 1) := by
    simpa only [range_domRestrict] using
      (isOpenMap_domRestrict_of_holomorphic_injOn isOpen_ball hg hinj).isOpen_range
  have hopenChart : IsOpen (range ComplexSphere.chart) := by
    rw [ComplexSphere.range_chart]
    exact isClosed_singleton.isOpen_compl
  have hopen : IsOpen (ComplexSphere.chart '' (g '' ball 0 1)) :=
    ComplexSphere.isEmbedding_chart.isInducing.isOpenMap hopenChart _ hopenComplex
  have hnot (arc : EmbeddedSphericalImageArc g angle) {p : ComplexSphere.Sphere}
      (hp : p ∈ ({arc.first, arc.last} : Set ComplexSphere.Sphere)) :
      p ∉ ComplexSphere.chart '' (g '' ball 0 1) := by
    have hfront : p ∈ frontier (ComplexSphere.chart '' (g '' ball 0 1)) := by
      rcases hp with rfl | hp
      · exact arc.first_frontier
      · rw [mem_singleton_iff] at hp
        rw [hp]
        exact arc.last_frontier
    simpa only [hopen.interior_eq] using hfront.2
  apply Set.disjoint_left.mpr
  rintro p ⟨s, rfl⟩ ⟨t, ht⟩
  rcases a.image_mem_cases s with ha | ⟨z, hz, hza, heqa⟩
  · rcases b.image_mem_cases t with hb | ⟨w, hw, hwb, heqb⟩
    · exact Set.disjoint_left.mp he ha (ht ▸ hb)
    · exact hnot a ha (ht ▸ heqb.symm ▸ ⟨_, ⟨w, hw, rfl⟩, rfl⟩)
  · rcases b.image_mem_cases t with hb | ⟨w, hw, hwb, heqb⟩
    · exact hnot b hb (ht.symm ▸ heqa.symm ▸ ⟨_, ⟨z, hz, rfl⟩, rfl⟩)
    · have hequal : z = w := hinj hz hw
        (ComplexSphere.isEmbedding_chart.injective (heqa.symm.trans (ht.symm.trans heqb)))
      exact Set.disjoint_left.mp hs hza (hequal.symm ▸ hwb)

end EmbeddedSphericalImageArc

/-- The actual rectangle retained by the local analytic construction. -/
structure RectangleSphericalImageArc (g : ℂ → ℂ) (angle : ℝ)
    extends EmbeddedSphericalImageArc g angle where
  height : ℝ
  height_mem : height ∈ Ioo (0 : ℝ) width
  source_formula : ∀ t : unitInterval, source t =
    logarithmicDiskMap (angle - width / 2)
      (rectangleArc (left - (angle - width / 2))
        (right - (angle - width / 2)) height (3 * (t : ℝ)))

namespace RectangleSphericalImageArc

variable {g : ℂ → ℂ} {angle : ℝ}

@[expose] def neighborhood (arc : RectangleSphericalImageArc g angle) :
    Set (closedBall (0 : ℂ) 1) :=
  logarithmicRectangleNeighborhood (angle - arc.width / 2)
    (arc.left - (angle - arc.width / 2))
    (arc.right - (angle - arc.width / 2)) arc.height

theorem isOpen_neighborhood (arc : RectangleSphericalImageArc g angle) :
    IsOpen arc.neighborhood := isOpen_logarithmicRectangleNeighborhood _ _ _ _

theorem closure_neighborhood (arc : RectangleSphericalImageArc g angle) :
    Subtype.val '' closure arc.neighborhood =
      logarithmicDiskMap (angle - arc.width / 2) ''
        closedLogarithmicRectangle (arc.left - (angle - arc.width / 2))
          (arc.right - (angle - arc.width / 2)) arc.height := by
  apply closure_logarithmicRectangleNeighborhood
  · linarith [arc.left_mem.2, arc.right_mem.1]
  · exact arc.height_mem.1

theorem frontier_neighborhood (arc : RectangleSphericalImageArc g angle) :
    Subtype.val '' frontier arc.neighborhood = range arc.source := by
  have h := frontier_logarithmicRectangleNeighborhood
    (show 0 < arc.left - (angle - arc.width / 2) by linarith [arc.left_mem.1])
    (show arc.left - (angle - arc.width / 2) <
      arc.right - (angle - arc.width / 2) by linarith [arc.left_mem.2, arc.right_mem.1])
    (show arc.right - (angle - arc.width / 2) < arc.width by
      linarith [arc.right_mem.2]) arc.height_mem.1
    (show arc.width < 2 * Real.pi by linarith [arc.width_mem.2, Real.pi_gt_three])
    (angle - arc.width / 2)
  rw [show (fun t : unitInterval => logarithmicDiskMap (angle - arc.width / 2)
    (rectangleArc (arc.left - (angle - arc.width / 2))
      (arc.right - (angle - arc.width / 2)) arc.height (3 * (t : ℝ)))) =
      arc.source from funext fun t => (arc.source_formula t).symm] at h
  exact h

theorem boundaryPoint_mem_neighborhood (arc : RectangleSphericalImageArc g angle) :
    (⟨Complex.exp ((angle : ℂ) * I), by
      simp [mem_closedBall, Complex.norm_exp]⟩ : closedBall (0 : ℂ) 1) ∈
      arc.neighborhood := by
  have h := boundaryPoint_mem_logarithmicRectangleNeighborhood (angle - arc.width / 2)
    (show arc.width / 2 ∈ Ioo (arc.left - (angle - arc.width / 2))
      (arc.right - (angle - arc.width / 2)) by
        constructor <;> linarith [arc.left_mem.2, arc.right_mem.1]) arc.height_mem.1
  have hangle : angle - arc.width / 2 + arc.width / 2 = angle := by ring
  have hpoint :
      (⟨Complex.exp (((angle - arc.width / 2 + arc.width / 2 : ℝ) : ℂ) * I), by
        simp [mem_closedBall, Complex.norm_exp]⟩ : closedBall (0 : ℂ) 1) =
      ⟨Complex.exp ((angle : ℂ) * I), by
        simp [mem_closedBall, Complex.norm_exp]⟩ := by
    apply Subtype.ext
    change Complex.exp (((angle - arc.width / 2 + arc.width / 2 : ℝ) : ℂ) * I) = _
    rw [hangle]
  exact hpoint ▸ h

end RectangleSphericalImageArc

private theorem exists_rectangle_arc_inside_finite_neighborhoods
    {g : ℂ → ℂ} (hg : DifferentiableOn ℂ g (ball 0 1))
    (hinj : InjOn g (ball 0 1)) (angle : ℝ)
    (forbidden : Finset ComplexSphere.Sphere)
    (previous : Finset (RectangleSphericalImageArc g angle))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ arc : RectangleSphericalImageArc g angle,
      (arc.first ∉ forbidden ∧ arc.last ∉ forbidden) ∧
      (∀ z ∈ closure arc.neighborhood,
        dist (z : ℂ) (Complex.exp ((angle : ℂ) * I)) < ε) ∧
      (∀ t : unitInterval,
        dist (arc.source t) (Complex.exp ((angle : ℂ) * I)) < ε) ∧
      Metric.ediam (range arc.source) < ENNReal.ofReal ε ∧
      Metric.ediam (range arc.image) < ENNReal.ofReal ε ∧
      ∀ old ∈ previous, closure arc.neighborhood ⊆ old.neighborhood ∧
        Disjoint (range old.source) (range arc.source) ∧
        Disjoint (range old.image) (range arc.image) := by
  classical
  let anchor : closedBall (0 : ℂ) 1 :=
    ⟨Complex.exp ((angle : ℂ) * I), by simp [mem_closedBall, Complex.norm_exp]⟩
  let U : Set (closedBall (0 : ℂ) 1) := ⋂ old ∈ previous, old.neighborhood
  have hopen : IsOpen U := isOpen_biInter_finset fun old _ => old.isOpen_neighborhood
  have hanchor : anchor ∈ U := by
    simp only [U, mem_iInter]
    exact fun old _ => old.boundaryPoint_mem_neighborhood
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp hopen anchor hanchor
  let excluded := forbidden ∪ previous.biUnion (fun old => {old.first, old.last})
  obtain ⟨width, hw, left, hl, right, hr, p, q, source, image, hs, hi,
    hp, hq, hpa, hqa, hpq, hagrees, hclose, hds, hdi, height, hh, hformula, hfilled⟩ :=
    exists_short_embedded_spherical_image_rectangle_arc hg hinj angle
      (lt_min hδ hε) hε excluded
  let arc : RectangleSphericalImageArc g angle :=
    { toEmbeddedSphericalImageArc :=
        ⟨width, hw, left, hl, right, hr, p, q, source, image,
          hs, hi, hp, hq, hpq, hagrees⟩
      height := height
      height_mem := hh
      source_formula := hformula }
  have hclosure (z : closedBall (0 : ℂ) 1) (hz : z ∈ closure arc.neighborhood) :
      dist (z : ℂ) (Complex.exp ((angle : ℂ) * I)) < min δ ε := by
    have hmem : (z : ℂ) ∈ Subtype.val '' closure arc.neighborhood := ⟨z, hz, rfl⟩
    rw [arc.closure_neighborhood] at hmem
    rcases hmem with ⟨w, hw, heq⟩
    rw [← heq]
    exact hfilled w hw.1 hw.2
  have hnested (old : RectangleSphericalImageArc g angle) (hold : old ∈ previous) :
      closure arc.neighborhood ⊆ old.neighborhood := by
    intro z hz
    have hzball : z ∈ ball anchor δ := (hclosure z hz).trans_le (min_le_left δ ε)
    have hzU := hball hzball
    exact mem_iInter.mp (mem_iInter.mp hzU old) hold
  refine ⟨arc, ⟨fun h => hpa (Finset.mem_union_left _ h),
      fun h => hqa (Finset.mem_union_left _ h)⟩,
    fun z hz => (hclosure z hz).trans_le (min_le_right δ ε),
    fun t => (hclose t).trans_le (min_le_right δ ε),
    hds.trans_le (ENNReal.ofReal_le_ofReal (min_le_right δ ε)), hdi, ?_⟩
  intro old hold
  have hsource : Disjoint (range old.source) (range arc.source) := by
    apply Set.disjoint_left.mpr
    intro z hzold hznew
    rw [← old.frontier_neighborhood] at hzold
    rw [← arc.frontier_neighborhood] at hznew
    rcases hzold with ⟨u, hu, rfl⟩
    rcases hznew with ⟨v, hv, heq⟩
    have huv : v = u := Subtype.ext heq
    subst v
    exact Set.disjoint_left.mp
      (disjoint_frontier_iff_isOpen.mpr old.isOpen_neighborhood)
      hu (hnested old hold (frontier_subset_closure hv))
  have hend : Disjoint ({old.first, old.last} : Set ComplexSphere.Sphere)
      {arc.first, arc.last} := by
    apply Set.disjoint_left.mpr
    intro z hz hz'
    have hmem : z ∈ excluded := Finset.mem_union_right _
      (Finset.mem_biUnion.mpr ⟨old, hold, by simpa using hz⟩)
    rcases hz' with rfl | hz'
    · exact hpa hmem
    · rw [mem_singleton_iff] at hz'
      change z = q at hz'
      rw [hz'] at hmem
      exact hqa hmem
  exact ⟨hnested old hold, hsource,
    EmbeddedSphericalImageArc.disjoint_image_of_disjoint_source hg hinj
      old.toEmbeddedSphericalImageArc arc.toEmbeddedSphericalImageArc hsource hend⟩

/-- One selection recursion gives nested relatively open source neighborhoods
with their exact source-arc frontiers and pairwise disjoint full image ranges.
Finite forbidden endpoint values are retained throughout the sequence. -/
theorem exists_nested_shrinking_spherical_image_arcs
    {g : ℂ → ℂ} (hg : DifferentiableOn ℂ g (ball 0 1))
    (hinj : InjOn g (ball 0 1)) (angle : ℝ)
    (forbidden : Finset ComplexSphere.Sphere) :
    ∃ arcs : ℕ → RectangleSphericalImageArc g angle,
      ∃ ε : ℕ → ℝ, (∀ n, 0 < ε n) ∧ Tendsto ε atTop (𝓝 0) ∧
      (∀ n, ((arcs n).first ∉ forbidden ∧ (arcs n).last ∉ forbidden) ∧
        (∀ z ∈ closure (arcs n).neighborhood,
          dist (z : ℂ) (Complex.exp ((angle : ℂ) * I)) < ε n) ∧
        (∀ t : unitInterval,
          dist ((arcs n).source t) (Complex.exp ((angle : ℂ) * I)) < ε n) ∧
        Metric.ediam (range (arcs n).source) < ENNReal.ofReal (ε n) ∧
        Metric.ediam (range (arcs n).image) < ENNReal.ofReal (ε n)) ∧
      (∀ m n, m < n → closure (arcs n).neighborhood ⊆ (arcs m).neighborhood) ∧
      Pairwise (fun m n => Disjoint (range (arcs m).source) (range (arcs n).source)) ∧
      Pairwise (fun m n => Disjoint (range (arcs m).image) (range (arcs n).image)) ∧
      Tendsto (fun n => Metric.ediam (range (arcs n).source)) atTop (𝓝 0) ∧
      Tendsto (fun n => Metric.ediam (range (arcs n).image)) atTop (𝓝 0) := by
  classical
  let A := ℕ × RectangleSphericalImageArc g angle
  let P (a : A) : Prop :=
    (a.2.first ∉ forbidden ∧ a.2.last ∉ forbidden) ∧
    (∀ z ∈ closure a.2.neighborhood,
      dist (z : ℂ) (Complex.exp ((angle : ℂ) * I)) < 1 / ((a.1 : ℝ) + 1)) ∧
    (∀ t : unitInterval, dist (a.2.source t) (Complex.exp ((angle : ℂ) * I)) <
      1 / ((a.1 : ℝ) + 1)) ∧
    Metric.ediam (range a.2.source) < ENNReal.ofReal (1 / ((a.1 : ℝ) + 1)) ∧
    Metric.ediam (range a.2.image) < ENNReal.ofReal (1 / ((a.1 : ℝ) + 1))
  let R (a b : A) : Prop := a.1 < b.1 ∧
    closure b.2.neighborhood ⊆ a.2.neighborhood ∧
    Disjoint (range a.2.source) (range b.2.source) ∧
    Disjoint (range a.2.image) (range b.2.image)
  obtain ⟨seq, hseq, hrel⟩ := exists_seq_of_forall_finset_exists P R (by
    intro previous _
    let k := previous.sup Prod.fst + 1
    obtain ⟨arc, havoid, hclosure, hclose, hs, hi, hnested⟩ :=
      exists_rectangle_arc_inside_finite_neighborhoods hg hinj angle forbidden
        (previous.image Prod.snd) (show 0 < 1 / ((k : ℝ) + 1) by positivity)
    refine ⟨(k, arc), ⟨havoid, hclosure, hclose, hs, hi⟩, ?_⟩
    intro old hold
    exact ⟨Nat.lt_succ_of_le (Finset.le_sup hold),
      hnested old.2 (Finset.mem_image.mpr ⟨old, hold, rfl⟩)⟩)
  have hmono : StrictMono (fun n => (seq n).1) := fun m n hmn => (hrel m n hmn).1
  let ε : ℕ → ℝ := fun n => 1 / (((seq n).1 : ℝ) + 1)
  have hε : Tendsto ε atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat.comp hmono.tendsto_atTop
  have hε' : Tendsto (fun n => ENNReal.ofReal (ε n)) atTop (𝓝 0) := by
    have h := ENNReal.continuous_ofReal.continuousAt.tendsto.comp hε
    simp only [Function.comp_def, ENNReal.ofReal_zero] at h
    convert! h using 1
  refine ⟨fun n => (seq n).2, ε, fun n => by dsimp [ε]; positivity,
    hε, hseq, fun m n hmn => (hrel m n hmn).2.1, ?_, ?_, ?_, ?_⟩
  · intro m n hmn
    rcases lt_or_gt_of_ne hmn with h | h
    · exact (hrel m n h).2.2.1
    · exact (hrel n m h).2.2.1.symm
  · intro m n hmn
    rcases lt_or_gt_of_ne hmn with h | h
    · exact (hrel m n h).2.2.2
    · exact (hrel n m h).2.2.2.symm
  · exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hε'
      (fun _ => zero_le) (fun n => (hseq n).2.2.2.1.le)
  · exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hε'
      (fun _ => zero_le) (fun n => (hseq n).2.2.2.2.le)

/-- Forgetting the rectangle neighborhoods recovers the disjoint shrinking arc
statement without a second recursion. -/
theorem exists_disjoint_shrinking_spherical_image_arcs
    {g : ℂ → ℂ} (hg : DifferentiableOn ℂ g (ball 0 1))
    (hinj : InjOn g (ball 0 1)) (angle : ℝ) :
    ∃ arcs : ℕ → EmbeddedSphericalImageArc g angle,
      ∃ ε : ℕ → ℝ, (∀ n, 0 < ε n) ∧ Tendsto ε atTop (𝓝 0) ∧
      (∀ n, (∀ t : unitInterval,
        dist ((arcs n).source t) (Complex.exp ((angle : ℂ) * I)) < ε n) ∧
        Metric.ediam (range (arcs n).source) < ENNReal.ofReal (ε n) ∧
        Metric.ediam (range (arcs n).image) < ENNReal.ofReal (ε n)) ∧
      Pairwise (fun m n => Disjoint (range (arcs m).source) (range (arcs n).source)) ∧
      Pairwise (fun m n => Disjoint (range (arcs m).image) (range (arcs n).image)) ∧
      Tendsto (fun n => Metric.ediam (range (arcs n).source)) atTop (𝓝 0) ∧
      Tendsto (fun n => Metric.ediam (range (arcs n).image)) atTop (𝓝 0) := by
  obtain ⟨arcs, ε, hpos, hlim, hdata, _, hs, hi, hds, hdi⟩ :=
    exists_nested_shrinking_spherical_image_arcs hg hinj angle ∅
  exact ⟨fun n => (arcs n).toEmbeddedSphericalImageArc, ε, hpos, hlim,
    fun n => (hdata n).2.2, hs, hi, hds, hdi⟩

end Math.ComplexAnalysis
