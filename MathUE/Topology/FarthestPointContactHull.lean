import MathUE.Topology.CompactConvexHull
import Mathlib.Analysis.Convex.Intrinsic
import Mathlib.Analysis.InnerProductSpace.Continuous
import Mathlib.Analysis.InnerProductSpace.Projection.Minimal
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith

/-!
# Contacts of a farthest point

In a finite-dimensional real inner-product space, a point maximizing distance
to a compact set containing the relative boundary of a convex region belongs
to the convex hull of its nearest contacts. The metric is the actual Euclidean
inner-product metric, not an equivalent arbitrary norm.
-/

open Set Filter Metric
open scoped Topology

namespace Math.Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- A distance maximizer lies in the hull of its actual nearest contacts.
Neither the compact contact set nor its root inventory need be finite. -/
theorem mem_convexHull_contacts_of_farthestPoint
    (P K : Set E) (z : E)
    (hP : Convex ℝ P) (hPcompact : IsCompact P)
    (hK : IsCompact K) (hKP : K ⊆ P)
    (hfrontier : intrinsicFrontier ℝ P ⊆ K)
    (hz : z ∈ P) (hKnonempty : K.Nonempty)
    (hmax : ∀ x ∈ P, infDist x K ≤ infDist z K) :
    z ∈ convexHull ℝ (closedBall z (infDist z K) ∩ K) := by
  classical
  let d := infDist z K
  let contacts := closedBall z d ∩ K
  have hd : 0 ≤ d := infDist_nonneg
  obtain ⟨nearest, hnearestK, hnearestDist⟩ := hK.exists_infDist_eq_dist hKnonempty z
  have hcontacts : contacts.Nonempty :=
    ⟨nearest, ⟨by simpa only [mem_closedBall, dist_comm] using hnearestDist.ge, hnearestK⟩⟩
  by_cases hd0 : d = 0
  · have hnearest : z = nearest := by
      apply dist_eq_zero.mp
      exact hnearestDist.symm.trans hd0
    have hzK : z ∈ K := hnearest.symm ▸ hnearestK
    exact subset_convexHull ℝ contacts
      ⟨by simpa only [mem_closedBall, dist_self] using hd, hzK⟩
  have hdpos : 0 < d := lt_of_le_of_ne hd (Ne.symm hd0)
  have hcontactsCompact : IsCompact contacts := hK.inter_left isClosed_closedBall
  let hull := convexHull ℝ contacts
  have hhullCompact : IsCompact hull :=
    isCompact_convexHull_of_finiteDimensional hcontactsCompact
  have hhullConvex : Convex ℝ hull := convex_convexHull ℝ contacts
  by_contra hzHull
  obtain ⟨y, hyHull, hyMin⟩ := exists_norm_eq_iInf_of_complete_convex
    (convexHull_nonempty_iff.mpr hcontacts) hhullCompact.isComplete hhullConvex z
  have hprojection := (norm_eq_iInf_iff_real_inner_le_zero hhullConvex hyHull).mp hyMin
  let direction := z - y
  have hdirection : 0 < ‖direction‖ ^ 2 := by
    apply sq_pos_of_pos
    apply norm_pos_iff.mpr
    exact sub_ne_zero.mpr fun heq =>
      hzHull ((congrArg (fun point : E => point ∈ hull) heq).mpr hyHull)
  dsimp only [direction] at hdirection
  have hseparate : ∀ x ∈ hull, inner ℝ direction (x - z) < 0 := by
    intro x hx
    have h := hprojection x hx
    have heq : inner ℝ direction (x - z) =
        inner ℝ direction (x - y) - ‖direction‖ ^ 2 := by
      have hsub : x - z = (x - y) - direction := by dsimp [direction]; abel
      rw [hsub, inner_sub_right, real_inner_self_eq_norm_sq]
    rw [heq]
    dsimp [direction] at h ⊢
    linarith
  have hyP : y ∈ P :=
    convexHull_min (fun _ hx => hKP hx.2) hP hyHull
  have hzNotFrontier : z ∉ intrinsicFrontier ℝ P := by
    intro hzFrontier
    have hdist := infDist_le_dist_of_mem (x := z) (hfrontier hzFrontier)
    have : d ≤ 0 := by simpa only [dist_self] using hdist
    exact hdpos.not_ge this
  have hzInterior : z ∈ intrinsicInterior ℝ P := by
    rw [← closure_sdiff_intrinsicFrontier (𝕜 := ℝ) P]
    exact ⟨by rw [hPcompact.isClosed.closure_eq]; exact hz, hzNotFrontier⟩
  obtain ⟨zAffine, hzAffine, hzAffineEq⟩ := mem_intrinsicInterior.mp hzInterior
  have hshiftSpan : ∀ t : ℝ, z + t • direction ∈ affineSpan ℝ P := by
    intro t
    have hline := AffineMap.lineMap_mem (-t)
      (subset_affineSpan ℝ P hz) (subset_affineSpan ℝ P hyP)
    convert hline using 1
    rw [AffineMap.lineMap_apply_module']
    dsimp [direction]
    simp only [neg_smul, smul_sub]
    abel
  let shift : ℝ → affineSpan ℝ P := fun t => ⟨z + t • direction, hshiftSpan t⟩
  have hshiftContinuous : Continuous shift :=
    (continuous_const.add (continuous_id.smul continuous_const)).subtype_mk _
  have hshiftZero : shift 0 = zAffine := by
    apply Subtype.ext
    simpa only [shift, zero_smul, add_zero] using hzAffineEq.symm
  have hnearP : ∀ᶠ t in 𝓝 (0 : ℝ), z + t • direction ∈ P := by
    have hbase : shift 0 ∈ interior ((↑) ⁻¹' P : Set (affineSpan ℝ P)) := by
      rw [hshiftZero]
      exact hzAffine
    filter_upwards [(hshiftContinuous.tendsto 0).eventually
      (isOpen_interior.mem_nhds hbase)] with t ht
    have hsubtype : shift t ∈ ((↑) ⁻¹' P : Set (affineSpan ℝ P)) :=
      (interior_subset : interior ((↑) ⁻¹' P : Set (affineSpan ℝ P)) ⊆
        ((↑) ⁻¹' P : Set (affineSpan ℝ P))) ht
    change (shift t : E) ∈ P at hsubtype
    exact hsubtype
  have hdistContinuous : Continuous
      (fun pair : ℝ × E => dist (z + pair.1 • direction) pair.2) :=
    (continuous_const.add (continuous_fst.smul continuous_const)).dist continuous_snd
  have hinnerContinuous : Continuous
      (fun pair : ℝ × E => inner ℝ direction (pair.2 - z)) :=
    continuous_const.inner (continuous_snd.sub continuous_const)
  have hgoodOpen : IsOpen {pair : ℝ × E |
      d < dist (z + pair.1 • direction) pair.2 ∨
        inner ℝ direction (pair.2 - z) < 0} :=
    (isOpen_lt continuous_const hdistContinuous).union
      (isOpen_lt hinnerContinuous continuous_const)
  have hnearK : ∀ᶠ t in 𝓝 (0 : ℝ), ∀ x ∈ K,
      d < dist (z + t • direction) x ∨ inner ℝ direction (x - z) < 0 := by
    apply hK.eventually_forall_of_forall_eventually
    intro x hxK
    apply hgoodOpen.mem_nhds
    change d < dist (z + (0 : ℝ) • direction) x ∨ inner ℝ direction (x - z) < 0
    simp only [zero_smul, add_zero]
    by_cases hx : dist z x ≤ d
    · exact Or.inr (hseparate x (subset_convexHull ℝ contacts
        ⟨by simpa only [mem_closedBall, dist_comm] using hx, hxK⟩))
    · exact Or.inl (lt_of_not_ge hx)
  obtain ⟨radius, hradius, hsmall⟩ := Metric.eventually_nhds_iff.mp (hnearP.and hnearK)
  let t := radius / 2
  have ht : 0 < t := half_pos hradius
  have htSmall : dist t 0 < radius := by
    rw [Real.dist_eq, sub_zero, abs_of_pos ht]
    dsimp [t]
    linarith
  obtain ⟨htP, htK⟩ := hsmall htSmall
  obtain ⟨x, hxK, hxDist⟩ := hK.exists_infDist_eq_dist hKnonempty (z + t • direction)
  have hxUpper : dist (z + t • direction) x ≤ d := by
    rw [← hxDist]
    exact hmax _ htP
  have hxInner : inner ℝ direction (x - z) < 0 :=
    (htK x hxK).resolve_left (not_lt.mpr hxUpper)
  have hxLower : d ≤ ‖x - z‖ := by
    simpa only [dist_eq_norm, norm_sub_rev] using infDist_le_dist_of_mem (x := z) hxK
  have hnorm : ‖(x - z) - t • direction‖ ≤ d := by
    have heq : (x - z) - t • direction = -(z + t • direction - x) := by abel
    rw [heq, norm_neg]
    simpa only [dist_eq_norm] using hxUpper
  have hsquare : ‖(x - z) - t • direction‖ ^ 2 ≤ ‖x - z‖ ^ 2 := by
    simpa only [pow_two] using
      mul_self_le_mul_self (norm_nonneg _) (hnorm.trans hxLower)
  rw [norm_sub_sq_real, real_inner_smul_right, real_inner_comm direction (x - z)] at hsquare
  have hproduct : t * inner ℝ direction (x - z) < 0 := mul_neg_of_pos_of_neg ht hxInner
  nlinarith [sq_nonneg ‖t • direction‖]

end Math.Topology
