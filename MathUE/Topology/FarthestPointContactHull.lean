import MathUE.Topology.CompactConvexHull
import Mathlib.Analysis.Convex.Intrinsic
import Mathlib.Analysis.Convex.Exposed
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.InnerProductSpace.Continuous
import Mathlib.Analysis.InnerProductSpace.Projection.Minimal
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Tactic.Choose
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Ring
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
open scoped Topology BigOperators

namespace Math.Topology

/-- A convex-hull point internally selects a minimum-cardinality finite family.
Its affine independence bounds its size by the affine dimension of any containing
set, rather than by the full ambient dimension. -/
theorem exists_minimal_affineIndependent_finset_of_mem_convexHull
    {V : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
    (source region : Set V) (point : V) (hsource : source ⊆ region)
    (hpoint : point ∈ convexHull ℝ source) :
    ∃ family : Finset V,
      family.Nonempty ∧ (family : Set V) ⊆ source ∧
      point ∈ convexHull ℝ (family : Set V) ∧
      AffineIndependent ℝ ((↑) : family → V) ∧
      family.card ≤ Module.finrank ℝ (vectorSpan ℝ region) + 1 ∧
      ∀ alternative : Finset V, (alternative : Set V) ⊆ source →
        point ∈ convexHull ℝ (alternative : Set V) →
        family.card ≤ alternative.card := by
  classical
  let family := Caratheodory.minCardFinsetOfMemConvexHull hpoint
  have hsubset : (family : Set V) ⊆ source :=
    Caratheodory.minCardFinsetOfMemConvexHull_subseteq hpoint
  have hindependent : AffineIndependent ℝ ((↑) : family → V) :=
    Caratheodory.affineIndependent_minCardFinsetOfMemConvexHull hpoint
  have hspan : vectorSpan ℝ (Set.range ((↑) : family → V)) ≤
      vectorSpan ℝ region := by
    apply vectorSpan_mono ℝ
    rintro _ ⟨member, rfl⟩
    exact hsource (hsubset member.property)
  have hcard := hindependent.card_le_finrank_succ.trans
    (Nat.add_le_add_right (Submodule.finrank_mono hspan) 1)
  refine ⟨family, Caratheodory.minCardFinsetOfMemConvexHull_nonempty hpoint,
    hsubset, Caratheodory.mem_minCardFinsetOfMemConvexHull hpoint,
    hindependent, ?_, ?_⟩
  · simpa only [Fintype.card_coe] using hcard
  · intro alternative halternative hmem
    exact Caratheodory.minCardFinsetOfMemConvexHull_card_le_card hpoint
      halternative hmem

/-- Minimality of the actual contact family makes every convex coefficient
strictly positive. The coefficients are selected, not supplied. -/
theorem exists_pos_weights_of_minimal_convexHull_family
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (family : Finset V) (z : V)
    (hz : z ∈ convexHull ℝ (family : Set V))
    (hminimal : ∀ alternative : Finset V, (alternative : Set V) ⊆ family →
      z ∈ convexHull ℝ (alternative : Set V) → family.card ≤ alternative.card) :
    ∃ weight : family → ℝ, (∀ k, 0 < weight k) ∧
      ∑ k, weight k = 1 ∧ ∑ k, weight k • (k : V) = z := by
  classical
  obtain ⟨weight, hnonneg, hsum, hvalue⟩ := Finset.mem_convexHull'.mp hz
  have hpos (k : family) : 0 < weight k := by
    by_contra hnot
    have hzero : weight k = 0 := le_antisymm (not_lt.mp hnot) (hnonneg k k.property)
    have hsumErase : ∑ y ∈ family.erase k, weight y = 1 := by
      have h := Finset.sum_erase_add family weight k.property
      rw [hzero, add_zero, hsum] at h
      exact h
    have hvalueErase : ∑ y ∈ family.erase k, weight y • y = z := by
      have h := Finset.sum_erase_add family (fun y => weight y • y) k.property
      rw [hzero, zero_smul, add_zero, hvalue] at h
      exact h
    have hzErase : z ∈ convexHull ℝ (family.erase k : Set V) :=
      Finset.mem_convexHull'.mpr ⟨weight,
        fun y hy => hnonneg y (Finset.mem_of_mem_erase hy), hsumErase, hvalueErase⟩
    exact (Finset.card_erase_lt_of_mem k.property).not_ge
      (hminimal (family.erase k) (fun _ h => Finset.mem_of_mem_erase h) hzErase)
  refine ⟨fun k => weight k, hpos, ?_, ?_⟩
  · rw [family.sum_coe_sort (fun y => weight y)]
    exact hsum
  · rw [family.sum_coe_sort (fun y => weight y • y)]
    exact hvalue

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- The affine supporting coordinate obtained by normalizing an actual
contact normal and its actual minimum on the region. -/
noncomputable def contactSupportingCoordinate
    (normal : E) (minimum scale : ℝ) : E →ᵃ[ℝ] ℝ :=
  scale • ((innerSL ℝ normal).toLinearMap.toAffineMap - AffineMap.const ℝ E minimum)

omit [FiniteDimensional ℝ E] in
@[simp] theorem contactSupportingCoordinate_apply
    (normal : E) (minimum scale : ℝ) (x : E) :
    contactSupportingCoordinate normal minimum scale x =
      scale * (inner ℝ normal x - minimum) := rfl

/-- A distance maximizer lies in the hull of its actual nearest contacts.
Neither the compact contact set nor its root inventory need be finite. -/
theorem mem_convexHull_contacts_of_farthestPoint
    (P K : Set E) (z : E)
    (hP : Convex ℝ P)
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
    exact ⟨subset_closure hz, hzNotFrontier⟩
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

/-- The farthest point has an internally selected minimal finite family of
actual nearest contacts. Its size is controlled by the region's affine span,
including when that region is a lower-dimensional face. -/
theorem exists_minimal_affineIndependent_contacts_of_farthestPoint
    (P K : Set E) (z : E)
    (hP : Convex ℝ P)
    (hK : IsCompact K) (hKP : K ⊆ P)
    (hfrontier : intrinsicFrontier ℝ P ⊆ K)
    (hz : z ∈ P) (hKnonempty : K.Nonempty)
    (hmax : ∀ x ∈ P, infDist x K ≤ infDist z K) :
    ∃ contacts : Finset E,
      contacts.Nonempty ∧ (contacts : Set E) ⊆ closedBall z (infDist z K) ∩ K ∧
      z ∈ convexHull ℝ (contacts : Set E) ∧
      AffineIndependent ℝ ((↑) : contacts → E) ∧
      contacts.card ≤ Module.finrank ℝ (vectorSpan ℝ P) + 1 ∧
      ∀ alternative : Finset E,
        (alternative : Set E) ⊆ closedBall z (infDist z K) ∩ K →
        z ∈ convexHull ℝ (alternative : Set E) →
        contacts.card ≤ alternative.card := by
  exact exists_minimal_affineIndependent_finset_of_mem_convexHull
    (closedBall z (infDist z K) ∩ K) P z (fun _ hcontact => hKP hcontact.2)
    (mem_convexHull_contacts_of_farthestPoint P K z hP hK hKP
      hfrontier hz hKnonempty hmax)

/-- Projecting a point of the affine hull outside a compact convex region
internally gives a nearest point on its relative frontier. -/
theorem exists_nearestPoint_mem_intrinsicFrontier_of_not_mem
    (P : Set E) (center : E) (hP : Convex ℝ P) (hPcompact : IsCompact P)
    (hPnonempty : P.Nonempty) (hcenterSpan : center ∈ affineSpan ℝ P)
    (hcenter : center ∉ P) :
    ∃ nearest ∈ intrinsicFrontier ℝ P,
      (∀ point ∈ P, dist center nearest ≤ dist center point) ∧
      ∀ point ∈ P, inner ℝ (center - nearest) (point - nearest) ≤ 0 := by
  obtain ⟨nearest, hnearest, hminimum⟩ :=
    exists_norm_eq_iInf_of_complete_convex hPnonempty hPcompact.isComplete hP center
  let : Nonempty P := hPnonempty.to_subtype
  have hnormal := (norm_eq_iInf_iff_real_inner_le_zero hP hnearest).mp hminimum
  have hdist (point : E) (hpoint : point ∈ P) :
      dist center nearest ≤ dist center point := by
    rw [dist_eq_norm, dist_eq_norm, hminimum]
    have hbounded : BddBelow (Set.range (fun point : P => ‖center - (point : E)‖)) :=
      ⟨0, Set.forall_mem_range.mpr (fun point => norm_nonneg (center - (point : E)))⟩
    exact ciInf_le hbounded ⟨point, hpoint⟩
  have hnotInterior : nearest ∉ intrinsicInterior ℝ P := by
    intro hinterior
    obtain ⟨nearestAffine, hrelativeInterior, hequal⟩ :=
      mem_intrinsicInterior.mp hinterior
    have hshiftSpan (time : ℝ) :
        nearest + time • (center - nearest) ∈ affineSpan ℝ P := by
      have h := (affineSpan ℝ P).smul_vsub_vadd_mem time hcenterSpan
        (subset_affineSpan ℝ P hnearest) (subset_affineSpan ℝ P hnearest)
      simpa only [vsub_eq_sub, vadd_eq_add, add_comm] using h
    let shift : ℝ → affineSpan ℝ P :=
      fun time => ⟨nearest + time • (center - nearest), hshiftSpan time⟩
    have hcontinuous : Continuous shift :=
      (continuous_const.add (continuous_id.smul continuous_const)).subtype_mk _
    have hzero : shift 0 = nearestAffine := by
      apply Subtype.ext
      simpa only [shift, zero_smul, add_zero] using hequal.symm
    have hnear : ∀ᶠ time in 𝓝 (0 : ℝ),
        nearest + time • (center - nearest) ∈ P := by
      have hbase : shift 0 ∈ interior ((↑) ⁻¹' P : Set (affineSpan ℝ P)) :=
        hzero.symm ▸ hrelativeInterior
      filter_upwards [(hcontinuous.tendsto 0).eventually
        (isOpen_interior.mem_nhds hbase)] with time htime
      have hsubtype : shift time ∈ ((↑) ⁻¹' P : Set (affineSpan ℝ P)) :=
        (interior_subset : interior ((↑) ⁻¹' P : Set (affineSpan ℝ P)) ⊆
          ((↑) ⁻¹' P : Set (affineSpan ℝ P))) htime
      exact hsubtype
    obtain ⟨radius, hradius, hsmall⟩ := Metric.eventually_nhds_iff.mp hnear
    let time := radius / 2
    have htime : 0 < time := half_pos hradius
    have htimeSmall : dist time 0 < radius := by
      rw [Real.dist_eq, sub_zero, abs_of_pos htime]
      dsimp only [time]
      linarith
    have hpositive : 0 < ‖center - nearest‖ ^ 2 := by
      apply sq_pos_of_pos
      apply norm_pos_iff.mpr
      exact sub_ne_zero.mpr (fun heq => hcenter (heq.symm ▸ hnearest))
    have h := hnormal _ (hsmall htimeSmall)
    rw [show nearest + time • (center - nearest) - nearest =
        time • (center - nearest) by abel,
      real_inner_smul_right, real_inner_self_eq_norm_sq] at h
    exact (not_lt_of_ge h) (mul_pos htime hpositive)
  refine ⟨nearest, ?_, hdist, hnormal⟩
  rw [← closure_sdiff_intrinsicInterior (𝕜 := ℝ) P,
    hPcompact.isClosed.closure_eq]
  exact ⟨hnearest, hnotInterior⟩

/-- The shifted ball in Sorin's continuation replacement contains an actual
point of K different from the continuation payoff. The strict supporting
inequality rules out the continuation as an exterior nearest projection;
the contact-hull theorem rules out a unique contact at an interior center. -/
theorem exists_other_contact_of_shifted_center
    (P K : Set E) (center continuation : E)
    (hP : Convex ℝ P) (hPcompact : IsCompact P)
    (hK : IsCompact K) (hKP : K ⊆ P) (hKnonempty : K.Nonempty)
    (hfrontier : intrinsicFrontier ℝ P ⊆ K)
    (hcenterSpan : center ∈ affineSpan ℝ P) (hcontinuation : continuation ∈ P)
    (hpositive : 0 < dist center continuation)
    (hmax : ∀ point ∈ P, infDist point K ≤ dist center continuation)
    (hstrict : ∃ lower ∈ P,
      inner ℝ lower (continuation - center) <
        inner ℝ continuation (continuation - center)) :
    ∃ other ∈ K, other ≠ continuation ∧
      dist center other ≤ dist center continuation := by
  classical
  by_cases hcenter : center ∈ P
  · by_contra hnone
    have hsame (other : E) (hother : other ∈ K)
        (hball : dist center other ≤ dist center continuation) :
        other = continuation := by
      by_contra hne
      exact hnone ⟨other, hother, hne, hball⟩
    obtain ⟨nearest, hnearestK, hnearestDist⟩ :=
      hK.exists_infDist_eq_dist hKnonempty center
    have hnearestBall : dist center nearest ≤ dist center continuation := by
      rw [← hnearestDist]
      exact hmax center hcenter
    have hnearest := hsame nearest hnearestK hnearestBall
    have hdist : infDist center K = dist center continuation := by
      rwa [hnearest] at hnearestDist
    have hhull := mem_convexHull_contacts_of_farthestPoint
      P K center hP hK hKP hfrontier hcenter hKnonempty
      (fun point hpoint => (hmax point hpoint).trans_eq hdist.symm)
    have hsingleton : center ∈ ({continuation} : Set E) :=
      convexHull_min (fun other hother => by
        apply Set.mem_singleton_iff.mpr
        apply hsame other hother.2
        simpa only [Metric.mem_closedBall, dist_comm, hdist] using hother.1)
        (convex_singleton continuation) hhull
    have hequal : center = continuation := Set.mem_singleton_iff.mp hsingleton
    exact hpositive.ne' (by simp [hequal])
  · obtain ⟨nearest, hfront, hminimum, hnormal⟩ :=
      exists_nearestPoint_mem_intrinsicFrontier_of_not_mem P center
        hP hPcompact ⟨continuation, hcontinuation⟩ hcenterSpan hcenter
    have hne : nearest ≠ continuation := by
      intro hequal
      obtain ⟨lower, hlower, hstrictLower⟩ := hstrict
      have h := hnormal lower hlower
      rw [hequal] at h
      have hinner : inner ℝ (center - continuation) (lower - continuation) =
          inner ℝ continuation (continuation - center) -
            inner ℝ lower (continuation - center) := by
        rw [show center - continuation = -(continuation - center) by abel,
          inner_neg_left, inner_sub_right,
          real_inner_comm (continuation - center) lower,
          real_inner_comm (continuation - center) continuation]
        ring
      rw [hinner] at h
      linarith
    exact ⟨nearest, hfrontier hfront, hne, hminimum continuation hcontinuation⟩

omit [FiniteDimensional ℝ E] in
/-- A nontrivial partial continuation replacement strictly reduces the
Euclidean distance to the original center whenever its replacement lies in
the paper's shifted closed ball. This is the squared-distance step of case (a). -/
theorem dist_partial_replacement_lt
    (contact center continuation replacement : E) (coefficient : ℝ)
    (hcoefficient : coefficient ∈ Set.Ioo 0 1)
    (hne : replacement ≠ continuation)
    (hball : dist replacement (continuation - contact + center) ≤ dist contact center) :
    dist (contact + coefficient • (replacement - continuation)) center <
      dist contact center := by
  let difference := replacement - continuation
  let direction := contact - center
  have hdifference : 0 < ‖difference‖ ^ 2 := by
    apply sq_pos_of_pos
    exact norm_pos_iff.mpr (sub_ne_zero.mpr hne)
  have hballNorm : ‖difference + direction‖ ≤ ‖direction‖ := by
    rw [dist_eq_norm, dist_eq_norm] at hball
    have heq : replacement - (continuation - contact + center) =
        difference + direction := by dsimp only [difference, direction]; abel
    rwa [heq] at hball
  have hballSquare := mul_self_le_mul_self (norm_nonneg _) hballNorm
  simp only [← pow_two] at hballSquare
  rw [norm_add_sq_real] at hballSquare
  have hscaled := mul_le_mul_of_nonneg_left hballSquare hcoefficient.1.le
  have hnorm : ‖coefficient • difference‖ ^ 2 =
      coefficient ^ 2 * ‖difference‖ ^ 2 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hcoefficient.1, mul_pow]
  have hsquare : ‖direction + coefficient • difference‖ ^ 2 < ‖direction‖ ^ 2 := by
    rw [norm_add_sq_real, real_inner_smul_right, hnorm,
      real_inner_comm difference direction]
    have hdrop := mul_pos
      (mul_pos hcoefficient.1 (sub_pos.mpr hcoefficient.2)) hdifference
    nlinarith
  have hnormStrict : ‖direction + coefficient • difference‖ < ‖direction‖ := by
    nlinarith [norm_nonneg (direction + coefficient • difference), norm_nonneg direction]
  rw [dist_eq_norm, dist_eq_norm]
  have heq : contact + coefficient • (replacement - continuation) - center =
      direction + coefficient • difference := by dsimp only [direction, difference]; abel
  rw [heq]
  exact hnormStrict

omit [FiniteDimensional ℝ E] in
/-- Construct the normalized supporting coordinates of the paper's projected
simplex. Its normals are the actual contacts translated by z, and its minima
are attained on P. No coordinates or minima are given as hypotheses. -/
theorem exists_normalized_contact_coordinates
    {I : Type*} [Fintype I]
    (P : Set E) (z : E) (point : I → E) (weight : I → ℝ)
    (hPcompact : IsCompact P) (hz : z ∈ P) (hpoint : ∀ k, point k ∈ P)
    (hpos : ∀ k, 0 < weight k) (hsum : ∑ k, weight k = 1)
    (hvalue : ∑ k, weight k • point k = z) (hne : ∀ k, point k ≠ z) :
    ∃ minimum scale : I → ℝ,
      (∀ k, 0 < scale k) ∧
      (∀ k, ∃ minimizer ∈ P,
        inner ℝ (point k - z) minimizer = minimum k) ∧
      (∀ k x, x ∈ P → minimum k ≤ inner ℝ (point k - z) x) ∧
      (∀ x, ∑ k, contactSupportingCoordinate (point k - z) (minimum k) (scale k) x = 1) ∧
      (∀ k x, x ∈ P →
        0 ≤ contactSupportingCoordinate (point k - z) (minimum k) (scale k) x) ∧
      (∀ k, contactSupportingCoordinate (point k - z) (minimum k) (scale k) z <
        contactSupportingCoordinate (point k - z) (minimum k) (scale k) (point k)) := by
  classical
  have hnonempty : Nonempty I := by
    by_contra hnone
    let : IsEmpty I := not_nonempty_iff.mp hnone
    simp at hsum
  let : Nonempty I := hnonempty
  let normal : I → E := fun k => point k - z
  have hbalance : ∑ k, weight k • normal k = 0 := by
    simp only [normal, smul_sub, Finset.sum_sub_distrib, ← Finset.sum_smul, hsum,
      one_smul, hvalue, sub_self]
  have hminimum (k : I) : ∃ minimizer ∈ P,
      ∀ x ∈ P, inner ℝ (normal k) minimizer ≤ inner ℝ (normal k) x :=
    hPcompact.exists_isMinOn (f := fun x : E => inner ℝ (normal k) x)
      ⟨z, hz⟩ (continuous_const.inner continuous_id).continuousOn
  choose minimizer hminimizer hmin using hminimum
  let minimum : I → ℝ := fun k => inner ℝ (normal k) (minimizer k)
  let denominator : ℝ := -∑ k, weight k * minimum k
  have hnormalSum (x : E) : ∑ k, weight k * inner ℝ (normal k) x = 0 := by
    calc
      ∑ k, weight k * inner ℝ (normal k) x =
          inner ℝ (∑ k, weight k • normal k) x := by
        simp only [sum_inner, real_inner_smul_left]
      _ = 0 := by rw [hbalance, inner_zero_left]
  have htotal (x : E) :
      ∑ k, weight k * (inner ℝ (normal k) x - minimum k) = denominator := by
    simp only [mul_sub, Finset.sum_sub_distrib, hnormalSum, zero_sub, denominator]
  have hdenominator : 0 < denominator := by
    let k : I := Classical.arbitrary I
    rw [← htotal (point k)]
    apply Finset.sum_pos'
    · intro j _
      exact mul_nonneg (hpos j).le (sub_nonneg.mpr (hmin j _ (hpoint k)))
    · refine ⟨k, Finset.mem_univ k, mul_pos (hpos k) ?_⟩
      have hself : inner ℝ (normal k) (point k) - inner ℝ (normal k) z =
          ‖normal k‖ ^ 2 := by
        rw [← inner_sub_right]
        change inner ℝ (normal k) (normal k) = ‖normal k‖ ^ 2
        exact real_inner_self_eq_norm_sq (normal k)
      have hnorm : 0 < ‖normal k‖ ^ 2 :=
        sq_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr (hne k)))
      have hbound := hmin k z hz
      dsimp only [minimum]
      linarith
  let scale : I → ℝ := fun k => weight k / denominator
  refine ⟨minimum, scale, fun k => div_pos (hpos k) hdenominator,
    (fun k => ⟨minimizer k, hminimizer k, rfl⟩), hmin, ?_, ?_, ?_⟩
  · intro x
    change (∑ k, (weight k / denominator) *
      (inner ℝ (normal k) x - minimum k)) = 1
    simp_rw [div_mul_eq_mul_div]
    rw [← Finset.sum_div, htotal, div_self hdenominator.ne']
  · intro k x hx
    exact mul_nonneg (div_pos (hpos k) hdenominator).le
      (sub_nonneg.mpr (hmin k x hx))
  · intro k
    simp only [contactSupportingCoordinate_apply]
    apply mul_lt_mul_of_pos_left ?_ (div_pos (hpos k) hdenominator)
    have hnorm : 0 < ‖normal k‖ ^ 2 :=
      sq_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr (hne k)))
    have hself : inner ℝ (normal k) (point k) - inner ℝ (normal k) z =
        ‖normal k‖ ^ 2 := by
      rw [← inner_sub_right]
      change inner ℝ (normal k) (normal k) = ‖normal k‖ ^ 2
      exact real_inner_self_eq_norm_sq (normal k)
    linarith

omit [FiniteDimensional ℝ E] in
/-- Translation by z turns the contact affine span into its direction space.
This is not the unshifted linear span of the contacts. -/
theorem span_contact_normals_eq_vectorSpan
    {I : Type*} (point : I → E) (z : E)
    (hz : z ∈ affineSpan ℝ (Set.range point)) :
    Submodule.span ℝ (Set.range fun k => point k - z) =
      vectorSpan ℝ (Set.range point) := by
  classical
  have hnonempty : Nonempty I := by
    by_contra hnone
    let : IsEmpty I := not_nonempty_iff.mp hnone
    rw [Set.range_eq_empty point, AffineSubspace.span_empty] at hz
    exact (AffineSubspace.notMem_bot ℝ E z) hz
  let : Nonempty I := hnonempty
  let L := Submodule.span ℝ (Set.range fun k => point k - z)
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨k, rfl⟩
    rw [← direction_affineSpan]
    exact (affineSpan ℝ (Set.range point)).vsub_mem_direction
      (subset_affineSpan ℝ _ (Set.mem_range_self k)) hz
  · let k : I := Classical.arbitrary I
    rw [vectorSpan_range_eq_span_range_vsub_right ℝ point k]
    apply Submodule.span_le.mpr
    rintro _ ⟨j, rfl⟩
    have heq : point j -ᵥ point k = (point j - z) - (point k - z) := by
      simp only [vsub_eq_sub]
      abel
    change point j -ᵥ point k ∈ L
    rw [heq]
    exact Submodule.sub_mem L
      (Submodule.subset_span (Set.mem_range_self j))
      (Submodule.subset_span (Set.mem_range_self k))

/-- Actual orthogonal projection onto the translated contact direction space
preserves every supporting coordinate. No ambient injectivity is asserted. -/
theorem contactSupportingCoordinate_orthogonalProjection
    {I : Type*} (point : I → E) (z : E) (minimum scale : I → ℝ)
    (k : I) (x : E) :
    let L := Submodule.span ℝ (Set.range fun j => point j - z)
    contactSupportingCoordinate (point k - z) (minimum k) (scale k)
        ((L.orthogonalProjectionOnto (x - z) : E) + z) =
      contactSupportingCoordinate (point k - z) (minimum k) (scale k) x := by
  dsimp only
  let L := Submodule.span ℝ (Set.range fun j => point j - z)
  let normal : L := ⟨point k - z, Submodule.subset_span (Set.mem_range_self k)⟩
  have h : inner ℝ (point k - z) (L.orthogonalProjectionOnto (x - z) : E) =
      inner ℝ (point k - z) (x - z) :=
    L.inner_orthogonalProjectionOnto_eq_of_mem_left normal (x - z)
  simp only [contactSupportingCoordinate_apply, inner_add_right]
  rw [h]
  rw [inner_sub_right]
  ring

omit [FiniteDimensional ℝ E] in
/-- The supporting coordinates separate points of the translated contact
direction space. The projection itself may have a nontrivial kernel. -/
theorem contactSupportingCoordinates_injective_on_direction
    {I : Type*} (point : I → E) (z : E) (minimum scale : I → ℝ)
    (hscale : ∀ k, scale k ≠ 0) :
    let L := Submodule.span ℝ (Set.range fun k => point k - z)
    Function.Injective (fun x : L => fun k =>
      contactSupportingCoordinate (point k - z) (minimum k) (scale k) ((x : E) + z)) := by
  dsimp only
  intro x y heq
  have hnormal (k : I) : inner ℝ (point k - z) ((x : E) - y) = 0 := by
    have h := congrFun heq k
    simp only [contactSupportingCoordinate_apply, inner_add_right] at h
    have h' := mul_left_cancel₀ (hscale k) h
    rw [inner_sub_right]
    linarith
  have hall : ∀ v ∈ Submodule.span ℝ (Set.range fun k => point k - z),
      inner ℝ v ((x : E) - y) = 0 := by
    intro v hv
    induction hv using Submodule.span_induction with
    | mem v hv => obtain ⟨k, rfl⟩ := hv; exact hnormal k
    | zero => exact inner_zero_left _
    | add u v hu hv ihu ihv => simp only [inner_add_left, ihu, ihv, add_zero]
    | smul a v hv ih => simp only [real_inner_smul_left, ih, mul_zero]
  have hself := hall ((x : E) - y) (Submodule.sub_mem _ x.property y.property)
  apply Subtype.ext
  exact sub_eq_zero.mp (inner_self_eq_zero.mp hself)

/-- The derived supporting coordinates identify the translated contact
direction space with the sum-one affine hyperplane. In particular the region
cut out by the actual contact halfspaces is the standard simplex in these
coordinates, of dimension `Fintype.card I - 1`. -/
theorem contactSupportingCoordinates_projected_simplex
    {I : Type*} [Fintype I]
    (point : I → E) (z : E) (minimum scale : I → ℝ)
    (hz : z ∈ affineSpan ℝ (Set.range point))
    (hindependent : AffineIndependent ℝ point)
    (hscale : ∀ k, 0 < scale k)
    (hsum : ∀ x, ∑ k,
      contactSupportingCoordinate (point k - z) (minimum k) (scale k) x = 1) :
    let L := Submodule.span ℝ (Set.range fun k => point k - z)
    Module.finrank ℝ L + 1 = Fintype.card I ∧
      ∀ bary : I → ℝ, (∑ k, bary k = 1) →
        ∃! t : L, ∀ k,
          contactSupportingCoordinate (point k - z) (minimum k) (scale k)
            ((t : E) + z) = bary k := by
  classical
  dsimp only
  have hnonempty : Nonempty I := by
    by_contra hnone
    let : IsEmpty I := not_nonempty_iff.mp hnone
    simpa using hsum z
  let : Nonempty I := hnonempty
  let L := Submodule.span ℝ (Set.range fun k => point k - z)
  have hrank : Module.finrank ℝ L + 1 = Fintype.card I := by
    have hequal : Module.finrank ℝ L =
        Module.finrank ℝ (vectorSpan ℝ (Set.range point)) :=
      (LinearEquiv.ofEq L (vectorSpan ℝ (Set.range point))
        (span_contact_normals_eq_vectorSpan point z hz)).finrank_eq
    exact (congrArg (fun n : ℕ => n + 1) hequal).trans
      hindependent.finrank_vectorSpan_add_one
  let sumMap : (I → ℝ) →ₗ[ℝ] ℝ :=
    Fintype.linearCombination ℝ (fun _ : I => (1 : ℝ))
  let W := sumMap.ker
  have hsumMap (bary : I → ℝ) : sumMap bary = ∑ k, bary k := by
    simp only [sumMap, Fintype.linearCombination_apply, smul_eq_mul, mul_one]
  have hsumSurjective : Function.Surjective sumMap := by
    intro r
    let k : I := Classical.arbitrary I
    refine ⟨Pi.single k r, ?_⟩
    simp only [sumMap, Fintype.linearCombination_apply_single, smul_eq_mul, mul_one]
  have hWrank : Module.finrank ℝ W + 1 = Fintype.card I := by
    have h := sumMap.finrank_range_add_finrank_ker
    rw [LinearMap.range_eq_top.mpr hsumSurjective, finrank_top,
      Module.finrank_self, Module.finrank_fintype_fun_eq_card] at h
    dsimp only [W]
    omega
  let raw : L →ₗ[ℝ] (I → ℝ) := LinearMap.pi fun k =>
    scale k • ((innerSL ℝ (point k - z)).toLinearMap.comp L.subtype)
  have hraw (t : L) (k : I) : raw t k =
      contactSupportingCoordinate (point k - z) (minimum k) (scale k) ((t : E) + z) -
        contactSupportingCoordinate (point k - z) (minimum k) (scale k) z := by
    change scale k * inner ℝ (point k - z) (t : E) = _
    simp only [contactSupportingCoordinate_apply, inner_add_right]
    ring
  have hrawW (t : L) : raw t ∈ W := by
    change sumMap (raw t) = 0
    rw [hsumMap]
    simp only [hraw, Finset.sum_sub_distrib, hsum, sub_self]
  let linear : L →ₗ[ℝ] W := raw.codRestrict W hrawW
  have hinjective : Function.Injective linear := by
    intro t u htu
    have hvalues : raw t = raw u := congrArg Subtype.val htu
    apply contactSupportingCoordinates_injective_on_direction
      point z minimum scale (fun k => (hscale k).ne')
    funext k
    have h := congrFun hvalues k
    rw [hraw, hraw] at h
    linarith
  have hdim : Module.finrank ℝ L = Module.finrank ℝ W := by omega
  have hsurjective : Function.Surjective linear :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp hinjective
  refine ⟨hrank, ?_⟩
  intro bary hbary
  let target : W := ⟨fun k => bary k -
      contactSupportingCoordinate (point k - z) (minimum k) (scale k) z, by
    change sumMap _ = 0
    rw [hsumMap]
    simp only [Finset.sum_sub_distrib, hbary, hsum, sub_self]⟩
  obtain ⟨t, ht⟩ := hsurjective target
  have htcoord (k : I) :
      contactSupportingCoordinate (point k - z) (minimum k) (scale k) ((t : E) + z) =
        bary k := by
    have h := congrFun (congrArg Subtype.val ht) k
    change raw t k = bary k -
      contactSupportingCoordinate (point k - z) (minimum k) (scale k) z at h
    rw [hraw] at h
    linarith
  refine ⟨t, htcoord, ?_⟩
  intro u hu
  apply contactSupportingCoordinates_injective_on_direction
    point z minimum scale (fun k => (hscale k).ne')
  funext k
  exact (hu k).trans (htcoord k).symm

/-- The actual supporting halfspaces, restricted to the translated direction
space, correspond exactly to nonnegative sum-one coordinate vectors. This is
the projected simplex, not the original convex hull of contact points. -/
theorem contactSupportingCoordinates_projected_simplex_region
    {I : Type*} [Fintype I]
    (point : I → E) (z : E) (minimum scale : I → ℝ)
    (hz : z ∈ affineSpan ℝ (Set.range point))
    (hindependent : AffineIndependent ℝ point)
    (hscale : ∀ k, 0 < scale k)
    (hsum : ∀ x, ∑ k,
      contactSupportingCoordinate (point k - z) (minimum k) (scale k) x = 1)
    (bary : I → ℝ) (hbary : ∑ k, bary k = 1) (hnonneg : ∀ k, 0 ≤ bary k) :
    let L := Submodule.span ℝ (Set.range fun k => point k - z)
    ∃! t : L, (∀ k, minimum k ≤ inner ℝ (point k - z) ((t : E) + z)) ∧
      ∀ k, contactSupportingCoordinate (point k - z) (minimum k) (scale k)
        ((t : E) + z) = bary k := by
  dsimp only
  obtain ⟨t, ht, hunique⟩ :=
    (contactSupportingCoordinates_projected_simplex
      point z minimum scale hz hindependent hscale hsum).2 bary hbary
  refine ⟨t, ⟨?_, ht⟩, fun u hu => hunique u hu.2⟩
  intro k
  have h := hnonneg k
  rw [← ht k, contactSupportingCoordinate_apply] at h
  have hs := hscale k
  nlinarith

/-- Source-data constructor for both the actual supporting coordinates and
their actual projected simplex. The affine independence is that of the
contacts; only the translated direction-space restriction is injective. -/
theorem exists_projected_contact_simplex
    {I : Type*} [Fintype I]
    (P : Set E) (z : E) (point : I → E) (weight : I → ℝ)
    (hPcompact : IsCompact P) (hz : z ∈ P) (hpoint : ∀ k, point k ∈ P)
    (hpos : ∀ k, 0 < weight k) (hsum : ∑ k, weight k = 1)
    (hvalue : ∑ k, weight k • point k = z) (hne : ∀ k, point k ≠ z)
    (hindependent : AffineIndependent ℝ point) :
    ∃ minimum scale : I → ℝ,
      (∀ k, 0 < scale k) ∧
      (∀ k, ∃ minimizer ∈ P,
        inner ℝ (point k - z) minimizer = minimum k) ∧
      (∀ k x, x ∈ P → minimum k ≤ inner ℝ (point k - z) x) ∧
      (∀ x, ∑ k, contactSupportingCoordinate (point k - z) (minimum k) (scale k) x = 1) ∧
      (∀ k x, x ∈ P →
        0 ≤ contactSupportingCoordinate (point k - z) (minimum k) (scale k) x) ∧
      (∀ k, contactSupportingCoordinate (point k - z) (minimum k) (scale k) z <
        contactSupportingCoordinate (point k - z) (minimum k) (scale k) (point k)) ∧
      let L := Submodule.span ℝ (Set.range fun k => point k - z)
      Module.finrank ℝ L + 1 = Fintype.card I ∧
        ∀ bary : I → ℝ, (∑ k, bary k = 1) →
          ∃! t : L, ∀ k,
            contactSupportingCoordinate (point k - z) (minimum k) (scale k)
              ((t : E) + z) = bary k := by
  obtain ⟨minimum, scale, hscale, hattained, hmin, hcoordSum, hnonneg, hstrict⟩ :=
    exists_normalized_contact_coordinates
      P z point weight hPcompact hz hpoint hpos hsum hvalue hne
  have hcontains : z ∈ convexHull ℝ (Set.range point) := by
    have h := (convex_convexHull ℝ (Set.range point)).sum_mem
      (fun k _ => (hpos k).le) hsum
      (fun k _ => subset_convexHull ℝ _ (Set.mem_range_self k))
    rwa [hvalue] at h
  refine ⟨minimum, scale, hscale, hattained, hmin, hcoordSum, hnonneg, hstrict, ?_⟩
  exact contactSupportingCoordinates_projected_simplex point z minimum scale
    (convexHull_subset_affineSpan _ hcontains) hindependent hscale hcoordSum

/-- A relative-boundary point of a compact convex set belongs to a canonical
exposed convex extreme subset of strictly smaller relative dimension. The
supporting functional is selected in the actual affine-span direction space. -/
theorem exists_proper_exposed_subset_of_mem_intrinsicFrontier
    (P : Set E) (hP : Convex ℝ P) (hPcompact : IsCompact P)
    (x : E) (hx : x ∈ intrinsicFrontier ℝ P) :
    ∃ Q : Set E, x ∈ Q ∧ IsExposed ℝ P Q ∧ Convex ℝ Q ∧
      Module.finrank ℝ (vectorSpan ℝ Q) < Module.finrank ℝ (vectorSpan ℝ P) := by
  classical
  have hxP : x ∈ P := intrinsicFrontier_subset hPcompact.isClosed hx
  let A := affineSpan ℝ P
  let L := A.direction
  let origin : A := ⟨x, subset_affineSpan ℝ P hxP⟩
  let : Nonempty A := ⟨origin⟩
  let shift : L ≃ᵃⁱ[ℝ] A := AffineIsometryEquiv.vaddConst ℝ origin
  let region : Set L := shift ⁻¹' ((↑) ⁻¹' P : Set A)
  have hshift (v : L) : (shift v : E) = (v : E) + x := rfl
  have hregion : Convex ℝ region := hP.affine_preimage
    (A.subtype.comp shift.toAffineEquiv.toAffineMap)
  have hspanInterior : (interior ((↑) ⁻¹' P : Set A)).Nonempty := by
    simpa only [intrinsicInterior, Set.image_nonempty] using
      Set.Nonempty.intrinsicInterior hP ⟨x, hxP⟩
  have hinterior : (interior region).Nonempty := by
    obtain ⟨point, hpoint⟩ := hspanInterior
    refine ⟨shift.symm point, ?_⟩
    change shift.symm point ∈ interior (shift.toHomeomorph ⁻¹' ((↑) ⁻¹' P : Set A))
    rw [← shift.toHomeomorph.preimage_interior]
    change shift (shift.symm point) ∈ interior ((↑) ⁻¹' P : Set A)
    simpa only [AffineIsometryEquiv.apply_symm_apply] using hpoint
  have horiginFrontier : origin ∈ frontier ((↑) ⁻¹' P : Set A) := by
    obtain ⟨point, hpoint, hequal⟩ := mem_intrinsicFrontier.mp hx
    have : point = origin := Subtype.ext hequal
    exact this ▸ hpoint
  have hzeroFrontier : (0 : L) ∈ frontier region := by
    change (0 : L) ∈ frontier (shift.toHomeomorph ⁻¹' ((↑) ⁻¹' P : Set A))
    rw [← shift.toHomeomorph.preimage_frontier]
    change shift 0 ∈ frontier ((↑) ⁻¹' P : Set A)
    have hzero : shift 0 = origin := by
      apply Subtype.ext
      change (0 : E) + x = x
      exact zero_add x
    exact hzero.symm ▸ horiginFrontier
  have hzeroRegion : (0 : L) ∈ region := by
    change (shift 0 : E) ∈ P
    simpa only [hshift, Submodule.coe_zero, zero_add] using hxP
  obtain ⟨functional, hfunctional, hsupport⟩ :=
    geometric_hahn_banach_of_nonempty_interior_point hregion
      ((mem_frontier_iff_notMem_interior hzeroRegion).mp hzeroFrontier) hinterior
  let ambient : E →L[ℝ] ℝ := functional.comp L.orthogonalProjectionOnto
  have hambient (v : L) : ambient (v : E) = functional v := by
    simp only [ambient, ContinuousLinearMap.comp_apply,
      L.orthogonalProjectionOnto_mem_subspace_eq_self]
  have hbound (y : E) (hy : y ∈ P) : ambient y ≤ ambient x := by
    let v : L := ⟨y - x, A.vsub_mem_direction
      (subset_affineSpan ℝ P hy) origin.property⟩
    have hv : v ∈ region := by
      change (shift v : E) ∈ P
      rw [hshift]
      simpa only [v, Subtype.coe_mk, sub_add_cancel] using hy
    have h := hsupport v hv
    have hequal : ambient y - ambient x = functional v := by
      rw [← map_sub]
      exact hambient v
    rw [map_zero] at h
    linarith
  let Q := ambient.toExposed P
  have hxQ : x ∈ Q := ⟨hxP, hbound⟩
  have hQexposed : IsExposed ℝ P Q :=
    ContinuousLinearMap.toExposed.isExposed (l := ambient) (A := P)
  have hQspan : vectorSpan ℝ Q ≤ L := by
    change vectorSpan ℝ Q ≤ (affineSpan ℝ P).direction
    rw [direction_affineSpan]
    exact vectorSpan_mono ℝ hQexposed.subset
  have hQker : vectorSpan ℝ Q ≤ ambient.toLinearMap.ker := by
    rw [vectorSpan_def, Submodule.span_le]
    rintro v ⟨a, ha, b, hb, hequal⟩
    rw [← hequal]
    have haValue : ambient a = ambient x :=
      le_antisymm (hbound a ha.1) (ha.2 x hxP)
    have hbValue : ambient b = ambient x :=
      le_antisymm (hbound b hb.1) (hb.2 x hxP)
    change ambient (a - b) = 0
    rw [map_sub, haValue, hbValue, sub_self]
  have hproper : L ⊓ ambient.toLinearMap.ker < L := by
    apply lt_of_le_of_ne inf_le_left
    intro hequal
    apply hfunctional
    ext v
    have hv : (v : E) ∈ ambient.toLinearMap.ker := by
      have h : (v : E) ∈ L ⊓ ambient.toLinearMap.ker := hequal.symm ▸ v.property
      exact h.2
    change ambient (v : E) = 0 at hv
    change functional v = 0
    exact (hambient v).symm.trans hv
  refine ⟨Q, hxQ, hQexposed, hQexposed.convex hP, ?_⟩
  have hle := Submodule.finrank_mono (le_inf hQspan hQker)
  have hlt := Submodule.finrank_lt_finrank_of_lt hproper
  have hLrank : Module.finrank ℝ L = Module.finrank ℝ (vectorSpan ℝ P) :=
    (LinearEquiv.ofEq L (vectorSpan ℝ P) (direction_affineSpan ℝ P)).finrank_eq
  exact (hle.trans_lt hlt).trans_eq hLrank

/-- Affine inverse images preserve canonical extreme subsets. -/
theorem isExtreme_affine_preimage {V F : Type*}
    [AddCommGroup V] [Module ℝ V] [AddCommGroup F] [Module ℝ F]
    (f : V →ᵃ[ℝ] F) (ambient face : Set F) (hface : IsExtreme ℝ ambient face) :
    IsExtreme ℝ (f ⁻¹' ambient) (f ⁻¹' face) := by
  refine ⟨Set.preimage_mono hface.subset, ?_⟩
  intro x hx y hy z hz hsegment
  apply hface.left_mem_of_mem_openSegment hx hy hz
  rw [← image_openSegment ℝ f x y]
  exact Set.mem_image_of_mem f hsegment

end Math.Topology
