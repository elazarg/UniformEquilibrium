import MathUE.ProbabilityMassFunction.Simplex
import Mathlib.Analysis.Convex.Hull
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Topology.Order.Compact
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Actual endpoints and coordinates of a finite one-dimensional hull

The elementary affine normalization in Sorin (1986), Proposition 7.
Finite coordinate extrema select actual members of the source set; no
segment endpoints or affine parametrization are supplied as certificates.
-/

noncomputable section

namespace Math.Topology

open Set

variable {ι : Type}

/-- Scalar affine coordinate determined by two actual endpoint vectors. -/
def segmentCoordinate (left right : ι → ℝ) (who : ι) (value : ι → ℝ) : ℝ :=
  (value who - left who) / (right who - left who)

theorem segmentCoordinate_continuous (left right : ι → ℝ) (who : ι) :
    Continuous (segmentCoordinate left right who) := by
  exact ((continuous_apply who).sub continuous_const).div_const _

theorem segmentCoordinate_left (left right : ι → ℝ) (who : ι) :
    segmentCoordinate left right who left = 0 := by
  simp [segmentCoordinate]

theorem segmentCoordinate_right (left right : ι → ℝ) (who : ι)
    (hne : right who ≠ left who) :
    segmentCoordinate left right who right = 1 := by
  simp [segmentCoordinate, sub_ne_zero.mpr hne]

theorem segmentCoordinate_mix (left right first tail : ι → ℝ) (who : ι) (a : ℝ) :
    segmentCoordinate left right who (a • first + (1 - a) • tail) =
      a * segmentCoordinate left right who first +
        (1 - a) * segmentCoordinate left right who tail := by
  simp only [segmentCoordinate, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    div_eq_mul_inv]
  ring

theorem segmentCoordinate_replacement (left right value next previous : ι → ℝ)
    (who : ι) (coefficient : ℝ) :
    segmentCoordinate left right who (value + coefficient • (next - previous)) =
      segmentCoordinate left right who value + coefficient *
        (segmentCoordinate left right who next - segmentCoordinate left right who previous) := by
  simp only [segmentCoordinate, Pi.add_apply, Pi.smul_apply, Pi.sub_apply,
    smul_eq_mul, div_eq_mul_inv]
  ring

theorem segmentCoordinate_expect {Ω : Type} [Finite Ω]
    (left right : ι → ℝ) (who : ι) (law : PMF Ω) (value : Ω → ι → ℝ) :
    segmentCoordinate left right who
      (fun player => Math.Probability.expect law (fun point => value point player)) =
      Math.Probability.expect law
        (fun point => segmentCoordinate left right who (value point)) := by
  simp only [segmentCoordinate, div_eq_mul_inv]
  have hfunction : (fun point =>
      (value point who - left who) * (right who - left who)⁻¹) =
      fun point => (right who - left who)⁻¹ * (value point who - left who) := by
    funext point
    ring
  rw [hfunction, Math.Probability.expect_const_mul, Math.Probability.expect_sub,
    Math.Probability.expect_const]
  ring

/-- A finite hull of affine dimension one has two actual endpoint members,
an actual varying coordinate, and an internally derived affine parametrization. -/
theorem exists_interval_coordinate_of_finite
    [Fintype ι]
    (F : Set (ι → ℝ)) (hF : F.Finite)
    (hdimension : Module.finrank ℝ (vectorSpan ℝ F) = 1) :
    ∃ left ∈ F, ∃ right ∈ F, ∃ who : ι,
      left who < right who ∧
      (∀ value ∈ affineSpan ℝ F,
        value = (1 - segmentCoordinate left right who value) • left +
          segmentCoordinate left right who value • right) ∧
      (∀ value ∈ convexHull ℝ F,
        segmentCoordinate left right who value ∈ Icc (0 : ℝ) 1) ∧
      (∀ t ∈ Icc (0 : ℝ) 1, (1 - t) • left + t • right ∈ convexHull ℝ F) := by
  classical
  have hnotSubsingleton : ¬F.Subsingleton := by
    intro hsubsingleton
    rw [vectorSpan_of_subsingleton ℝ hsubsingleton] at hdimension
    simp at hdimension
  obtain ⟨first, hfirst, second, hsecond, hdistinct⟩ :=
    Set.not_subsingleton_iff.mp hnotSubsingleton
  have hdifferent : ∃ who, first who ≠ second who := by
    by_contra hnone
    apply hdistinct
    funext who
    exact not_not.mp (not_exists.mp hnone who)
  obtain ⟨who, hwho⟩ := hdifferent
  obtain ⟨left, hleft, hmin⟩ := hF.isCompact.exists_isMinOn ⟨first, hfirst⟩
    (continuous_apply who).continuousOn
  obtain ⟨right, hright, hmax⟩ := hF.isCompact.exists_isMaxOn ⟨first, hfirst⟩
    (continuous_apply who).continuousOn
  have hordered : left who < right who := by
    have hleftRight : left who ≤ right who := hmin hright
    by_contra hnot
    have hequal : left who = right who := le_antisymm hleftRight (le_of_not_gt hnot)
    apply hwho
    have hfirstMin : left who ≤ first who := hmin hfirst
    have hfirstMax : first who ≤ right who := hmax hfirst
    have hsecondMin : left who ≤ second who := hmin hsecond
    have hsecondMax : second who ≤ right who := hmax hsecond
    linarith
  have hdenom : right who - left who ≠ 0 := (sub_pos.mpr hordered).ne'
  have hdirection : right - left ≠ (0 : ι → ℝ) := by
    intro hequal
    have h := congrFun hequal who
    simp only [Pi.sub_apply, Pi.zero_apply] at h
    exact hdenom h
  have hspan : vectorSpan ℝ F = Submodule.span ℝ {right - left} :=
    eq_span_singleton_of_mem_of_finrank_eq_one hdimension
      (vsub_mem_vectorSpan ℝ hright hleft) hdirection
  have hrepresentation (value : ι → ℝ) (hvalue : value ∈ affineSpan ℝ F) :
      value = (1 - segmentCoordinate left right who value) • left +
        segmentCoordinate left right who value • right := by
    have hdifference : value - left ∈ vectorSpan ℝ F :=
      vsub_mem_vectorSpan_of_mem_affineSpan_of_mem_affineSpan
        hvalue (subset_affineSpan ℝ F hleft)
    rw [hspan] at hdifference
    obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.mp hdifference
    have hscalar := congrFun hr who
    simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul] at hscalar
    have hrCoordinate : r = segmentCoordinate left right who value := by
      unfold segmentCoordinate
      exact (eq_div_iff hdenom).mpr hscalar
    rw [hrCoordinate] at hr
    funext player
    have h := congrFun hr player
    simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul] at h
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    linarith
  let bounds : Set (ι → ℝ) := {value | left who ≤ value who ∧ value who ≤ right who}
  have hboundsConvex : Convex ℝ bounds := by
    intro first hfirst second hsecond a b ha hb hab
    change left who ≤ first who ∧ first who ≤ right who at hfirst
    change left who ≤ second who ∧ second who ≤ right who at hsecond
    change left who ≤ a * first who + b * second who ∧
      a * first who + b * second who ≤ right who
    constructor
    · calc
        left who = a * left who + b * left who := by rw [← add_mul, hab, one_mul]
        _ ≤ a * first who + b * second who := add_le_add
          (mul_le_mul_of_nonneg_left hfirst.1 ha)
          (mul_le_mul_of_nonneg_left hsecond.1 hb)
    · calc
        a * first who + b * second who ≤ a * right who + b * right who := add_le_add
          (mul_le_mul_of_nonneg_left hfirst.2 ha)
          (mul_le_mul_of_nonneg_left hsecond.2 hb)
        _ = right who := by rw [← add_mul, hab, one_mul]
  have hbounds : convexHull ℝ F ⊆ bounds :=
    convexHull_min (fun value hvalue => ⟨hmin hvalue, hmax hvalue⟩) hboundsConvex
  refine ⟨left, hleft, right, hright, who, hordered, hrepresentation, ?_, ?_⟩
  · intro value hvalue
    have h := hbounds hvalue
    unfold segmentCoordinate
    constructor
    · exact div_nonneg (sub_nonneg.mpr h.1) (sub_pos.mpr hordered).le
    · exact (div_le_one (sub_pos.mpr hordered)).mpr (by linarith [h.2])
  · intro t ht
    exact (convex_convexHull ℝ F) (subset_convexHull ℝ F hleft)
      (subset_convexHull ℝ F hright) (sub_nonneg.mpr ht.2) ht.1 (by ring)

end Math.Topology
