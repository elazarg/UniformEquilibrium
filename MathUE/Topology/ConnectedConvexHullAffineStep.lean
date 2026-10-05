import MathUE.Topology.ConnectedConvexHullRepresentation
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Module

/-! # Affine peeling of a connected convex hull

A connected small representation supplies a coefficient at least the
reciprocal dimension. Removing one prescribed stage weight leaves an actual
convex-hull residual. This is the elementary geometric step following the
classical connected-set representation theorem.
-/

noncomputable section

open Set
open scoped BigOperators

namespace Math.Topology

/-- Select a source point and convex-hull residual internally. The budget
uses the dimension-zero correction; no maximizing coefficient is supplied. -/
theorem exists_affine_step_of_mem_convexHull_isPreconnected
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (source : Set E) (hsource : IsPreconnected source) (point : E)
    (hpoint : point ∈ convexHull ℝ source) (weight : ℝ)
    (hweight : 0 ≤ weight) (hweightLt : weight < 1)
    (hbudget : weight * (max 1 (Module.finrank ℝ E) : ℕ) ≤ 1) :
    ∃ current ∈ source, ∃ next ∈ convexHull ℝ source,
      point = weight • current + (1 - weight) • next := by
  classical
  obtain ⟨family, hfamily, hsubset, hmem, hcard⟩ :=
    exists_small_finset_of_mem_convexHull_isPreconnected source hsource point hpoint
  obtain ⟨coefficient, hnonneg, hsum, hvalue⟩ := Finset.mem_convexHull'.mp hmem
  obtain ⟨current, hcurrent, hmaximum⟩ := family.exists_max_image coefficient hfamily
  have hcardPos : 0 < (family.card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr hfamily
  have hcardReal : (family.card : ℝ) ≤ (max 1 (Module.finrank ℝ E) : ℕ) := by
    exact_mod_cast hcard
  have hsumMax : 1 ≤ (family.card : ℝ) * coefficient current := by
    calc
      1 = ∑ member ∈ family, coefficient member := hsum.symm
      _ ≤ ∑ _member ∈ family, coefficient current :=
        Finset.sum_le_sum (fun member hmember => hmaximum member hmember)
      _ = (family.card : ℝ) * coefficient current := by simp [mul_comm]
  have hbudgetFamily : weight * (family.card : ℝ) ≤ 1 :=
    (mul_le_mul_of_nonneg_left hcardReal hweight).trans hbudget
  have hcurrentWeight : weight ≤ coefficient current := by
    nlinarith
  have hdenomPos : 0 < 1 - weight := sub_pos.mpr hweightLt
  have hdenom : 1 - weight ≠ 0 := hdenomPos.ne'
  let remainder : E → ℝ := fun member =>
    (coefficient member - if member = current then weight else 0) / (1 - weight)
  have hremainderNonneg (member : E) (hmember : member ∈ family) :
      0 ≤ remainder member := by
    dsimp only [remainder]
    apply div_nonneg _ hdenomPos.le
    by_cases hequal : member = current
    · rw [ite_eq_left hequal, hequal]
      exact sub_nonneg.mpr hcurrentWeight
    · rw [ite_eq_right hequal, sub_zero]
      exact hnonneg member hmember
  have hremainderSum : ∑ member ∈ family, remainder member = 1 := by
    dsimp only [remainder]
    rw [← Finset.sum_div, Finset.sum_sub_distrib, hsum, Finset.sum_ite_eq',
      ite_eq_left hcurrent]
    exact div_self hdenom
  let next := ∑ member ∈ family, remainder member • member
  have hnext : next ∈ convexHull ℝ source := by
    apply convexHull_mono hsubset
    exact Finset.mem_convexHull'.mpr
      ⟨remainder, hremainderNonneg, hremainderSum, rfl⟩
  have hcancel (member : E) :
      (1 - weight) * remainder member =
        coefficient member - if member = current then weight else 0 := by
    dsimp only [remainder]
    exact mul_div_cancel₀ _ hdenom
  have hnextValue : (1 - weight) • next = point - weight • current := by
    dsimp only [next]
    simp_rw [Finset.smul_sum, smul_smul, hcancel, sub_smul, ite_smul, zero_smul]
    rw [Finset.sum_sub_distrib, hvalue]
    simp only [Finset.sum_ite_eq', hcurrent, ite_true]
  refine ⟨current, hsubset hcurrent, next, hnext, ?_⟩
  rw [hnextValue]
  abel

end Math.Topology
