import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.Normed.Module.Basic
import MathUE.SimplexApproximation

/-!
# Uniform empirical approximation of a finite convex hull

A point in the convex hull of finitely many vectors can be approximated, at
every sufficiently large denominator, by an equal-weight average of those
vectors.  The denominator threshold is uniform over the whole convex hull.
-/

noncomputable section

open scoped BigOperators

namespace MathUE

variable {V κ : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [Fintype κ] [DecidableEq κ] [Nonempty κ]

/-- Every point of a finite convex hull has an empirical approximation at each
sufficiently large denominator.  The threshold depends only on the number and
uniform norm bound of the generating vectors, not on the point. -/
theorem exists_uniformAverage_close_of_mem_convexHull_range
    (point : κ → V) {bound ε : ℝ}
    (hbound : ∀ k, ‖point k‖ ≤ bound) (hbound0 : 0 ≤ bound) (hε : 0 < ε) :
    ∃ n₀ : ℕ, 0 < n₀ ∧ ∀ n, n₀ ≤ n →
      ∀ x ∈ convexHull ℝ (Set.range point),
        ∃ sample : Fin n → κ,
          ‖(n : ℝ)⁻¹ • ∑ j, point (sample j) - x‖ < ε := by
  classical
  let errorBudget : ℝ :=
    (Fintype.card κ : ℝ) * ((Fintype.card κ : ℝ) * bound)
  have herrorBudget : 0 ≤ errorBudget := by
    dsimp only [errorBudget]
    positivity
  obtain ⟨n₀, hn₀⟩ := exists_nat_gt (max (errorBudget / ε) 0)
  have hn₀pos : 0 < n₀ := by
    have : (0 : ℝ) < n₀ := (le_max_right _ _).trans_lt hn₀
    exact_mod_cast this
  refine ⟨n₀, hn₀pos, ?_⟩
  intro n hn x hx
  have hnpos : 0 < n := hn₀pos.trans_le hn
  have hbudgetLt : errorBudget < (n : ℝ) * ε := by
    have hratio : errorBudget / ε < (n₀ : ℝ) :=
      (le_max_left _ _).trans_lt hn₀
    have hn₀n : (n₀ : ℝ) ≤ n := by exact_mod_cast hn
    exact ((div_lt_iff₀ hε).1 hratio).trans_le
      (mul_le_mul_of_nonneg_right hn₀n hε.le)
  rw [convexHull_range_eq_exists_affineCombination] at hx
  rcases hx with ⟨support, weight₀, hweight₀0, hweight₀sum, hweighted⟩
  let weight : κ → ℝ := fun k => if k ∈ support then weight₀ k else 0
  have hweight0 : ∀ k, 0 ≤ weight k := by
    intro k
    by_cases hk : k ∈ support
    · simpa [weight, hk] using hweight₀0 k hk
    · simp [weight, hk]
  have hweightSum : ∑ k, weight k = 1 := by
    simpa [weight] using hweight₀sum
  have hweightedSum : ∑ k, weight k • point k = x := by
    rw [← hweighted,
      support.affineCombination_eq_linear_combination point weight₀ hweight₀sum]
    simp [weight]
  let base : κ := Classical.arbitrary κ
  let count : κ → ℕ :=
    Math.SimplexApproximation.residualFloorCounts base weight n
  have hcountSum : ∑ k, count k = n := by
    exact Math.SimplexApproximation.sum_residualFloorCounts
      base hweight0 hweightSum n
  let expanded := Sigma fun k => Fin (count k)
  have hcard : Fintype.card expanded = n := by
    dsimp only [expanded]
    rw [Fintype.card_sigma]
    simpa using hcountSum
  let equivalence : expanded ≃ Fin n :=
    (Fintype.equivFin expanded).trans (finCongr hcard)
  let sample : Fin n → κ := fun j => (equivalence.symm j).1
  refine ⟨sample, ?_⟩
  have hsampleSum : ∑ j, point (sample j) =
      ∑ k, (count k : ℝ) • point k := by
    rw [show (∑ j, point (sample j)) =
        ∑ a : expanded, point a.1 by
      exact (Fintype.sum_equiv equivalence
        (fun a : expanded => point a.1)
        (fun j : Fin n => point (sample j))
        (fun a => by simp [sample])).symm]
    rw [Fintype.sum_sigma]
    apply Finset.sum_congr rfl
    intro k _
    simp [Nat.cast_smul_eq_nsmul]
  have herrorIdentity :
      (n : ℝ)⁻¹ • ∑ j, point (sample j) - x =
        (n : ℝ)⁻¹ •
          ∑ k, ((count k : ℝ) - (n : ℝ) * weight k) • point k := by
    rw [hsampleSum, ← hweightedSum]
    have hnne : (n : ℝ) ≠ 0 := by positivity
    rw [Finset.smul_sum, Finset.smul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro k _
    rw [smul_smul, smul_smul]
    rw [← sub_smul]
    congr 1
    field_simp
  rw [herrorIdentity, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (inv_nonneg.mpr (Nat.cast_nonneg n))]
  have hsumBound :
      ‖∑ k, ((count k : ℝ) - (n : ℝ) * weight k) • point k‖ ≤
        errorBudget := by
    calc
      ‖∑ k, ((count k : ℝ) - (n : ℝ) * weight k) • point k‖ ≤
          ∑ k, ‖((count k : ℝ) - (n : ℝ) * weight k) • point k‖ :=
        norm_sum_le _ _
      _ ≤ ∑ _k : κ, (Fintype.card κ : ℝ) * bound := by
        apply Finset.sum_le_sum
        intro k _
        rw [norm_smul, Real.norm_eq_abs]
        exact mul_le_mul
          (Math.SimplexApproximation.residualFloorCounts_abs_error_le_card
            base hweight0 hweightSum n k)
          (hbound k) (norm_nonneg _) (Nat.cast_nonneg _)
      _ = errorBudget := by
        simp [errorBudget, Finset.sum_const, nsmul_eq_mul]
  have hscaled : (n : ℝ)⁻¹ * errorBudget < ε := by
    have hnreal : 0 < (n : ℝ) := by exact_mod_cast hnpos
    have := mul_lt_mul_of_pos_left hbudgetLt (inv_pos.mpr hnreal)
    calc
      (n : ℝ)⁻¹ * errorBudget < (n : ℝ)⁻¹ * ((n : ℝ) * ε) := this
      _ = ε := by rw [← mul_assoc, inv_mul_cancel₀ (ne_of_gt hnreal), one_mul]
  exact (mul_le_mul_of_nonneg_left hsumBound
    (inv_nonneg.mpr (Nat.cast_nonneg n))).trans_lt hscaled

end MathUE
