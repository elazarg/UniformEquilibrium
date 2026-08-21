import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import MathUE.Probability
import MathUE.SimplexApproximation

/-!
# Uniform empirical approximation of a finite convex hull

A point in the convex hull of finitely many vectors can be approximated, at
every sufficiently large denominator, by an equal-weight average of those
vectors.  The denominator threshold is uniform over the whole convex hull.
-/

noncomputable section

open scoped BigOperators
open Filter Topology

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

/-! ## One coherent infinite empirical schedule -/

/-- Choose a coordinate whose next-step target count is still ahead of its
actual count.  Under probability-weight and total-count hypotheses such a
coordinate always exists; the fallback only makes the definition total. -/
noncomputable def balancedChoice (weight : κ → ℝ)
    (count : κ → ℕ) (step : ℕ) : κ :=
  if h : ∃ k, (count k : ℝ) < (step + 1 : ℕ) * weight k then
    Classical.choose h
  else
    Classical.arbitrary κ

/-- Prefix counts generated by weighted round-robin allocation. -/
noncomputable def balancedCounts (weight : κ → ℝ) : ℕ → κ → ℕ
  | 0 => fun _ => 0
  | step + 1 =>
      let selected := balancedChoice weight (balancedCounts weight step) step
      fun k => balancedCounts weight step k + if k = selected then 1 else 0

/-- The coordinate selected at the next step of weighted round-robin. -/
noncomputable def balancedSample (weight : κ → ℝ) (step : ℕ) : κ :=
  balancedChoice weight (balancedCounts weight step) step

@[simp] theorem sum_balancedCounts (weight : κ → ℝ) (step : ℕ) :
    ∑ k, balancedCounts weight step k = step := by
  classical
  induction step with
  | zero => simp [balancedCounts]
  | succ step ih =>
      rw [balancedCounts]
      simp only [Finset.sum_add_distrib, ih]
      simp

theorem balancedChoice_spec {weight : κ → ℝ}
    (_hweight0 : ∀ k, 0 ≤ weight k) (hweightSum : ∑ k, weight k = 1)
    (step : ℕ) :
    (balancedCounts weight step (balancedSample weight step) : ℝ) <
      (step + 1 : ℕ) * weight (balancedSample weight step) := by
  classical
  have hex : ∃ k,
      (balancedCounts weight step k : ℝ) <
        (step + 1 : ℕ) * weight k := by
    by_contra hnot
    push Not at hnot
    have hsum := Finset.sum_le_sum fun k (_hk : k ∈ Finset.univ) => hnot k
    have hcountCast :
        ∑ k, (balancedCounts weight step k : ℝ) = step := by
      exact_mod_cast sum_balancedCounts weight step
    rw [← Finset.mul_sum, hweightSum, mul_one, hcountCast] at hsum
    norm_num at hsum
  unfold balancedSample balancedChoice
  rw [dif_pos hex]
  exact Classical.choose_spec hex

/-- Every weighted round-robin count stays less than one above its real-valued
target count. -/
theorem balancedCounts_sub_target_lt_one {weight : κ → ℝ}
    (hweight0 : ∀ k, 0 ≤ weight k) (hweightSum : ∑ k, weight k = 1)
    (step : ℕ) (k : κ) :
    (balancedCounts weight step k : ℝ) - step * weight k < 1 := by
  classical
  induction step with
  | zero => simp [balancedCounts]
  | succ step ih =>
      rw [balancedCounts]
      by_cases hk : k = balancedSample weight step
      · subst k
        have hsame : balancedSample weight step =
            balancedChoice weight (balancedCounts weight step) step := rfl
        dsimp only
        rw [hsame, if_pos rfl]
        norm_num only [Nat.cast_add, Nat.cast_one]
        have hselected := balancedChoice_spec hweight0 hweightSum step
        rw [hsame, Nat.cast_add, Nat.cast_one] at hselected
        linarith
      · have hk' : k ≠
            balancedChoice weight (balancedCounts weight step) step := by
          simpa only [balancedSample] using hk
        dsimp only
        rw [if_neg hk']
        norm_num only [add_zero, Nat.cast_add, Nat.cast_one]
        have hw := hweight0 k
        nlinarith

/-- Weighted round-robin has discrepancy at most the number of coordinates. -/
theorem abs_balancedCounts_sub_target_le_card {weight : κ → ℝ}
    (hweight0 : ∀ k, 0 ≤ weight k) (hweightSum : ∑ k, weight k = 1)
    (step : ℕ) (k : κ) :
    |(balancedCounts weight step k : ℝ) - step * weight k| ≤
      Fintype.card κ := by
  classical
  let error : κ → ℝ := fun j =>
    (balancedCounts weight step j : ℝ) - step * weight j
  have herrorSum : ∑ j, error j = 0 := by
    dsimp only [error]
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, hweightSum, mul_one]
    have hcountCast :
        ∑ j, (balancedCounts weight step j : ℝ) = step := by
      exact_mod_cast sum_balancedCounts weight step
    rw [hcountCast]
    simp
  have hothers : ∑ j ∈ (Finset.univ.erase k), error j ≤
      Fintype.card κ := by
    calc
      ∑ j ∈ (Finset.univ.erase k), error j ≤
          ∑ _j ∈ (Finset.univ.erase k), (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro j _hj
        exact (balancedCounts_sub_target_lt_one
          hweight0 hweightSum step j).le
      _ = ((Finset.univ.erase k).card : ℝ) := by simp
      _ ≤ Fintype.card κ := by
        exact_mod_cast Finset.card_le_univ (Finset.univ.erase k)
  have hsplit : ∑ j ∈ (Finset.univ.erase k), error j + error k = 0 := by
    rw [Finset.sum_erase_add _ _ (Finset.mem_univ k)]
    exact herrorSum
  have hlower : -(Fintype.card κ : ℝ) ≤ error k := by
    linarith
  have hcardOne : (1 : ℝ) ≤ Fintype.card κ := by
    exact_mod_cast Fintype.card_pos_iff.mpr (inferInstance : Nonempty κ)
  have hupper : error k ≤ Fintype.card κ :=
    (balancedCounts_sub_target_lt_one
      hweight0 hweightSum step k).le.trans hcardOne
  exact abs_le.mpr ⟨hlower, hupper⟩

/-- Prefix sums of the selected sequence are exactly the count-weighted sums. -/
theorem sum_range_balancedSample (weight : κ → ℝ)
    (point : κ → V) (step : ℕ) :
    ∑ time ∈ Finset.range step, point (balancedSample weight time) =
      ∑ k, (balancedCounts weight step k : ℝ) • point k := by
  classical
  induction step with
  | zero => simp [balancedCounts]
  | succ step ih =>
      rw [Finset.sum_range_succ, ih, balancedCounts]
      simp only [Nat.cast_add, Nat.cast_ite, Nat.cast_one, Nat.cast_zero,
        add_smul, Finset.sum_add_distrib]
      congr 1
      simp [balancedSample]

/-- Every point of a finite convex hull is the limit of the prefix averages of
one coherent infinite sequence of generating points. -/
theorem exists_sequence_tendsto_average_of_mem_convexHull_range
    (point : κ → V) {x : V}
    (hx : x ∈ convexHull ℝ (Set.range point)) :
    ∃ sample : ℕ → κ,
      Tendsto (fun step : ℕ =>
        ((step + 1 : ℕ) : ℝ)⁻¹ •
          ∑ time ∈ Finset.range (step + 1), point (sample time))
        atTop (nhds x) := by
  classical
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
  obtain ⟨bound, hboundAbs⟩ := Math.Probability.exists_abs_bound_of_finite
    (fun k ↦ ‖point k‖)
  have hbound : ∀ k, ‖point k‖ ≤ bound := by
    intro k
    simpa [abs_of_nonneg (norm_nonneg _)] using hboundAbs k
  have hbound0 : 0 ≤ bound :=
    (norm_nonneg (point (Classical.arbitrary κ))).trans (hbound _)
  let sample := balancedSample weight
  refine ⟨sample, Metric.tendsto_atTop.mpr ?_⟩
  intro ε hε
  let errorBudget : ℝ :=
    (Fintype.card κ : ℝ) * ((Fintype.card κ : ℝ) * bound)
  obtain ⟨threshold, hthreshold⟩ := exists_nat_gt (errorBudget / ε)
  refine ⟨threshold, fun step hstep ↦ ?_⟩
  let n := step + 1
  have hnpos : 0 < n := by omega
  have hbudgetLt : errorBudget < (n : ℝ) * ε := by
    have hthresholdStep : (threshold : ℝ) ≤ step := by exact_mod_cast hstep
    have hratio : errorBudget / ε < (step : ℝ) :=
      hthreshold.trans_le hthresholdStep
    have hratioN : errorBudget / ε < (n : ℝ) := by
      exact hratio.trans_le (by exact_mod_cast (Nat.le_succ step))
    exact (div_lt_iff₀ hε).1 hratioN
  rw [dist_eq_norm]
  have herrorIdentity :
      (n : ℝ)⁻¹ •
          ∑ time ∈ Finset.range n, point (sample time) - x =
        (n : ℝ)⁻¹ • ∑ k,
          ((balancedCounts weight n k : ℝ) - (n : ℝ) * weight k) •
            point k := by
    rw [show (∑ time ∈ Finset.range n, point (sample time)) =
        ∑ k, (balancedCounts weight n k : ℝ) • point k by
      exact sum_range_balancedSample weight point n]
    rw [← hweightedSum]
    have hnne : (n : ℝ) ≠ 0 := by positivity
    rw [Finset.smul_sum, Finset.smul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro k _
    rw [smul_smul, smul_smul, ← sub_smul]
    congr 1
    field_simp
  rw [herrorIdentity, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (inv_nonneg.mpr (Nat.cast_nonneg n))]
  have hsumBound :
      ‖∑ k, ((balancedCounts weight n k : ℝ) -
          (n : ℝ) * weight k) • point k‖ ≤ errorBudget := by
    calc
      ‖∑ k, ((balancedCounts weight n k : ℝ) -
          (n : ℝ) * weight k) • point k‖ ≤
          ∑ k, ‖((balancedCounts weight n k : ℝ) -
            (n : ℝ) * weight k) • point k‖ := norm_sum_le _ _
      _ ≤ ∑ _k : κ, (Fintype.card κ : ℝ) * bound := by
        apply Finset.sum_le_sum
        intro k _
        rw [norm_smul, Real.norm_eq_abs]
        exact mul_le_mul
          (abs_balancedCounts_sub_target_le_card
            hweight0 hweightSum n k)
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
