import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Finset.Max
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Capped finite simplex reduction to ordered pairs

For any finite family and cap between one half and one, a nonpositive
capped-simplex average exists exactly when one ordered two-coordinate
average is nonpositive.  Existence of the capped weights itself rules out
empty and singleton index types.
-/

namespace Math

open Finset

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A capped probability average is nonpositive iff a distinct ordered pair
has a nonpositive average with the full cap on its first coordinate. -/
theorem exists_cappedWeight_weightedSum_nonpositive_iff_exists_pair
    (a : ι → ℝ) (beta : ℝ)
    (hhalf : (1 : ℝ) / 2 ≤ beta) (hlt : beta < 1) :
    (∃ weight : ι → ℝ,
      (∀ index, 0 ≤ weight index) ∧
      (∑ index, weight index = 1) ∧
      (∀ index, weight index ≤ beta) ∧
      ∑ index, weight index * a index ≤ 0) ↔
      ∃ first second : ι, first ≠ second ∧
        beta * a first + (1 - beta) * a second ≤ 0 := by
  constructor
  · rintro ⟨weight, hnonnegative, hsum, hcapped, hweighted⟩
    have hexists : ∃ index, weight index ≠ 0 := by
      by_contra hnone
      have hzero : ∀ index, weight index = 0 := by
        intro index
        by_contra hne
        exact hnone ⟨index, hne⟩
      have hsumZero : ∑ index, weight index = 0 := by
        exact Finset.sum_eq_zero fun index _ => hzero index
      linarith
    letI : Nonempty ι := ⟨hexists.choose⟩
    obtain ⟨first, -, hfirst⟩ :=
      Finset.exists_min_image (Finset.univ : Finset ι) a Finset.univ_nonempty
    have hotherExists : ∃ other, other ≠ first := by
      by_contra hnone
      have hall : ∀ index, index = first := by
        intro index
        by_contra hne
        exact hnone ⟨index, hne⟩
      have hsumSingle : ∑ index, weight index = weight first := by
        apply Finset.sum_eq_single first
        · intro index _ hne
          exact (hne (hall index)).elim
        · simp
      have hweightFirst : weight first = 1 := by
        linarith
      exact (not_le_of_gt hlt) (hweightFirst ▸ hcapped first)
    obtain ⟨other, hother⟩ := hotherExists
    have herase : (Finset.univ.erase first).Nonempty :=
      ⟨other, Finset.mem_erase.mpr ⟨hother, Finset.mem_univ other⟩⟩
    obtain ⟨second, hsecondMem, hsecond⟩ :=
      Finset.exists_min_image (Finset.univ.erase first) a herase
    have hne : first ≠ second := Ne.symm (Finset.mem_erase.mp hsecondMem).1
    have hsumErase : ∑ index ∈ Finset.univ.erase first, weight index =
        1 - weight first := by
      have hdecompose := Finset.sum_erase_add _ weight (Finset.mem_univ first)
      rw [hsum] at hdecompose
      linarith
    have hlower :
        weight first * a first + (1 - weight first) * a second ≤
          ∑ index, weight index * a index := by
      have houtside :
          ∑ index ∈ Finset.univ.erase first, weight index * a second ≤
            ∑ index ∈ Finset.univ.erase first, weight index * a index := by
        apply Finset.sum_le_sum
        intro index hindex
        exact mul_le_mul_of_nonneg_left (hsecond index hindex)
          (hnonnegative index)
      have hweightedDecompose := Finset.sum_erase_add _
        (fun index => weight index * a index) (Finset.mem_univ first)
      rw [← Finset.sum_mul, hsumErase] at houtside
      linarith
    have hfirstSecond : a first ≤ a second :=
      hfirst second (Finset.mem_univ second)
    have hcapLower :
        beta * a first + (1 - beta) * a second ≤
          weight first * a first + (1 - weight first) * a second := by
      have hproduct :
          0 ≤ (beta - weight first) * (a second - a first) :=
        mul_nonneg (sub_nonneg.mpr (hcapped first))
          (sub_nonneg.mpr hfirstSecond)
      nlinarith
    exact ⟨first, second, hne, hcapLower.trans (hlower.trans hweighted)⟩
  · rintro ⟨first, second, hne, hpair⟩
    let weight : ι → ℝ := fun index =>
      (Pi.single first beta : ι → ℝ) index +
        (Pi.single second (1 - beta) : ι → ℝ) index
    refine ⟨weight, ?_, ?_, ?_, ?_⟩
    · intro index
      by_cases hfirst : index = first
      · subst index
        simp [weight, hne]
        linarith
      · by_cases hsecond : index = second
        · subst index
          simp [weight, hfirst]
          linarith
        · simp [weight, hfirst, hsecond]
    · simp only [weight, Finset.sum_add_distrib, Finset.sum_pi_single',
        Finset.mem_univ, if_true]
      ring
    · intro index
      by_cases hfirst : index = first
      · subst index
        simp [weight, hne]
      · by_cases hsecond : index = second
        · subst index
          simp [weight, hfirst]
          linarith
        · simp [weight, hfirst, hsecond]
          exact le_trans (by linarith : 0 ≤ (1 : ℝ) / 2) hhalf
    · simp_rw [weight, add_mul]
      simp only [Finset.sum_add_distrib, Pi.single_apply, ite_mul, zero_mul,
        Finset.sum_ite_eq', Finset.mem_univ, if_true]
      exact hpair

end Math
