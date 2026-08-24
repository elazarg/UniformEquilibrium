/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.Option
import Mathlib.Tactic

/-!
# Finite affine interval feasibility

A finite family of affine rows on the unit interval is simultaneously
nonpositive exactly when every row is nonpositive at at least one endpoint
and every lower-bound row is compatible with every upper-bound row.  The
criterion contains only signs and cross-products; in particular it removes
the quantified real parameter without division in the final proposition.
-/

noncomputable section

namespace Math

variable {κ : Type*} [Fintype κ]

/-- A common point of the unit interval makes every affine endpoint row
nonpositive. -/
def IsFiniteAffineIntervalFeasible (lower upper : κ → ℝ) : Prop :=
  ∃ weight : ℝ, 0 ≤ weight ∧ weight ≤ 1 ∧
    ∀ index,
      (1 - weight) * lower index + weight * upper index ≤ 0

/-- The division-free sign and cross-product test for a common feasible
point of a finite family of affine endpoint rows. -/
def FiniteAffineIntervalCriterion (lower upper : κ → ℝ) : Prop :=
  (∀ index, lower index ≤ 0 ∨ upper index ≤ 0) ∧
    ∀ lowerIndex upperIndex,
      0 < lower lowerIndex → upper lowerIndex ≤ 0 →
      lower upperIndex ≤ 0 → 0 < upper upperIndex →
      lower lowerIndex * upper upperIndex ≤
        upper lowerIndex * lower upperIndex

/-- **Finite affine interval feasibility.**  A common legal affine weight
exists exactly when the endpoint signs and every lower--upper cross-product
are compatible. -/
theorem finiteAffineIntervalFeasible_iff
    (lower upper : κ → ℝ) :
    IsFiniteAffineIntervalFeasible lower upper ↔
      FiniteAffineIntervalCriterion lower upper := by
  classical
  constructor
  · rintro ⟨weight, hweight0, hweight1, hrows⟩
    refine ⟨?_, ?_⟩
    · intro index
      by_contra hnone
      push Not at hnone
      have hleft0 : 0 ≤ (1 - weight) * lower index :=
        mul_nonneg (by linarith) hnone.1.le
      rcases hweight0.eq_or_lt with hzero | hweightPos
      · subst weight
        exact (not_le_of_gt hnone.1) (by simpa using hrows index)
      · have hrightPos : 0 < weight * upper index :=
          mul_pos hweightPos hnone.2
        linarith [hrows index]
    · intro lowerIndex upperIndex hlowerPos hlowerUpper
        hupperLower hupperPos
      have hlowerRow := hrows lowerIndex
      have hupperRow := hrows upperIndex
      have hlowerDen : 0 < lower lowerIndex - upper lowerIndex := by
        linarith
      have hupperDen : 0 < upper upperIndex - lower upperIndex := by
        linarith
      have hlowerBound : lower lowerIndex ≤
          weight * (lower lowerIndex - upper lowerIndex) := by
        nlinarith [hlowerRow]
      have hupperBound : weight *
          (upper upperIndex - lower upperIndex) ≤ -lower upperIndex := by
        nlinarith [hupperRow]
      have hscaledLower :=
        mul_le_mul_of_nonneg_right hlowerBound hupperDen.le
      have hscaledUpper :=
        mul_le_mul_of_nonneg_right hupperBound hlowerDen.le
      nlinarith [hscaledLower, hscaledUpper]
  · rintro ⟨hendpoint, hcross⟩
    let candidate : Option κ → ℝ
      | none => 0
      | some index =>
          if 0 < lower index then
            lower index / (lower index - upper index)
          else 0
    let weight : ℝ :=
      Finset.univ.sup' Finset.univ_nonempty candidate
    have hweight0 : 0 ≤ weight := by
      dsimp only [weight]
      have h := Finset.le_sup' candidate
        (Finset.mem_univ (none : Option κ))
      simpa [candidate] using h
    have hweight1 : weight ≤ 1 := by
      dsimp only [weight]
      apply Finset.sup'_le
      intro index _hindex
      rcases index with _ | index
      · simp [candidate]
      · by_cases hlowerPos : 0 < lower index
        · have hupperNonpos : upper index ≤ 0 :=
            (hendpoint index).resolve_left (not_le.mpr hlowerPos)
          have hden : 0 < lower index - upper index := by linarith
          simp only [candidate, hlowerPos, ↓reduceIte]
          rw [div_le_iff₀ hden]
          linarith
        · simp [candidate, hlowerPos]
    refine ⟨weight, hweight0, hweight1, ?_⟩
    intro index
    by_cases hlowerPos : 0 < lower index
    · have hupperNonpos : upper index ≤ 0 :=
        (hendpoint index).resolve_left (not_le.mpr hlowerPos)
      have hden : 0 < lower index - upper index := by linarith
      have hlowerBound :
          lower index / (lower index - upper index) ≤ weight := by
        dsimp only [weight]
        have h := Finset.le_sup' candidate
          (Finset.mem_univ (some index))
        simpa [candidate, hlowerPos] using h
      have hscaled := mul_le_mul_of_nonneg_right hlowerBound hden.le
      have hcancel :
          lower index / (lower index - upper index) *
              (lower index - upper index) = lower index := by
        field_simp
      rw [hcancel] at hscaled
      nlinarith
    · have hlowerNonpos : lower index ≤ 0 := le_of_not_gt hlowerPos
      by_cases hupperPos : 0 < upper index
      · have hupperDen : 0 < upper index - lower index := by linarith
        have hupperBound : weight ≤
            -lower index / (upper index - lower index) := by
          dsimp only [weight]
          apply Finset.sup'_le
          intro candidateIndex _hindex
          rcases candidateIndex with _ | lowerIndex
          · exact div_nonneg (neg_nonneg.mpr hlowerNonpos) hupperDen.le
          · by_cases hcLowerPos : 0 < lower lowerIndex
            · have hcUpperNonpos : upper lowerIndex ≤ 0 :=
                (hendpoint lowerIndex).resolve_left
                  (not_le.mpr hcLowerPos)
              have hcDen : 0 < lower lowerIndex - upper lowerIndex := by
                linarith
              have hpair := hcross lowerIndex index hcLowerPos
                hcUpperNonpos hlowerNonpos hupperPos
              simp only [candidate, hcLowerPos, ↓reduceIte]
              rw [div_le_div_iff₀ hcDen hupperDen]
              nlinarith [hpair]
            · simp only [candidate, hcLowerPos, ↓reduceIte]
              exact div_nonneg (neg_nonneg.mpr hlowerNonpos) hupperDen.le
        have hscaled :=
          mul_le_mul_of_nonneg_right hupperBound hupperDen.le
        have hcancel :
            (-lower index / (upper index - lower index)) *
                (upper index - lower index) = -lower index := by
          field_simp
        rw [hcancel] at hscaled
        nlinarith
      · have hupperNonpos : upper index ≤ 0 := le_of_not_gt hupperPos
        exact add_nonpos
          (mul_nonpos_of_nonneg_of_nonpos (by linarith) hlowerNonpos)
          (mul_nonpos_of_nonneg_of_nonpos hweight0 hupperNonpos)

end Math
