/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Approximate witness switching for a four-corner supremum envelope

For four payoff families indexed by the same deviation type, a pointwise
mixed-difference bound controls the mixed difference of their suprema unless
an approximately optimal witness switches corners.  The statements use
explicit `sSup` values and approximate witnesses, so no supremum attainment is
assumed.  The finite-mixture lemma is only an algebraic extraction result; it
does not assert a behavioral-to-pure decomposition.
-/

noncomputable section

open scoped BigOperators

namespace Math.Optimization

variable {D : Type*}

/-- Mixed difference of the four supremum-envelope values. -/
def supMixedDifference
    (f₀ f₁ f₂ f₁₂ : D → ℝ) : ℝ :=
  sSup (Set.range f₁₂) - sSup (Set.range f₁) -
    sSup (Set.range f₂) + sSup (Set.range f₀)

/-- The regret of a witness at the base corner. -/
def baseRegret (f₀ : D → ℝ) (d : D) : ℝ :=
  sSup (Set.range f₀) - f₀ d

/-- The regret at corner `2` of a witness selected at corner `1`. -/
def oppositeRegret₂ (f₂ : D → ℝ) (d : D) : ℝ :=
  sSup (Set.range f₂) - f₂ d

/-- The regret at corner `1` of a witness selected at corner `2`. -/
def oppositeRegret₁ (f₁ : D → ℝ) (d : D) : ℝ :=
  sSup (Set.range f₁) - f₁ d

/-- Positive upper-to-base witness switching, with an unattained supremum
allowed. -/
theorem upperToBase_regret_ge_supMixedDifference_sub
    (f₀ f₁ f₂ f₁₂ : D → ℝ)
    (h₁ : BddAbove (Set.range f₁))
    (h₂ : BddAbove (Set.range f₂))
    (q eta : ℝ) (d : D)
    (hface : ∀ d,
      |f₁₂ d - f₁ d - f₂ d + f₀ d| ≤ q)
    (hupper : sSup (Set.range f₁₂) - eta ≤ f₁₂ d) :
    supMixedDifference f₀ f₁ f₂ f₁₂ - (q + eta) ≤
      baseRegret f₀ d := by
  have hf₁ : f₁ d ≤ sSup (Set.range f₁) :=
    le_csSup h₁ ⟨d, rfl⟩
  have hf₂ : f₂ d ≤ sSup (Set.range f₂) :=
    le_csSup h₂ ⟨d, rfl⟩
  have hcurvature :
      f₁₂ d - f₁ d - f₂ d + f₀ d ≤ q := by
    exact (le_abs_self _).trans (hface d)
  dsimp [supMixedDifference, baseRegret]
  linarith

/-- Negative side-to-opposite-side witness switching from corner `1` to
corner `2`, with an unattained supremum allowed. -/
theorem sideOneToSideTwo_regret_ge_neg_supMixedDifference_sub
    (f₀ f₁ f₂ f₁₂ : D → ℝ)
    (h₀ : BddAbove (Set.range f₀))
    (h₁₂ : BddAbove (Set.range f₁₂))
    (q eta : ℝ) (d : D)
    (hface : ∀ d,
      |f₁₂ d - f₁ d - f₂ d + f₀ d| ≤ q)
    (hside : sSup (Set.range f₁) - eta ≤ f₁ d) :
    -supMixedDifference f₀ f₁ f₂ f₁₂ - (q + eta) ≤
      oppositeRegret₂ f₂ d := by
  have hf₀ : f₀ d ≤ sSup (Set.range f₀) :=
    le_csSup h₀ ⟨d, rfl⟩
  have hf₁₂ : f₁₂ d ≤ sSup (Set.range f₁₂) :=
    le_csSup h₁₂ ⟨d, rfl⟩
  have hcurvature :
      -q ≤ f₁₂ d - f₁ d - f₂ d + f₀ d := by
    exact neg_le_of_abs_le (hface d)
  dsimp [supMixedDifference, oppositeRegret₂]
  linarith

/-- Negative side-to-opposite-side witness switching from corner `2` to
corner `1`, with an unattained supremum allowed. -/
theorem sideTwoToSideOne_regret_ge_neg_supMixedDifference_sub
    (f₀ f₁ f₂ f₁₂ : D → ℝ)
    (h₀ : BddAbove (Set.range f₀))
    (h₁₂ : BddAbove (Set.range f₁₂))
    (q eta : ℝ) (d : D)
    (hface : ∀ d,
      |f₁₂ d - f₁ d - f₂ d + f₀ d| ≤ q)
    (hside : sSup (Set.range f₂) - eta ≤ f₂ d) :
    -supMixedDifference f₀ f₁ f₂ f₁₂ - (q + eta) ≤
      oppositeRegret₁ f₁ d := by
  have hf₀ : f₀ d ≤ sSup (Set.range f₀) :=
    le_csSup h₀ ⟨d, rfl⟩
  have hf₁₂ : f₁₂ d ≤ sSup (Set.range f₁₂) :=
    le_csSup h₁₂ ⟨d, rfl⟩
  have hcurvature :
      -q ≤ f₁₂ d - f₁ d - f₂ d + f₀ d := by
    exact neg_le_of_abs_le (hface d)
  dsimp [supMixedDifference, oppositeRegret₁]
  linarith

/-- Pointwise mixed curvature of a debt difference is the envelope curvature
minus the prescribed-payoff curvature. -/
theorem debtMixedDifference_eq_envelope_sub_prescribed
    (envelope prescribed : D → ℝ)
    (base one two both : D) :
    ((envelope both - prescribed both) -
        (envelope one - prescribed one) -
        (envelope two - prescribed two) +
        (envelope base - prescribed base)) =
      (envelope both - envelope one - envelope two + envelope base) -
        (prescribed both - prescribed one - prescribed two + prescribed base) := by
  ring

/-- A positive weighted average of oriented regrets contains a positive
oriented pure component. -/
theorem exists_pos_regret_difference_of_weighted_pos
    {ι : Type*} [Fintype ι]
    (weight source target : ι → ℝ)
    (hweight : ∀ i, 0 ≤ weight i)
    (hpositive : 0 < ∑ i, weight i * (source i - target i)) :
    ∃ i, 0 < source i - target i := by
  by_contra hnone
  push Not at hnone
  have hsum : ∑ i, weight i * (source i - target i) ≤ 0 := by
    apply Finset.sum_nonpos
    intro i hi
    exact mul_nonpos_of_nonneg_of_nonpos (hweight i) (hnone i)
  linarith

end Math.Optimization
