/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors.
-/

import MathUE.Interval.RationalMaxExpression

/-!
# Executable rational lower-bound box certificates

A problem consists of equality expressions, required-nonnegative expressions,
an objective, and a rational root box.  A finite tree repeatedly bisects one
coordinate.  Every leaf names one exact reason: an equality interval omits
zero, a required-nonnegative interval is strictly negative, or the objective
interval is above the requested lower bound.

The checker is executable and uses rational arithmetic only.  Its soundness
theorem is independent of any subdivision-completeness or search-generator
claim.
-/

namespace Math
namespace Interval

/-- A rational coordinate box. -/
abbrev RationalBox (variableCount : ℕ) :=
  Fin variableCount → RationalInterval

namespace RationalBox

variable {variableCount : ℕ}

/-- Real point membership in a rational box. -/
def Contains (box : RationalBox variableCount)
    (point : Fin variableCount → ℝ) : Prop :=
  ∀ index, (box index).Contains (point index)

/-- Replace one coordinate interval. -/
def update (box : RationalBox variableCount) (coordinate : Fin variableCount)
    (interval : RationalInterval) : RationalBox variableCount :=
  Function.update box coordinate interval

/-- Closed left child of a rational split. -/
def left (box : RationalBox variableCount) (coordinate : Fin variableCount)
    (cut : ℚ) : RationalBox variableCount :=
  box.update coordinate ⟨(box coordinate).lower, cut⟩

/-- Closed right child of a rational split. -/
def right (box : RationalBox variableCount) (coordinate : Fin variableCount)
    (cut : ℚ) : RationalBox variableCount :=
  box.update coordinate ⟨cut, (box coordinate).upper⟩

/-- The closed children cover their parent. -/
theorem contains_left_or_right
    (box : RationalBox variableCount) (coordinate : Fin variableCount)
    (cut : ℚ) (point : Fin variableCount → ℝ)
    (hpoint : box.Contains point) :
    (box.left coordinate cut).Contains point ∨
      (box.right coordinate cut).Contains point := by
  rcases le_total (point coordinate) (cut : ℝ) with hleft | hright
  · left
    intro index
    by_cases hindex : index = coordinate
    · subst index
      rw [left, update, Function.update_self]
      exact ⟨(hpoint coordinate).1, hleft⟩
    · simpa [left, update, hindex] using hpoint index
  · right
    intro index
    by_cases hindex : index = coordinate
    · subst index
      rw [right, update, Function.update_self]
      exact ⟨hright, (hpoint coordinate).2⟩
    · simpa [right, update, hindex] using hpoint index

end RationalBox

/-- A finite exact-rational lower-bound problem. -/
structure RationalLowerBoxProblem
    (variableCount equalityCount inequalityCount : ℕ) where
  root : RationalBox variableCount
  equality : Fin equalityCount → RationalMaxExpression variableCount
  nonnegative : Fin inequalityCount → RationalMaxExpression variableCount
  objective : RationalMaxExpression variableCount

namespace RationalLowerBoxProblem

variable {variableCount equalityCount inequalityCount : ℕ}

/-- Real feasibility of one assignment. -/
def Feasible
    (problem : RationalLowerBoxProblem variableCount equalityCount
      inequalityCount)
    (point : Fin variableCount → ℝ) : Prop :=
  problem.root.Contains point ∧
    (∀ index, RationalMaxExpression.evalReal point
      (problem.equality index) = 0) ∧
    ∀ index, 0 ≤ RationalMaxExpression.evalReal point
      (problem.nonnegative index)

end RationalLowerBoxProblem

/-- Exact reason carried by one closed leaf. -/
inductive RationalLowerLeafReason (equalityCount inequalityCount : ℕ) where
  | equalitySeparated (index : Fin equalityCount)
  | nonnegativeSeparated (index : Fin inequalityCount)
  | objectiveLowerBound
deriving DecidableEq, Repr

/-- A finite split tree.  Child boxes are reconstructed from the root and
split path, so a certificate cannot substitute unrelated leaf boxes. -/
inductive RationalLowerBoxTree
    (variableCount equalityCount inequalityCount : ℕ) where
  | leaf (reason : RationalLowerLeafReason equalityCount inequalityCount)
  | split (coordinate : Fin variableCount) (cut : ℚ)
      (left right : RationalLowerBoxTree variableCount equalityCount
        inequalityCount)
deriving DecidableEq, Repr

namespace RationalLowerBoxProblem

variable {variableCount equalityCount inequalityCount : ℕ}

/-- Exact checker for one leaf reason. -/
def verifyLeaf
    (problem : RationalLowerBoxProblem variableCount equalityCount
      inequalityCount)
    (gamma : ℚ) (box : RationalBox variableCount) :
    RationalLowerLeafReason equalityCount inequalityCount → Bool
  | .equalitySeparated index =>
      let enclosure := RationalMaxExpression.evalInterval box
        (problem.equality index)
      decide (enclosure.upper < 0 ∨ 0 < enclosure.lower)
  | .nonnegativeSeparated index =>
      let enclosure := RationalMaxExpression.evalInterval box
        (problem.nonnegative index)
      decide (enclosure.upper < 0)
  | .objectiveLowerBound =>
      let enclosure := RationalMaxExpression.evalInterval box
        problem.objective
      decide (gamma ≤ enclosure.lower)

/-- Executable recursive certificate verifier.  Strict interior cuts keep
accepted trees suitable for the normalized-longest-side generator as well as
for soundness. -/
def verifyTree
    (problem : RationalLowerBoxProblem variableCount equalityCount
      inequalityCount)
    (gamma : ℚ) : RationalBox variableCount →
      RationalLowerBoxTree variableCount equalityCount inequalityCount → Bool
  | box, .leaf reason => problem.verifyLeaf gamma box reason
  | box, .split coordinate cut left right =>
      decide ((box coordinate).lower < cut ∧ cut < (box coordinate).upper) &&
        problem.verifyTree gamma (box.left coordinate cut) left &&
        problem.verifyTree gamma (box.right coordinate cut) right

/-- Public whole-certificate checker. -/
def verifies
    (problem : RationalLowerBoxProblem variableCount equalityCount
      inequalityCount)
    (gamma : ℚ)
    (tree : RationalLowerBoxTree variableCount equalityCount
      inequalityCount) : Bool :=
  problem.verifyTree gamma problem.root tree

/-- A checked leaf either excludes every feasible assignment in its box or
proves the requested objective lower bound there. -/
theorem verifyLeaf_sound
    (problem : RationalLowerBoxProblem variableCount equalityCount
      inequalityCount)
    (gamma : ℚ) (box : RationalBox variableCount)
    (reason : RationalLowerLeafReason equalityCount inequalityCount)
    (hverify : problem.verifyLeaf gamma box reason = true)
    (point : Fin variableCount → ℝ) (hpoint : box.Contains point)
    (hequality : ∀ index, RationalMaxExpression.evalReal point
      (problem.equality index) = 0)
    (hnonnegative : ∀ index, 0 ≤ RationalMaxExpression.evalReal point
      (problem.nonnegative index)) :
    (gamma : ℝ) ≤ RationalMaxExpression.evalReal point problem.objective := by
  cases reason with
  | equalitySeparated index =>
      simp only [verifyLeaf, decide_eq_true_eq] at hverify
      have henclosure := RationalMaxExpression.evalInterval_sound
        (problem.equality index) box point hpoint
      rw [hequality index] at henclosure
      rcases hverify with hupper | hlower
      · exact False.elim (not_lt_of_ge henclosure.2 (by exact_mod_cast hupper))
      · exact False.elim (not_lt_of_ge henclosure.1 (by exact_mod_cast hlower))
  | nonnegativeSeparated index =>
      simp only [verifyLeaf, decide_eq_true_eq] at hverify
      have henclosure := RationalMaxExpression.evalInterval_sound
        (problem.nonnegative index) box point hpoint
      have hnegative : RationalMaxExpression.evalReal point
          (problem.nonnegative index) < 0 :=
        lt_of_le_of_lt henclosure.2 (by exact_mod_cast hverify)
      exact False.elim (not_lt_of_ge (hnonnegative index) hnegative)
  | objectiveLowerBound =>
      simp only [verifyLeaf, decide_eq_true_eq] at hverify
      have henclosure := RationalMaxExpression.evalInterval_sound
        problem.objective box point hpoint
      have hgamma : (gamma : ℝ) ≤
          (RationalMaxExpression.evalInterval box problem.objective).lower := by
        exact_mod_cast hverify
      exact hgamma.trans henclosure.1

/-- Induction over an accepted finite tree proves its global lower bound. -/
theorem verifyTree_sound
    (problem : RationalLowerBoxProblem variableCount equalityCount
      inequalityCount)
    (gamma : ℚ)
    (tree : RationalLowerBoxTree variableCount equalityCount inequalityCount)
    (box : RationalBox variableCount)
    (hverify : problem.verifyTree gamma box tree = true)
    (point : Fin variableCount → ℝ) (hpoint : box.Contains point)
    (hequality : ∀ index, RationalMaxExpression.evalReal point
      (problem.equality index) = 0)
    (hnonnegative : ∀ index, 0 ≤ RationalMaxExpression.evalReal point
      (problem.nonnegative index)) :
    (gamma : ℝ) ≤ RationalMaxExpression.evalReal point problem.objective := by
  induction tree generalizing box with
  | leaf reason =>
      exact problem.verifyLeaf_sound gamma box reason hverify point hpoint
        hequality hnonnegative
  | split coordinate cut left right hleft hright =>
      have hparts :
          (((box coordinate).lower < cut ∧ cut < (box coordinate).upper) ∧
            problem.verifyTree gamma (box.left coordinate cut) left = true) ∧
            problem.verifyTree gamma (box.right coordinate cut) right = true := by
        simpa only [verifyTree, Bool.and_eq_true, decide_eq_true_eq] using hverify
      obtain ⟨⟨_hcut, hleftVerify⟩, hrightVerify⟩ := hparts
      rcases box.contains_left_or_right coordinate cut point hpoint with
          hpointLeft | hpointRight
      · exact hleft (box.left coordinate cut) hleftVerify hpointLeft
      · exact hright (box.right coordinate cut) hrightVerify hpointRight

/-- Soundness of the public executable checker. -/
theorem verifies_sound
    (problem : RationalLowerBoxProblem variableCount equalityCount
      inequalityCount)
    (gamma : ℚ)
    (tree : RationalLowerBoxTree variableCount equalityCount inequalityCount)
    (hverify : problem.verifies gamma tree = true)
    (point : Fin variableCount → ℝ) (hpoint : problem.Feasible point) :
    (gamma : ℝ) ≤ RationalMaxExpression.evalReal point problem.objective := by
  exact problem.verifyTree_sound gamma tree problem.root hverify point hpoint.1
    hpoint.2.1 hpoint.2.2

end RationalLowerBoxProblem

end Interval
end Math
