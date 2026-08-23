/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticForcedOwnerWallRectangleCurvature
import UniformEquilibrium.Quitting.Bellman.Finite.BooleanMobiusAdapter
import UniformEquilibrium.ProofView.Concepts.Potential.MixedPotential

/-!
# Pure-background decomposition of an owner/outsider square

The owner/outsider influence at an arbitrary product root is the expectation
of literal two-bit squares after every other action has been fixed.  Hence a
positive mixed square selects a positive pure-background square.  All other
players then enter the four displayed cells only through one background
coalition.

This is a local rank statement.  It does not merge the background players in
a new quitting game and does not control the infimum over profiles of such a
compiled game.
-/

noncomputable section

namespace GameTheory

open Math.Probability Math.PMFProduct

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Literal payoff square after all actions other than `owner` and `who` have
been fixed by `action`. -/
def quittingPureBackgroundOwnerOutsiderSquare
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : Payoff ι) (action : ι → Bool)
    (owner who : ι) : ℝ :=
  quittingRootPayoff reward tail
        (Function.update (Function.update action owner true) who true) who -
    quittingRootPayoff reward tail
        (Function.update (Function.update action owner true) who false) who -
    quittingRootPayoff reward tail
        (Function.update (Function.update action owner false) who true) who +
    quittingRootPayoff reward tail
        (Function.update (Function.update action owner false) who false) who

/-- A double pure update can be moved from the product distribution into the
integrand, in the same chronological order. -/
theorem quittingRootExpectedPayoff_doublePureUpdate_eq_expect_update
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : Payoff ι) (root : ι → PMF Bool)
    (owner who : ι) (ownerAction whoAction : Bool) :
    quittingRootExpectedPayoff reward tail
        (Function.update
          (Function.update root owner (PMF.pure ownerAction)) who
          (PMF.pure whoAction)) who =
      expect (pmfPi root) (fun action =>
        quittingRootPayoff reward tail
          (Function.update
            (Function.update action owner ownerAction) who whoAction) who) := by
  unfold quittingRootExpectedPayoff
  rw [KernelGame.expect_pmfPi_update_pure]
  rw [KernelGame.expect_pmfPi_update_pure]

/-- **Mixed square = average of pure-background squares.** -/
theorem quittingOwnerInfluence_eq_expect_pureBackgroundSquare
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : Payoff ι) (root : ι → PMF Bool)
    (owner who : ι) :
    quittingOwnerInfluenceOnEndpointDifference reward tail root owner who =
      expect (pmfPi root) (fun action =>
        quittingPureBackgroundOwnerOutsiderSquare
          reward tail action owner who) := by
  unfold quittingOwnerInfluenceOnEndpointDifference
    quittingRootEndpointDifference quittingRootQuitPayoff
    quittingRootContinuePayoff
  rw [quittingRootExpectedPayoff_doublePureUpdate_eq_expect_update,
    quittingRootExpectedPayoff_doublePureUpdate_eq_expect_update,
    quittingRootExpectedPayoff_doublePureUpdate_eq_expect_update,
    quittingRootExpectedPayoff_doublePureUpdate_eq_expect_update]
  rw [← expect_sub, ← expect_sub, ← expect_sub]
  apply congrArg (expect (pmfPi root))
  funext action
  unfold quittingPureBackgroundOwnerOutsiderSquare
  ring

/-- A positive mixed owner influence has a positive pure-background square
on an action profile with positive product probability. -/
theorem exists_positiveProbability_pureBackgroundSquare_of_influence_pos
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : Payoff ι) (root : ι → PMF Bool)
    (owner who : ι)
    (hpositive : 0 < quittingOwnerInfluenceOnEndpointDifference
      reward tail root owner who) :
    ∃ action : ι → Bool,
      0 < ((pmfPi root) action).toReal ∧
      0 < quittingPureBackgroundOwnerOutsiderSquare
        reward tail action owner who := by
  rw [quittingOwnerInfluence_eq_expect_pureBackgroundSquare
    reward tail root owner who, expect_eq_sum] at hpositive
  by_contra hnot
  push Not at hnot
  have hsumNonpos :
      (∑ action,
        ((pmfPi root) action).toReal *
          quittingPureBackgroundOwnerOutsiderSquare
            reward tail action owner who) ≤ 0 := by
    exact Finset.sum_nonpos fun action _ => by
      have hprob0 : 0 ≤ ((pmfPi root) action).toReal := ENNReal.toReal_nonneg
      by_cases hprob : 0 < ((pmfPi root) action).toReal
      · exact mul_nonpos_of_nonneg_of_nonpos hprob.le
          (hnot action hprob)
      · have hzero : ((pmfPi root) action).toReal = 0 :=
          le_antisymm (le_of_not_gt hprob) hprob0
        rw [hzero]
        simp
  exact (not_lt_of_ge hsumNonpos hpositive).elim

/-- A negative mixed owner influence has a negative pure-background square
on an action profile of positive product probability. -/
theorem exists_positiveProbability_pureBackgroundSquare_of_influence_neg
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : Payoff ι) (root : ι → PMF Bool)
    (owner who : ι)
    (hnegative : quittingOwnerInfluenceOnEndpointDifference
      reward tail root owner who < 0) :
    ∃ action : ι → Bool,
      0 < ((pmfPi root) action).toReal ∧
      quittingPureBackgroundOwnerOutsiderSquare
        reward tail action owner who < 0 := by
  rw [quittingOwnerInfluence_eq_expect_pureBackgroundSquare
    reward tail root owner who, expect_eq_sum] at hnegative
  by_contra hnot
  push Not at hnot
  have hsumNonneg : 0 ≤
      ∑ action,
        ((pmfPi root) action).toReal *
          quittingPureBackgroundOwnerOutsiderSquare
            reward tail action owner who := by
    exact Finset.sum_nonneg fun action _ => by
      have hprob0 : 0 ≤ ((pmfPi root) action).toReal := ENNReal.toReal_nonneg
      by_cases hprob : 0 < ((pmfPi root) action).toReal
      · exact mul_nonneg hprob.le (hnot action hprob)
      · have hzero : ((pmfPi root) action).toReal = 0 :=
          le_antisymm (le_of_not_gt hprob) hprob0
        rw [hzero]
        simp
  exact (not_lt_of_ge hsumNonneg hnegative).elim

/-- Oriented pure-background square: Quit witnesses use the ordinary square,
Continue witnesses use its negative. -/
def quittingOrientedPureBackgroundSquare
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : Payoff ι) (background : ι → Bool)
    (owner who : ι) (action : Bool) : ℝ :=
  if action then
    quittingPureBackgroundOwnerOutsiderSquare
      reward tail background owner who
  else
    -quittingPureBackgroundOwnerOutsiderSquare
      reward tail background owner who

/-- **A positive mixed rectangle selects a positive oriented pure-background
square.**  This is the local host selector for either Boolean orientation. -/
theorem exists_positiveProbability_orientedPureBackgroundSquare_of_rectangle_pos
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : Payoff ι) (root : ι → PMF Bool)
    (owner who : ι) (hne : owner ≠ who) (action : Bool)
    (hpositive : 0 < quittingOwnerOutsiderDeviationRectangle
      reward tail root owner who action) :
    ∃ background : ι → Bool,
      0 < ((pmfPi root) background).toReal ∧
      0 < quittingOrientedPureBackgroundSquare
        reward tail background owner who action := by
  have horientation := positive_quittingOwnerOutsiderDeviationRectangle_orientation
    reward tail root owner who hne action hpositive
  rcases horientation with ⟨haction, hinfluence⟩ |
      ⟨haction, hinfluence⟩
  · subst action
    obtain ⟨background, hprob, hsquare⟩ :=
      exists_positiveProbability_pureBackgroundSquare_of_influence_pos
        reward tail root owner who hinfluence
    exact ⟨background, hprob, by
      simpa [quittingOrientedPureBackgroundSquare] using hsquare⟩
  · subst action
    obtain ⟨background, hprob, hsquare⟩ :=
      exists_positiveProbability_pureBackgroundSquare_of_influence_neg
        reward tail root owner who hinfluence
    exact ⟨background, hprob, by
      unfold quittingOrientedPureBackgroundSquare
      simp only [Bool.false_eq_true, ↓reduceIte]
      linarith⟩

/-- Probability of the prescribed outsider action opposite the tested pure
endpoint. -/
def quittingOutsiderOppositeActionProbability
    (root : ι → PMF Bool) (who : ι) (action : Bool) : ℝ :=
  (root who (!action)).toReal

/-- **Exact oriented-background expansion of a rectangle.** -/
theorem quittingOwnerOutsiderDeviationRectangle_eq_oppositeProbability_mul_expect_orientedBackground
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : Payoff ι) (root : ι → PMF Bool)
    (owner who : ι) (hne : owner ≠ who) (action : Bool) :
    quittingOwnerOutsiderDeviationRectangle reward tail root owner who action =
      quittingOutsiderOppositeActionProbability root who action *
        expect (pmfPi root) (fun background =>
          quittingOrientedPureBackgroundSquare
            reward tail background owner who action) := by
  rw [quittingOwnerOutsiderDeviationRectangle_eq_polarity
    reward tail root owner who hne action]
  rw [quittingOwnerInfluence_eq_expect_pureBackgroundSquare
    reward tail root owner who]
  cases action with
  | false =>
      unfold quittingOutsiderOppositeActionProbability
        quittingOrientedPureBackgroundSquare
      simp only [Bool.not_false, Bool.false_eq_true, ↓reduceIte, expect_neg]
      ring
  | true =>
      unfold quittingOutsiderOppositeActionProbability
        quittingOrientedPureBackgroundSquare
      simp only [Bool.not_true, ↓reduceIte]

/-- Nonnegative contribution of one pure background to the oriented square
expansion. -/
def quittingPositiveOrientedBackgroundCharge
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : Payoff ι) (root : ι → PMF Bool)
    (owner who : ι) (action : Bool) (background : ι → Bool) : ℝ :=
  quittingOutsiderOppositeActionProbability root who action *
    ((pmfPi root) background).toReal *
      max (quittingOrientedPureBackgroundSquare
        reward tail background owner who action) 0

theorem quittingPositiveOrientedBackgroundCharge_nonneg
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : Payoff ι) (root : ι → PMF Bool)
    (owner who : ι) (action : Bool) (background : ι → Bool) :
    0 ≤ quittingPositiveOrientedBackgroundCharge
      reward tail root owner who action background := by
  exact mul_nonneg
    (mul_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg)
    (le_max_right _ 0)

/-- The positive part of a mixed rectangle is bounded by the sum of its
positive oriented pure-background charges.  This is the quantitative host
selector needed before finite-label extraction. -/
theorem max_rectangle_le_sum_positiveOrientedBackgroundCharge
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : Payoff ι) (root : ι → PMF Bool)
    (owner who : ι) (hne : owner ≠ who) (action : Bool) :
    max (quittingOwnerOutsiderDeviationRectangle
      reward tail root owner who action) 0 ≤
      ∑ background,
        quittingPositiveOrientedBackgroundCharge
          reward tail root owner who action background := by
  rw [quittingOwnerOutsiderDeviationRectangle_eq_oppositeProbability_mul_expect_orientedBackground
    reward tail root owner who hne action]
  rw [expect_eq_sum]
  let p := quittingOutsiderOppositeActionProbability root who action
  let f : (ι → Bool) → ℝ := fun background =>
    quittingOrientedPureBackgroundSquare
      reward tail background owner who action
  have hp0 : 0 ≤ p := ENNReal.toReal_nonneg
  have hsum : (∑ background,
      ((pmfPi root) background).toReal * f background) ≤
      ∑ background,
        ((pmfPi root) background).toReal * max (f background) 0 := by
    exact Finset.sum_le_sum fun background _ =>
      mul_le_mul_of_nonneg_left (le_max_left _ 0) ENNReal.toReal_nonneg
  have hscaled : p * (∑ background,
      ((pmfPi root) background).toReal * f background) ≤
      p * ∑ background,
        ((pmfPi root) background).toReal * max (f background) 0 :=
    mul_le_mul_of_nonneg_left hsum hp0
  have hrhs0 : 0 ≤ p * ∑ background,
      ((pmfPi root) background).toReal * max (f background) 0 :=
    mul_nonneg hp0 (Finset.sum_nonneg fun background _ =>
      mul_nonneg ENNReal.toReal_nonneg (le_max_right _ 0))
  change max (p * ∑ background,
      ((pmfPi root) background).toReal * f background) 0 ≤
    ∑ background,
      p * ((pmfPi root) background).toReal * max (f background) 0
  calc
    max (p * ∑ background,
        ((pmfPi root) background).toReal * f background) 0 ≤
      p * ∑ background,
        ((pmfPi root) background).toReal * max (f background) 0 :=
      max_le hscaled hrhs0
    _ = ∑ background,
        p * ((pmfPi root) background).toReal * max (f background) 0 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro background _
      ring

/-- Background coalition obtained after erasing the two displayed actions. -/
def quittingPureBackgroundCoalition
    (action : ι → Bool) (owner who : ι) : Finset ι :=
  quittingQuitters
    (Function.update (Function.update action owner false) who false)

theorem quittingPureBackgroundCoalition_not_mem_owner
    (action : ι → Bool) (owner who : ι) :
    owner ∉ quittingPureBackgroundCoalition action owner who := by
  by_cases h : owner = who
  · subst who
    simp [quittingPureBackgroundCoalition, quittingQuitters]
  · simp [quittingPureBackgroundCoalition, quittingQuitters, h]

theorem quittingPureBackgroundCoalition_not_mem_who
    (action : ι → Bool) (owner who : ι) :
    who ∉ quittingPureBackgroundCoalition action owner who := by
  simp [quittingPureBackgroundCoalition, quittingQuitters]

/-- **Four-cell host formula.**  A pure-background square depends on all
other players only through their one quitting coalition `T`. -/
theorem quittingPureBackgroundOwnerOutsiderSquare_eq_fourCells
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : Payoff ι) (action : ι → Bool)
    (owner who : ι) (hne : owner ≠ who) :
    let T := quittingPureBackgroundCoalition action owner who
    quittingPureBackgroundOwnerOutsiderSquare reward tail action owner who =
      quittingStageCoalitionPayoff reward tail (insert who (insert owner T)) who -
        quittingStageCoalitionPayoff reward tail (insert owner T) who -
        quittingStageCoalitionPayoff reward tail (insert who T) who +
        quittingStageCoalitionPayoff reward tail T who := by
  dsimp only
  unfold quittingPureBackgroundOwnerOutsiderSquare
  repeat' rw [quittingRootPayoff_eq_stageCoalitionPayoff]
  let T := quittingPureBackgroundCoalition action owner who
  have hTT : quittingQuitters
      (Function.update (Function.update action owner true) who true) =
      insert who (insert owner T) := by
    ext player
    by_cases hpOwner : player = owner
    · subst player
      simp [T, quittingPureBackgroundCoalition, quittingQuitters, hne]
    · by_cases hpWho : player = who
      · subst player
        simp [T, quittingPureBackgroundCoalition, quittingQuitters, hpOwner]
      · simp [T, quittingPureBackgroundCoalition, quittingQuitters,
          hpOwner, hpWho]
  have hTF : quittingQuitters
      (Function.update (Function.update action owner true) who false) =
      insert owner T := by
    ext player
    by_cases hpOwner : player = owner
    · subst player
      simp [T, quittingPureBackgroundCoalition, quittingQuitters, hne]
    · by_cases hpWho : player = who
      · subst player
        simp [T, quittingPureBackgroundCoalition, quittingQuitters, hpOwner]
      · simp [T, quittingPureBackgroundCoalition, quittingQuitters,
          hpOwner, hpWho]
  have hFT : quittingQuitters
      (Function.update (Function.update action owner false) who true) =
      insert who T := by
    ext player
    by_cases hpOwner : player = owner
    · subst player
      simp [T, quittingPureBackgroundCoalition, quittingQuitters, hne]
    · by_cases hpWho : player = who
      · subst player
        simp [T, quittingPureBackgroundCoalition, quittingQuitters]
      · simp [T, quittingPureBackgroundCoalition, quittingQuitters,
          hpOwner, hpWho]
  have hFF : quittingQuitters
      (Function.update (Function.update action owner false) who false) = T := by
    rfl
  rw [hTT, hTF, hFT, hFF]

end GameTheory
