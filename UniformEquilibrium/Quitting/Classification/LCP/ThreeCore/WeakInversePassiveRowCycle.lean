/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import MathUE.LinearProgramming.NonnegativeInverseApproximation
import UniformEquilibrium.Quitting.Classification.LCP.ThreeCore.StrictInversePassiveRowCycle
import UniformEquilibrium.Quitting.Terminal.TerminalExploitabilityRewardRobustness

/-!
# Weak inverse passive-row approximation

Only singleton columns owned by the three-player child are perturbed. Child
receivers see subtraction of the off-diagonal-ones matrix; outside receivers
see the same subtraction multiplied by their fixed nonnegative row weights.
Thus the parent row factorization survives exactly, and reward-table closure
returns a fixed uniform payoff for the original table.
-/

noncomputable section

namespace GameTheory

open QuittingLCPClassification Math.LinearProgramming Math.LinearAlgebra

namespace PassiveSingletonRowFactorization

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
variable {deleted : ι → Prop} [DecidablePred deleted]

local notation "Child" => {who : ι // ¬ deleted who}

/-- The coefficient of a child's singleton column at one parent coordinate. -/
def perturbCoefficient (rows : PassiveSingletonRowFactorization reward deleted)
    (terminal : {S : Finset ι // S.Nonempty}) (who : ι) : ℝ :=
  ∑ owner : Child,
    if terminal.1 = {owner.1} then
      if h : deleted who then
        ∑ inside : Child,
          rows.weight who inside * offDiagonalOnes Child inside owner
      else offDiagonalOnes Child ⟨who, h⟩ owner
    else 0

/-- Literal parent-table perturbation preserving every nonsingleton reward
and every singleton column whose owner is outside the child. -/
def perturb (rows : PassiveSingletonRowFactorization reward deleted)
    (epsilon : ℝ) : {S : Finset ι // S.Nonempty} → Payoff ι :=
  fun terminal who => reward terminal who -
    epsilon * rows.perturbCoefficient terminal who

private theorem singleton_sum
    (owner : Child) (f : Child → ℝ) :
    (∑ candidate : Child,
      if ({owner.1} : Finset ι) = {candidate.1} then f candidate else 0) =
        f owner := by
  rw [Finset.sum_eq_single owner]
  · simp
  · intro candidate _ hne
    have hsets : ({owner.1} : Finset ι) ≠ {candidate.1} := by
      intro heq
      apply hne
      exact Subtype.ext (by simpa only [Finset.singleton_inj] using heq.symm)
    simp [hsets]
  · simp

private theorem coefficient_singleton
    (rows : PassiveSingletonRowFactorization reward deleted)
    (owner : Child) (who : ι) :
    rows.perturbCoefficient (quittingSingletonTerminal owner.1) who =
      if h : deleted who then
        ∑ inside : Child,
          rows.weight who inside * offDiagonalOnes Child inside owner
      else offDiagonalOnes Child ⟨who, h⟩ owner := by
  unfold perturbCoefficient
  change (∑ candidate : Child,
      if ({owner.1} : Finset ι) = {candidate.1} then
        (if h : deleted who then
          ∑ inside : Child,
            rows.weight who inside * offDiagonalOnes Child inside candidate
        else offDiagonalOnes Child ⟨who, h⟩ candidate)
      else 0) = _
  exact singleton_sum owner _

private theorem coefficient_other
    (rows : PassiveSingletonRowFactorization reward deleted)
    (terminal : {S : Finset ι // S.Nonempty}) (who : ι)
    (hother : ∀ owner : Child, terminal.1 ≠ {owner.1}) :
    rows.perturbCoefficient terminal who = 0 := by
  unfold perturbCoefficient
  apply Finset.sum_eq_zero
  intro owner _
  simp [hother owner]

/-- The nearby table leaves all coalitions other than child singletons intact. -/
theorem perturb_other
    (rows : PassiveSingletonRowFactorization reward deleted)
    (epsilon : ℝ) (terminal : {S : Finset ι // S.Nonempty}) (who : ι)
    (hother : ∀ owner : Child, terminal.1 ≠ {owner.1}) :
    rows.perturb epsilon terminal who = reward terminal who := by
  simp [perturb, coefficient_other rows terminal who hother]

private theorem child_singleton
    (rows : PassiveSingletonRowFactorization reward deleted)
    (epsilon : ℝ) (owner who : Child) :
    quittingSoloReward (quittingDeleteReward (rows.perturb epsilon) deleted)
        owner who =
      quittingSoloReward (quittingDeleteReward reward deleted) owner who -
        epsilon * offDiagonalOnes Child who owner := by
  rw [show quittingSoloReward
      (quittingDeleteReward (rows.perturb epsilon) deleted) owner who =
      quittingSoloReward (rows.perturb epsilon) owner.1 who.1 from
        quittingDeleteReward_singletonTerminal (rows.perturb epsilon)
          deleted owner who]
  rw [show quittingSoloReward (quittingDeleteReward reward deleted) owner who =
      quittingSoloReward reward owner.1 who.1 from
        quittingDeleteReward_singletonTerminal reward deleted owner who]
  change reward (quittingSingletonTerminal owner.1) who.1 -
      epsilon * rows.perturbCoefficient (quittingSingletonTerminal owner.1) who.1 =
    reward (quittingSingletonTerminal owner.1) who.1 -
      epsilon * offDiagonalOnes Child who owner
  rw [coefficient_singleton]
  simp [who.2]

private theorem outside_singleton
    (rows : PassiveSingletonRowFactorization reward deleted)
    (epsilon : ℝ) (owner : Child) (outside : ι) (houtside : deleted outside) :
    quittingSoloReward (rows.perturb epsilon) owner.1 outside =
      quittingSoloReward reward owner.1 outside -
        epsilon *
          ∑ inside : Child,
            rows.weight outside inside * offDiagonalOnes Child inside owner := by
  change reward (quittingSingletonTerminal owner.1) outside -
      epsilon * rows.perturbCoefficient (quittingSingletonTerminal owner.1) outside =
    reward (quittingSingletonTerminal owner.1) outside -
      epsilon * ∑ inside : Child,
        rows.weight outside inside * offDiagonalOnes Child inside owner
  rw [coefficient_singleton]
  simp [houtside]

private theorem own_singleton
    (rows : PassiveSingletonRowFactorization reward deleted)
    (epsilon : ℝ) (who : ι) :
    quittingSoloReward (rows.perturb epsilon) who who =
      quittingSoloReward reward who who := by
  by_cases hdeleted : deleted who
  · apply rows.perturb_other epsilon (quittingSingletonTerminal who) who
    intro owner heq
    change ({who} : Finset ι) = {owner.1} at heq
    have hwho : who = owner.1 := by simpa only [Finset.singleton_inj] using heq
    exact owner.2 (hwho ▸ hdeleted)
  · let inside : Child := ⟨who, hdeleted⟩
    have hcoeff : rows.perturbCoefficient (quittingSingletonTerminal who) who = 0 := by
      simpa [inside, hdeleted, offDiagonalOnes] using
        rows.coefficient_singleton inside who
    change reward (quittingSingletonTerminal who) who -
      epsilon * rows.perturbCoefficient (quittingSingletonTerminal who) who =
        reward (quittingSingletonTerminal who) who
    rw [hcoeff]
    ring

/-- The child matrix is exactly the small off-diagonal perturbation. -/
theorem normalizedSoloMatrix_perturb
    (rows : PassiveSingletonRowFactorization reward deleted) (epsilon : ℝ) :
    Matrix.of (normalizedSoloMatrix (quittingDeleteReward (rows.perturb epsilon) deleted)) =
      Matrix.of (normalizedSoloMatrix (quittingDeleteReward reward deleted)) -
        epsilon • offDiagonalOnes Child := by
  funext who owner
  simp only [Matrix.of_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
  rw [normalizedSoloMatrix_eq_soloReward_sub,
    normalizedSoloMatrix_eq_soloReward_sub]
  rw [child_singleton rows epsilon owner who,
    child_singleton rows epsilon who who]
  simp [offDiagonalOnes]
  ring

/-- The same outside weights factor the perturbed singleton rows. -/
def perturbRows (rows : PassiveSingletonRowFactorization reward deleted)
    (epsilon : ℝ) :
    PassiveSingletonRowFactorization (rows.perturb epsilon) deleted := by
  refine {
    weight := rows.weight
    nonneg := rows.nonneg
    row := ?_ }
  intro outside houtside owner
  rw [outside_singleton rows epsilon owner outside houtside,
    own_singleton rows epsilon outside]
  simp only [child_singleton rows epsilon]
  have hbase := rows.row outside houtside owner
  simp_rw [mul_sub] at hbase
  rw [Finset.sum_sub_distrib] at hbase
  have hdiag (inside : Child) : offDiagonalOnes Child inside inside = 0 := by
    simp [offDiagonalOnes]
  simp only [hdiag, mul_zero, sub_zero]
  simp_rw [mul_sub]
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib]
  have hsum :
      (∑ inside : Child,
        rows.weight outside inside * (epsilon * offDiagonalOnes Child inside owner)) =
        epsilon * ∑ inside : Child,
          rows.weight outside inside * offDiagonalOnes Child inside owner := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro inside _
    ring
  rw [hsum]
  linear_combination hbase

/-- A finite coefficient bound controls every coordinate of the parent
perturbation, including signed arbitrary weights on unused child rows. -/
def coefficientBound (rows : PassiveSingletonRowFactorization reward deleted) : ℝ :=
  1 + ∑ terminal : {S : Finset ι // S.Nonempty},
    ∑ who : ι, |rows.perturbCoefficient terminal who|

theorem coefficientBound_pos
    (rows : PassiveSingletonRowFactorization reward deleted) :
    0 < rows.coefficientBound := by
  unfold coefficientBound
  positivity

private theorem abs_coefficient_le_bound
    (rows : PassiveSingletonRowFactorization reward deleted)
    (terminal : {S : Finset ι // S.Nonempty}) (who : ι) :
    |rows.perturbCoefficient terminal who| ≤ rows.coefficientBound := by
  have hinner : |rows.perturbCoefficient terminal who| ≤
      ∑ other : ι, |rows.perturbCoefficient terminal other| := by
    exact Finset.single_le_sum (s := Finset.univ)
      (fun other _ => abs_nonneg (rows.perturbCoefficient terminal other))
      (Finset.mem_univ who)
  have houter :
      (∑ other : ι, |rows.perturbCoefficient terminal other|) ≤
      ∑ term : {S : Finset ι // S.Nonempty},
        ∑ other : ι, |rows.perturbCoefficient term other| := by
    exact Finset.single_le_sum (s := Finset.univ)
      (fun term _ => Finset.sum_nonneg fun other _ =>
        abs_nonneg (rows.perturbCoefficient term other))
      (Finset.mem_univ terminal)
  unfold coefficientBound
  linarith

theorem abs_perturb_sub_le
    (rows : PassiveSingletonRowFactorization reward deleted)
    (epsilon : ℝ) (hepsilon : 0 ≤ epsilon)
    (terminal : {S : Finset ι // S.Nonempty}) (who : ι) :
    |rows.perturb epsilon terminal who - reward terminal who| ≤
      epsilon * rows.coefficientBound := by
  rw [perturb]
  have hbound := rows.abs_coefficient_le_bound terminal who
  calc
    |reward terminal who - epsilon * rows.perturbCoefficient terminal who -
        reward terminal who| = |-(epsilon * rows.perturbCoefficient terminal who)| := by
      congr 1
      ring
    _ = epsilon * |rows.perturbCoefficient terminal who| := by
      rw [abs_neg, abs_mul, abs_of_nonneg hepsilon]
    _ ≤ epsilon * rows.coefficientBound := mul_le_mul_of_nonneg_left hbound hepsilon

end PassiveSingletonRowFactorization

/-- An invertible three-player child matrix with nonnegative inverse, together
with nonnegative factorizations of all outside singleton rows, gives an
original-table uniform-equilibrium payoff. The target is selected after
passing through arbitrarily close literal reward tables. -/
theorem exists_uniformEquilibriumPayoff_of_nonnegativeInverse_passiveRows
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (deleted : ι → Prop) [DecidablePred deleted]
    (hcard : Fintype.card {who : ι // ¬ deleted who} = 3)
    (hdet : Matrix.det
      (Matrix.of (normalizedSoloMatrix (quittingDeleteReward reward deleted))) ≠ 0)
    (hinverse : ∀ row column : {who : ι // ¬ deleted who},
      0 ≤ (Matrix.of
        (normalizedSoloMatrix (quittingDeleteReward reward deleted)))⁻¹ row column)
    (rows : PassiveSingletonRowFactorization reward deleted) :
    ∃ target, (quittingGame reward).IsUniformEquilibriumPayoff none target := by
  let matrix : Matrix {who : ι // ¬ deleted who} {who : ι // ¬ deleted who} ℝ :=
    Matrix.of (normalizedSoloMatrix (quittingDeleteReward reward deleted))
  obtain ⟨threshold, hthreshold, hstrict⟩ :=
    exists_pos_strictlyPositiveInverse_sub_offDiagonalOnes matrix
      (by simp [hcard]) hdet hinverse
  apply exists_uniformEquilibriumPayoff_of_arbitrarily_close_reward_tables reward
  intro delta hdelta
  let cap := rows.coefficientBound
  have hcap : 0 < cap := rows.coefficientBound_pos
  let epsilon := min threshold (delta / cap) / 2
  have hratio : 0 < delta / cap := div_pos hdelta hcap
  have hmin : 0 < min threshold (delta / cap) := lt_min hthreshold hratio
  have hepsilon : 0 < epsilon := by
    dsimp [epsilon]
    linarith
  have hthreshold' : epsilon < threshold := by
    dsimp [epsilon]
    linarith [min_le_left threshold (delta / cap)]
  have hdelta' : epsilon * cap ≤ delta := by
    dsimp [epsilon]
    have hle := min_le_right threshold (delta / cap)
    have hmul := mul_le_mul_of_nonneg_right hle hcap.le
    have hcancel : delta / cap * cap = delta := by
      field_simp [hcap.ne']
    linarith
  let nearby := rows.perturb epsilon
  have hmatrix :
      Matrix.of (normalizedSoloMatrix (quittingDeleteReward nearby deleted)) =
      matrix - epsilon • offDiagonalOnes {who : ι // ¬ deleted who} := by
    exact rows.normalizedSoloMatrix_perturb epsilon
  have hpositive : HasStrictlyPositiveInverse
      (Matrix.of (normalizedSoloMatrix (quittingDeleteReward nearby deleted))) := by
    rw [hmatrix]
    exact (hstrict epsilon hepsilon hthreshold').1
  refine ⟨nearby, ?_, ?_⟩
  · intro terminal player
    exact (rows.abs_perturb_sub_le epsilon hepsilon.le terminal player).trans hdelta'
  · exact exists_uniformEquilibriumPayoff_of_strictInverse_passiveRows
      nearby deleted hcard hpositive (rows.perturbRows epsilon)

end GameTheory
