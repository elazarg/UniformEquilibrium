/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Classification.PlayerDeletionLift
import UniformEquilibrium.Quitting.Cycles.BalancedSingletonCertificate

/-!
# Inheriting a balanced singleton cycle across passive rows

The input is a balanced cycle for the literal induced reward table and a
nonnegative factorization of each deleted player's singleton row. The output
is a certificate for the parent table, hence a parent uniform payoff. No
restriction is placed on rewards of nonsingleton quitting coalitions.
-/

noncomputable section

namespace GameTheory

open StochasticGame

namespace PassiveSingletonRowFactorization

private theorem child_solo_eq_parent
    {ι : Type} {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {deleted : ι → Prop} (owner who : {who : ι // ¬ deleted who}) :
    quittingSoloReward (quittingDeleteReward reward deleted) owner who =
      quittingSoloReward reward owner.1 who.1 := by
  exact quittingDeleteReward_singletonTerminal reward deleted owner who

end PassiveSingletonRowFactorization

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {L : ℕ}

/-- A deleted player's singleton differences factor through the surviving
players' singleton-difference matrix. The coefficients are not normalized. -/
structure PassiveSingletonRowFactorization
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (deleted : ι → Prop) [DecidablePred deleted] where
  weight : ι → {who : ι // ¬ deleted who} → ℝ
  nonneg : ∀ outside inside, deleted outside → 0 ≤ weight outside inside
  row : ∀ outside, deleted outside →
    ∀ owner : {who : ι // ¬ deleted who},
      quittingSoloReward reward owner.1 outside -
          quittingSoloReward reward outside outside =
        ∑ inside, weight outside inside *
          (quittingSoloReward (quittingDeleteReward reward deleted) owner inside -
            quittingSoloReward (quittingDeleteReward reward deleted) inside inside)

namespace PassiveSingletonRowFactorization

variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
variable {deleted : ι → Prop} [DecidablePred deleted]

/-- The parent phase value: child coordinates are inherited, while an
outside coordinate is its own singleton plus a weighted child surplus. -/
def coarse (rows : PassiveSingletonRowFactorization reward deleted)
    (child : BalancedSingletonCycleCertificate (L := L)
      (quittingDeleteReward reward deleted))
    (phase : Fin L) : Payoff ι := fun who =>
  if h : deleted who then
    quittingSoloReward reward who who +
      ∑ inside, rows.weight who inside *
        (child.coarse phase inside -
          quittingSoloReward (quittingDeleteReward reward deleted) inside inside)
  else child.coarse phase ⟨who, h⟩

/-- Lift the balanced child certificate to the literal parent reward table. -/
def certificate (rows : PassiveSingletonRowFactorization reward deleted)
    (child : BalancedSingletonCycleCertificate (L := L)
      (quittingDeleteReward reward deleted)) :
    BalancedSingletonCycleCertificate (L := L) reward := by
  let owner : Fin L → ι := fun phase => (child.owner phase).1
  let value := rows.coarse child
  refine {
    owner := owner
    hazard := child.hazard
    coarse := value
    initial := child.initial
    hazard_nonneg := child.hazard_nonneg
    hazard_lt_one := child.hazard_lt_one
    arc := ?_
    active := ?_
    soloFloor := ?_
    opponentDivergence := ?_ }
  · intro phase
    funext who
    by_cases hwho : deleted who
    · have hrow := rows.row who hwho (child.owner phase)
      have hchild (inside : {who : ι // ¬ deleted who}) :=
        congrFun (child.arc phase) inside
      have hsum :
          (∑ inside, rows.weight who inside *
            (child.coarse phase inside -
              quittingSoloReward (quittingDeleteReward reward deleted) inside inside)) =
          child.hazard phase *
            (∑ inside, rows.weight who inside *
              (quittingSoloReward (quittingDeleteReward reward deleted)
                  (child.owner phase) inside -
                quittingSoloReward (quittingDeleteReward reward deleted) inside inside)) +
          (1 - child.hazard phase) *
            (∑ inside, rows.weight who inside *
              (child.coarse (finRotate L phase) inside -
                quittingSoloReward (quittingDeleteReward reward deleted) inside inside)) := by
        rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro inside _
        rw [show child.coarse phase inside =
          child.hazard phase *
              quittingSoloReward (quittingDeleteReward reward deleted)
                (child.owner phase) inside +
            (1 - child.hazard phase) *
              child.coarse (finRotate L phase) inside from hchild inside]
        ring
      simp only [value, coarse, owner, quittingSingletonArcPayoff]
      simp only [dite_eq_left hwho]
      rw [hsum]
      rw [← hrow]
      ring
    · let inside : {who : ι // ¬ deleted who} := ⟨who, hwho⟩
      have hchild := congrFun (child.arc phase) inside
      change child.coarse phase inside =
          child.hazard phase *
              quittingSoloReward (quittingDeleteReward reward deleted)
                (child.owner phase) inside +
            (1 - child.hazard phase) * child.coarse (finRotate L phase) inside
        at hchild
      rw [child_solo_eq_parent] at hchild
      simpa [value, coarse, owner, hwho, inside, quittingSingletonArcPayoff]
        using hchild
  · intro phase
    have howner : ¬ deleted (owner phase) := (child.owner phase).2
    simpa [value, coarse, owner, howner, child_solo_eq_parent] using child.active phase
  · intro phase who
    by_cases hwho : deleted who
    · have hsum : 0 ≤
          ∑ inside, rows.weight who inside *
            (child.coarse phase inside -
              quittingSoloReward (quittingDeleteReward reward deleted) inside inside) := by
        apply Finset.sum_nonneg
        intro inside _
        exact mul_nonneg (rows.nonneg who inside hwho)
          (sub_nonneg.mpr (child.soloFloor phase inside))
      simpa [value, coarse, hwho] using hsum
    · let inside : {who : ι // ¬ deleted who} := ⟨who, hwho⟩
      have hfloor := child.soloFloor phase inside
      rw [child_solo_eq_parent] at hfloor
      simpa [value, coarse, hwho, inside] using hfloor
  · intro who
    by_cases hwho : deleted who
    · obtain ⟨phase, _, hpositive⟩ :=
        child.opponentDivergence (child.owner child.initial)
      exact ⟨phase, by
        intro heq
        have hnot : ¬ deleted who := by
          rw [heq]
          exact (child.owner phase).2
        exact hnot hwho, hpositive⟩
    · obtain ⟨phase, hne, hpositive⟩ := child.opponentDivergence ⟨who, hwho⟩
      exact ⟨phase, by
        intro heq
        apply hne
        exact Subtype.ext heq, hpositive⟩

/-- The fixed parent target supplied by the inherited cycle. -/
theorem isUniformEquilibriumPayoff
    (rows : PassiveSingletonRowFactorization reward deleted)
    (child : BalancedSingletonCycleCertificate (L := L)
      (quittingDeleteReward reward deleted)) :
    (quittingGame reward).IsUniformEquilibriumPayoff none
      (rows.coarse child child.initial) := by
  exact (rows.certificate child).isUniformEquilibriumPayoff

end PassiveSingletonRowFactorization
end GameTheory
