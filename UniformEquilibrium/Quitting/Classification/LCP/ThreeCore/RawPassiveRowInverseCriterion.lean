/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Classification.LCP.ThreeCore.WeakInversePassiveRowCycle

/-!
# Raw inverse-weight criterion for passive singleton rows

The row convention is receiver first and singleton owner second. For each
outside receiver `k`, its difference row is multiplied on the right by the
inverse of the induced child matrix. Nonnegativity of those literal weights
provides the passive-row factorization required by the checked cycle lift.
-/

noncomputable section

namespace GameTheory.PassiveRowInverseCriterion

open QuittingLCPClassification Math.LinearProgramming

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
variable (deleted : ι → Prop) [DecidablePred deleted]

local notation "Child" => {who : ι // ¬ deleted who}

/-- The literal selected singleton-difference matrix `T = Γ_SS`. -/
def childMatrix : Matrix Child Child ℝ :=
  Matrix.of (normalizedSoloMatrix (quittingDeleteReward reward deleted))

/-- The literal outside difference row `Γ_kS`. -/
def outsideRow (outside : ι) : Child → ℝ := fun owner =>
  quittingSoloReward reward owner.1 outside -
    quittingSoloReward reward outside outside

/-- The packet's weights `Γ_kS T⁻¹`, without a simplex normalization. -/
def inverseWeight (outside : ι) : Child → ℝ :=
  Matrix.vecMul (outsideRow reward deleted outside) (childMatrix reward deleted)⁻¹

/-- Matrix invertibility makes the inverse weights factor the original
outside singleton row through the child matrix. -/
def factorization
    (hdet : (childMatrix reward deleted).det ≠ 0)
    (hweight : ∀ outside, deleted outside →
      ∀ inside : Child, 0 ≤ inverseWeight reward deleted outside inside) :
    PassiveSingletonRowFactorization reward deleted := by
  have hunit : IsUnit (childMatrix reward deleted).det :=
    isUnit_iff_ne_zero.mpr hdet
  refine {
    weight := inverseWeight reward deleted
    nonneg := fun outside inside houtside => hweight outside houtside inside
    row := ?_ }
  intro outside _ owner
  have hcomp : Matrix.vecMul
      (inverseWeight reward deleted outside) (childMatrix reward deleted) =
        outsideRow reward deleted outside := by
    unfold inverseWeight
    rw [Matrix.vecMul_vecMul,
      Matrix.nonsing_inv_mul (childMatrix reward deleted) hunit,
      Matrix.vecMul_one]
  have hentry := congrFun hcomp owner
  rw [Matrix.vecMul_apply_eq_sum] at hentry
  change outsideRow reward deleted outside owner =
    ∑ inside : Child, inverseWeight reward deleted outside inside *
      (quittingSoloReward (quittingDeleteReward reward deleted) owner inside -
        quittingSoloReward (quittingDeleteReward reward deleted) inside inside)
  simpa only [childMatrix, Matrix.of_apply,
    normalizedSoloMatrix_eq_soloReward_sub] using hentry.symm

/-- The strict raw inverse and outside-row tests retain the selected labeling,
the actual right-cycle data and the canonical ambient phase-zero payoff.
Outside weights are the literal computed inverse weights, not supplied rows. -/
theorem exists_labeledCycle_uniformPayoff_of_raw_strictInverse_triple
    (hcard : Fintype.card Child = 3)
    (hpositive : HasStrictlyPositiveInverse (childMatrix reward deleted))
    (houtside : ∀ outside, deleted outside →
      ∀ inside : Child, 0 ≤ inverseWeight reward deleted outside inside) :
    ∃ label : Child ≃ Fin 3,
      ∃ cycle : RightSingletonCycle
          (quittingRewardReindex label (quittingDeleteReward reward deleted)),
        let rows := factorization reward deleted hpositive.1 houtside
        let child := RightSingletonCycle.toBalancedCertificate_reindex
          (quittingDeleteReward reward deleted) label cycle
        let certificate := rows.certificate child
        (quittingGame reward).IsUniformEquilibriumPayoff none (certificate.coarse 0) := by
  exact exists_labeledCycle_uniformPayoff_of_strictInverse_passiveRows
    reward deleted hcard hpositive
      (factorization reward deleted hpositive.1 houtside)

/-- The packet's literal inverse test, with a selected three-player child,
gives a fixed uniform-equilibrium payoff for the original parent game. -/
theorem exists_uniformEquilibriumPayoff_of_raw_nonnegativeInverse_triple
    (hcard : Fintype.card Child = 3)
    (hdet : (childMatrix reward deleted).det ≠ 0)
    (hinverse : ∀ row column : Child,
      0 ≤ (childMatrix reward deleted)⁻¹ row column)
    (houtside : ∀ outside, deleted outside →
      ∀ inside : Child, 0 ≤ inverseWeight reward deleted outside inside) :
    ∃ target, (quittingGame reward).IsUniformEquilibriumPayoff none target := by
  exact exists_uniformEquilibriumPayoff_of_nonnegativeInverse_passiveRows
    reward deleted hcard hdet hinverse
      (factorization reward deleted hdet houtside)

/-- If the parent game has no uniform-equilibrium payoff, then a selected
three-player child's literal raw inverse test must fail. -/
theorem raw_inverse_test_failure_of_no_uniformEquilibriumPayoff
    (hcard : Fintype.card Child = 3)
    (hno : ¬ ∃ target,
      (quittingGame reward).IsUniformEquilibriumPayoff none target) :
    (childMatrix reward deleted).det = 0 ∨
      (∃ row column : Child,
        (childMatrix reward deleted)⁻¹ row column < 0) ∨
      (∃ outside, deleted outside ∧ ∃ inside : Child,
        inverseWeight reward deleted outside inside < 0) := by
  by_cases hdet : (childMatrix reward deleted).det = 0
  · exact Or.inl hdet
  · right
    by_cases hinverse : ∀ row column : Child,
        0 ≤ (childMatrix reward deleted)⁻¹ row column
    · right
      by_cases houtside : ∀ outside, deleted outside →
          ∀ inside : Child, 0 ≤ inverseWeight reward deleted outside inside
      · exact False.elim (hno
          (exists_uniformEquilibriumPayoff_of_raw_nonnegativeInverse_triple
            reward deleted hcard hdet hinverse houtside))
      · push Not at houtside
        exact houtside
    · push Not at hinverse
      obtain ⟨row, column, hnegative⟩ := hinverse
      exact Or.inl ⟨row, column, hnegative⟩

end GameTheory.PassiveRowInverseCriterion
