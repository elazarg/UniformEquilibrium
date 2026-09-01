/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Root.SuccessorCertificate

/-!
# Bounded one-root endpoint estimates

This module owns the source-independent reward-box estimates for a product
root.  It contains no marked player, chronology, absorption path, or Nash
hypothesis.
-/

noncomputable section

namespace GameTheory

open StochasticGame Math.Probability Math.PMFProduct

variable {ι : Type} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
/-- The one-stage absorbing contribution is bounded by the reward bound times
the probability of absorption. -/
theorem abs_quittingRootAbsorbingContribution_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool) (who : ι) (M : ℝ)
    (hreward : ∀ S player, |reward S player| ≤ M) :
    |quittingRootAbsorbingContribution reward root who| ≤
      M * quittingRootAbsorptionMass root := by
  let absorbingBound : (ι → Bool) → ℝ := fun action ↦
    if (quittingQuitters action).Nonempty then M else 0
  have hpointUpper (action : ι → Bool) :
      quittingRootPayoff reward (0 : Payoff ι) action who ≤
        absorbingBound action := by
    by_cases hquit : (quittingQuitters action).Nonempty
    · have h := hreward ⟨quittingQuitters action, hquit⟩ who
      simp only [quittingRootPayoff, dif_pos hquit, absorbingBound,
        if_pos hquit]
      exact (le_abs_self _).trans h
    · simp only [quittingRootPayoff, dif_neg hquit, Pi.zero_apply,
        absorbingBound, if_neg hquit]
      norm_num
  have hpointLower (action : ι → Bool) :
      -absorbingBound action ≤
        quittingRootPayoff reward (0 : Payoff ι) action who := by
    by_cases hquit : (quittingQuitters action).Nonempty
    · have h := hreward ⟨quittingQuitters action, hquit⟩ who
      simp only [quittingRootPayoff, dif_pos hquit, absorbingBound,
        if_pos hquit]
      exact neg_le_of_abs_le h
    · simp only [quittingRootPayoff, dif_neg hquit, Pi.zero_apply,
        absorbingBound, if_neg hquit]
      norm_num
  have hupper :
      quittingRootAbsorbingContribution reward root who ≤
        expect (pmfPi root) absorbingBound := by
    unfold quittingRootAbsorbingContribution quittingRootExpectedPayoff
    exact expect_mono _ _ _ hpointUpper
  have hlower :
      -expect (pmfPi root) absorbingBound ≤
        quittingRootAbsorbingContribution reward root who := by
    have hmono := expect_mono (pmfPi root)
      (fun action ↦ -absorbingBound action)
      (fun action ↦ quittingRootPayoff reward (0 : Payoff ι) action who)
      hpointLower
    have hneg :
        expect (pmfPi root) (fun action ↦ -absorbingBound action) =
          -expect (pmfPi root) absorbingBound := by
      rw [show (fun action ↦ -absorbingBound action) =
          fun action ↦ (-1 : ℝ) * absorbingBound action by
        funext action
        ring,
        expect_const_mul]
      ring
    rw [hneg] at hmono
    exact hmono
  have hboundExpectation :
      expect (pmfPi root) absorbingBound =
        M * quittingRootAbsorptionMass root := by
    unfold absorbingBound
    rw [show (fun action : ι → Bool ↦
        if (quittingQuitters action).Nonempty then M else 0) =
        fun action ↦ M *
          (if (quittingQuitters action).Nonempty then (1 : ℝ) else 0) by
      funext action
      split <;> simp_all]
    rw [expect_const_mul,
      expect_quittingNonemptyIndicator_eq_absorptionMass]
  rw [hboundExpectation] at hupper hlower
  exact (abs_le).2 ⟨hlower, hupper⟩

omit [DecidableEq ι] in
/-- A bounded Bellman edge moves each payoff coordinate by at most twice the
reward bound times its one-stage absorption mass. -/
theorem abs_quittingRootSuccessorPayoff_sub_tail_le_two_mul_absorptionMass
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : Payoff ι) (root : ι → PMF Bool) (who : ι) (M : ℝ)
    (hreward : ∀ S player, |reward S player| ≤ M)
    (htail : |tail who| ≤ M) :
    |quittingRootSuccessorPayoff reward tail root who - tail who| ≤
      2 * M * quittingRootAbsorptionMass root := by
  rw [quittingRootSuccessorPayoff_sub_tail]
  have habsorbing :=
    abs_quittingRootAbsorbingContribution_le reward root who M hreward
  have hp0 : 0 ≤ quittingRootAbsorptionMass root := by
    unfold quittingRootAbsorptionMass
    linarith [quittingStationaryContinueMass_le_one root]
  calc
    |quittingRootAbsorbingContribution reward root who -
        quittingRootAbsorptionMass root * tail who| ≤
      |quittingRootAbsorbingContribution reward root who| +
        |quittingRootAbsorptionMass root * tail who| := abs_sub _ _
    _ ≤ M * quittingRootAbsorptionMass root +
        quittingRootAbsorptionMass root * M := by
      apply add_le_add habsorbing
      rw [abs_mul, abs_of_nonneg hp0]
      exact mul_le_mul_of_nonneg_left htail hp0
    _ = 2 * M * quittingRootAbsorptionMass root := by ring

namespace QuittingAbsorptionPath

/-- Forcing one player to Continue moves that endpoint away from the tail by
at most twice the reward bound times opponent absorption. -/
theorem abs_quittingRootContinuePayoff_sub_tail_le_two_mul_opponentAbsorptionMass
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : Payoff ι) (root : ι → PMF Bool) (player : ι) (bound : ℝ)
    (hreward : ∀ terminal who, |reward terminal who| ≤ bound)
    (htail : |tail player| ≤ bound) :
    |quittingRootContinuePayoff reward tail root player - tail player| ≤
      2 * bound * quittingRootOpponentAbsorptionMass root player := by
  simpa only [quittingRootContinuePayoff, quittingRootSuccessorPayoff,
    quittingRootOpponentAbsorptionMass] using
      abs_quittingRootSuccessorPayoff_sub_tail_le_two_mul_absorptionMass
        reward tail (Function.update root player (PMF.pure false)) player bound
        hreward htail

end QuittingAbsorptionPath

end GameTheory
