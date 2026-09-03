/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.RewardBound
import UniformEquilibrium.Quitting.Root.SuccessorCertificate

/-!
# Coordinatewise mixture identities for product quitting roots

The expected payoff at a product root is affine in any one player's Boolean
marginal, independently of which player's payoff is observed.  The resulting
identities and reward-box estimates are root semantics; they do not require a
Nash, chronology, compactness, or player-count hypothesis.
-/

noncomputable section

namespace GameTheory

open Math.Probability Math.PMFProduct

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Replacing one player's Boolean law mixes the two pure replacements with
that law's weights, for an arbitrary observed payoff coordinate. -/
theorem quittingRootExpectedPayoff_update_coord_eq_mix
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : Payoff ι) (root : ι → PMF Bool)
    (coord : ι) (marginal : PMF Bool) (who : ι) :
    quittingRootExpectedPayoff reward tail
        (Function.update root coord marginal) who =
      (marginal true).toReal *
          quittingRootExpectedPayoff reward tail
            (Function.update root coord (PMF.pure true)) who +
        (marginal false).toReal *
          quittingRootExpectedPayoff reward tail
            (Function.update root coord (PMF.pure false)) who := by
  unfold quittingRootExpectedPayoff
  rw [pmfPi_update_bind, expect_bind, expect_eq_sum, Fintype.sum_bool]

omit [DecidableEq ι] in
/-- A common bound on terminal and continuation payoffs bounds each expected
root payoff. -/
theorem abs_quittingRootExpectedPayoff_le_bound
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (continuation : Payoff ι) (root : ι → PMF Bool) (who : ι)
    {M : ℝ} (hreward : ∀ S player, |reward S player| ≤ M)
    (hcontinuation : ∀ player, |continuation player| ≤ M) :
    |quittingRootExpectedPayoff reward continuation root who| ≤ M := by
  unfold quittingRootExpectedPayoff
  exact abs_expect_le_of_abs_le (pmfPi root)
    (fun action => quittingRootPayoff reward continuation action who)
    (fun action => abs_quittingRootPayoff_le reward continuation
      hreward hcontinuation action who)

/-- Replacing one coordinate's marginal moves an observed payoff by at most
the Quit-probability change times twice the common payoff bound. -/
theorem abs_quittingRootExpectedPayoff_update_coord_sub_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : Payoff ι) (root : ι → PMF Bool) (coord who : ι)
    (first second : PMF Bool) {M : ℝ}
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (htail : ∀ player, |tail player| ≤ M) :
    |quittingRootExpectedPayoff reward tail
        (Function.update root coord first) who -
      quittingRootExpectedPayoff reward tail
        (Function.update root coord second) who| ≤
      |(first true).toReal - (second true).toReal| * (2 * M) := by
  set quitBranch := quittingRootExpectedPayoff reward tail
    (Function.update root coord (PMF.pure true)) who with hquitBranch
  set continueBranch := quittingRootExpectedPayoff reward tail
    (Function.update root coord (PMF.pure false)) who with hcontinueBranch
  have hquitBound : |quitBranch| ≤ M :=
    abs_quittingRootExpectedPayoff_le_bound reward tail _ who hreward htail
  have hcontinueBound : |continueBranch| ≤ M :=
    abs_quittingRootExpectedPayoff_le_bound reward tail _ who hreward htail
  have hfirstSum : (first false).toReal = 1 - (first true).toReal := by
    have hsum : (first false).toReal + (first true).toReal = 1 := by
      simpa [Fintype.sum_bool, add_comm] using pmf_toReal_sum_one first
    linarith
  have hsecondSum : (second false).toReal = 1 - (second true).toReal := by
    have hsum : (second false).toReal + (second true).toReal = 1 := by
      simpa [Fintype.sum_bool, add_comm] using pmf_toReal_sum_one second
    linarith
  rw [quittingRootExpectedPayoff_update_coord_eq_mix reward tail root coord
      first who,
    quittingRootExpectedPayoff_update_coord_eq_mix reward tail root coord
      second who, ← hquitBranch, ← hcontinueBranch]
  have hsplit :
      (first true).toReal * quitBranch +
          (first false).toReal * continueBranch -
        ((second true).toReal * quitBranch +
          (second false).toReal * continueBranch) =
      ((first true).toReal - (second true).toReal) *
        (quitBranch - continueBranch) := by
    rw [hfirstSum, hsecondSum]
    ring
  rw [hsplit, abs_mul]
  have hgap : |quitBranch - continueBranch| ≤ 2 * M := by
    have hquit' := abs_le.mp hquitBound
    have hcontinue' := abs_le.mp hcontinueBound
    rw [abs_le]
    constructor <;> linarith
  exact mul_le_mul_of_nonneg_left hgap (abs_nonneg _)

/-- Perturbing one coordinate away from its current marginal has the same
two-payoff-bound estimate. -/
theorem abs_quittingRootExpectedPayoff_update_coord_sub_self_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : Payoff ι) (root : ι → PMF Bool) (coord who : ι)
    (marginal : PMF Bool) {M : ℝ}
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (htail : ∀ player, |tail player| ≤ M) :
    |quittingRootExpectedPayoff reward tail
        (Function.update root coord marginal) who -
      quittingRootExpectedPayoff reward tail root who| ≤
      |(marginal true).toReal - (root coord true).toReal| * (2 * M) := by
  have h := abs_quittingRootExpectedPayoff_update_coord_sub_le reward tail
    root coord who marginal (root coord) hreward htail
  rwa [Function.update_eq_self] at h

end GameTheory
