/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Root.TerminalDebtPrefix

/-!
# One-stage Nash defect of a quitting root

This module isolates the elementary coordinatewise and total Nash defects of
a product root. The interface is independent of terminal-semantic plateau
arguments and can be used by Bellman reductions directly.
-/

noncomputable section

namespace GameTheory

open Math.Probability Math.PMFProduct

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The least nonnegative one-coordinate error needed to make the prescribed
root mixture dominate both pure endpoints. -/
def quittingRootCoordinateNashDefect
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : Payoff ι) (root : ι → PMF Bool) (who : ι) : ℝ :=
  max (quittingRootQuitPayoff reward tail root who)
      (quittingRootContinuePayoff reward tail root who) -
    quittingRootSuccessorPayoff reward tail root who

/-- Total one-stage Nash defect of a product root. -/
def quittingRootTotalNashDefect
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : Payoff ι) (root : ι → PMF Bool) : ℝ :=
  ∑ who, quittingRootCoordinateNashDefect reward tail root who

/-- A root-coordinate Nash defect is nonnegative because the prescribed
payoff is a convex combination of the two pure endpoint payoffs. -/
theorem quittingRootCoordinateNashDefect_nonneg
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : Payoff ι) (root : ι → PMF Bool) (who : ι) :
    0 ≤ quittingRootCoordinateNashDefect reward tail root who := by
  rw [quittingRootCoordinateNashDefect,
    quittingRootSuccessorPayoff_eq_endpointMix]
  have hsum := quittingRoot_continueProbability_add_quitProbability root who
  have hquit := le_max_left
    (quittingRootQuitPayoff reward tail root who)
    (quittingRootContinuePayoff reward tail root who)
  have hcontinue := le_max_right
    (quittingRootQuitPayoff reward tail root who)
    (quittingRootContinuePayoff reward tail root who)
  have hquitProbability : 0 ≤ (root who true).toReal := ENNReal.toReal_nonneg
  have hcontinueProbability : 0 ≤ (root who false).toReal :=
    ENNReal.toReal_nonneg
  have hweighted :
      (root who true).toReal * quittingRootQuitPayoff reward tail root who +
          (root who false).toReal *
            quittingRootContinuePayoff reward tail root who ≤
        max (quittingRootQuitPayoff reward tail root who)
          (quittingRootContinuePayoff reward tail root who) := by
    calc
      (root who true).toReal * quittingRootQuitPayoff reward tail root who +
          (root who false).toReal *
            quittingRootContinuePayoff reward tail root who ≤
        (root who true).toReal *
            max (quittingRootQuitPayoff reward tail root who)
              (quittingRootContinuePayoff reward tail root who) +
          (root who false).toReal *
            max (quittingRootQuitPayoff reward tail root who)
              (quittingRootContinuePayoff reward tail root who) :=
        add_le_add
          (mul_le_mul_of_nonneg_left hquit hquitProbability)
          (mul_le_mul_of_nonneg_left hcontinue hcontinueProbability)
      _ = max (quittingRootQuitPayoff reward tail root who)
            (quittingRootContinuePayoff reward tail root who) := by
        rw [← add_mul]
        have hsum' : (root who true).toReal +
            (root who false).toReal = 1 := by linarith
        rw [hsum', one_mul]
  linarith

/-- The total root Nash defect is nonnegative. -/
theorem quittingRootTotalNashDefect_nonneg
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : Payoff ι) (root : ι → PMF Bool) :
    0 ≤ quittingRootTotalNashDefect reward tail root := by
  exact Finset.sum_nonneg fun who _ =>
    quittingRootCoordinateNashDefect_nonneg reward tail root who

/-- Exact Nash is precisely zero coordinate defect. -/
theorem isZeroQuittingRootNash_iff_coordinateNashDefect_eq_zero
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : Payoff ι) (root : ι → PMF Bool) :
    IsεQuittingRootNash reward tail 0 root ↔
      ∀ who, quittingRootCoordinateNashDefect reward tail root who = 0 := by
  constructor
  · intro hnash who
    rw [quittingRootCoordinateNashDefect,
      ← quittingRootSuccessorPayoff_eq_max_of_isZeroNash
        reward tail root who hnash, sub_self]
  · intro hzero
    apply (isZeroQuittingRootEndpointNash_iff_isZeroQuittingRootNash
      reward tail root).mp
    intro who
    have hdefect := hzero who
    unfold quittingRootCoordinateNashDefect at hdefect
    have hquit : quittingRootQuitPayoff reward tail root who ≤
        quittingRootSuccessorPayoff reward tail root who := by
      linarith [le_max_left
        (quittingRootQuitPayoff reward tail root who)
        (quittingRootContinuePayoff reward tail root who)]
    have hcontinue : quittingRootContinuePayoff reward tail root who ≤
        quittingRootSuccessorPayoff reward tail root who := by
      linarith [le_max_right
        (quittingRootQuitPayoff reward tail root who)
        (quittingRootContinuePayoff reward tail root who)]
    have hmix := quittingRootSuccessorPayoff_eq_endpointMix
      reward tail root who
    have hsum := quittingRoot_continueProbability_add_quitProbability root who
    have hcontinueProbability : 0 ≤ (root who false).toReal :=
      ENNReal.toReal_nonneg
    have hquitProbability : 0 ≤ (root who true).toReal := ENNReal.toReal_nonneg
    have hquitRegret :
        quittingRootQuitPayoff reward tail root who -
            quittingRootSuccessorPayoff reward tail root who =
          (root who false).toReal *
            (quittingRootQuitPayoff reward tail root who -
              quittingRootContinuePayoff reward tail root who) := by
      rw [hmix]
      have hquitMass : (root who true).toReal =
          1 - (root who false).toReal := by linarith
      rw [hquitMass]
      ring
    have hcontinueRegret :
        quittingRootContinuePayoff reward tail root who -
            quittingRootSuccessorPayoff reward tail root who =
          -(root who true).toReal *
            (quittingRootQuitPayoff reward tail root who -
              quittingRootContinuePayoff reward tail root who) := by
      rw [hmix]
      have hcontinueMass : (root who false).toReal =
          1 - (root who true).toReal := by linarith
      rw [hcontinueMass]
      ring
    unfold quittingRootEndpointDifference
    constructor
    · linarith
    · linarith

end GameTheory
