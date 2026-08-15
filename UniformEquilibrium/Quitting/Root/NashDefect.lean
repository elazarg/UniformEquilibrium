/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Root.SuccessorCertificate

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

/-- Approximate root Nash is precisely the coordinatewise Nash-defect bound.
No nonnegativity assumption on the error is needed. -/
theorem isεQuittingRootNash_iff_coordinateNashDefect_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : Payoff ι) (ε : ℝ) (root : ι → PMF Bool) :
    IsεQuittingRootNash reward tail ε root ↔
      ∀ who, quittingRootCoordinateNashDefect reward tail root who ≤ ε := by
  constructor
  · intro hnash who
    have hquit :=
      quittingRootQuitPayoff_le_successor_add_of_isεNash
        reward tail ε root who hnash
    have hcontinue :=
      quittingRootContinuePayoff_le_successor_add_of_isεNash
        reward tail ε root who hnash
    unfold quittingRootCoordinateNashDefect
    linarith [max_le hquit hcontinue]
  · intro hdefect
    apply (isεQuittingRootEndpointNash_iff_isεQuittingRootNash
      reward tail ε root).mp
    apply (isεQuittingRootEndpointNash_iff_purePayoff_le
      reward tail ε root).mpr
    intro who
    have hwho := hdefect who
    unfold quittingRootCoordinateNashDefect at hwho
    constructor
    · linarith [le_max_left
        (quittingRootQuitPayoff reward tail root who)
        (quittingRootContinuePayoff reward tail root who)]
    · linarith [le_max_right
        (quittingRootQuitPayoff reward tail root who)
        (quittingRootContinuePayoff reward tail root who)]

/-- Total local Nash defect of an `ε`-Nash root is at most
`card ι * ε`. -/
theorem quittingRootTotalNashDefect_le_card_mul_of_isεQuittingRootNash
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : Payoff ι) (root : ι → PMF Bool) (ε : ℝ)
    (hnash : IsεQuittingRootNash reward tail ε root) :
    quittingRootTotalNashDefect reward tail root ≤ Fintype.card ι * ε := by
  unfold quittingRootTotalNashDefect
  calc
    (∑ who, quittingRootCoordinateNashDefect reward tail root who) ≤
        ∑ _who : ι, ε :=
      Finset.sum_le_sum fun who _ =>
        (isεQuittingRootNash_iff_coordinateNashDefect_le
          reward tail ε root).mp hnash who
    _ = Fintype.card ι * ε := by simp

/-- Exact Nash is precisely zero coordinate defect. -/
theorem isZeroQuittingRootNash_iff_coordinateNashDefect_eq_zero
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : Payoff ι) (root : ι → PMF Bool) :
    IsεQuittingRootNash reward tail 0 root ↔
      ∀ who, quittingRootCoordinateNashDefect reward tail root who = 0 := by
  rw [isεQuittingRootNash_iff_coordinateNashDefect_le]
  constructor
  · intro hle who
    exact le_antisymm (hle who)
      (quittingRootCoordinateNashDefect_nonneg reward tail root who)
  · intro hzero who
    rw [hzero who]

/-- Exact Nash is precisely zero total Nash defect. -/
theorem isZeroQuittingRootNash_iff_totalNashDefect_eq_zero
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : Payoff ι) (root : ι → PMF Bool) :
    IsεQuittingRootNash reward tail 0 root ↔
      quittingRootTotalNashDefect reward tail root = 0 := by
  rw [isZeroQuittingRootNash_iff_coordinateNashDefect_eq_zero]
  constructor
  · intro hzero
    unfold quittingRootTotalNashDefect
    exact Finset.sum_eq_zero fun who _ => hzero who
  · intro hsum who
    unfold quittingRootTotalNashDefect at hsum
    exact (Finset.sum_eq_zero_iff_of_nonneg fun player _ =>
      quittingRootCoordinateNashDefect_nonneg reward tail root player).mp
        hsum who (Finset.mem_univ who)

end GameTheory
