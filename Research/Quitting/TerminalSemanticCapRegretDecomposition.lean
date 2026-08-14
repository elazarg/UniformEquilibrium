/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.TerminalCapNashEndpointTransport
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticPlateauDefectCharge

/-!
# Exact cap-regret decomposition

For an arbitrary product root, the semantic debt after prefixing is the sum
of two terms: the root's one-stage Nash defect against the envelope coordinate
and the joint-Continue transport of the inherited debt.  This is the exact
arbitrary-root identity whose zero-defect specialization is cap--Nash debt
scaling.
-/

noncomputable section

namespace GameTheory

open Math.Probability

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}

/-- Exact decomposition of prefixed semantic debt into cap Nash defect and
transported inherited debt. -/
theorem quittingTerminalSemanticDebt_prefix_eq_capDefect_add_transport
    (pair : QuittingTerminalSemanticPair ι) (root : ι → PMF Bool)
    (who : ι) :
    quittingTerminalSemanticDebt
        (quittingTerminalSemanticPrefix reward root pair) who =
      quittingRootCoordinateNashDefect reward pair.2 root who +
        quittingStationaryContinueMass root *
          quittingTerminalSemanticDebt pair who := by
  have hquit : quittingRootQuitPayoff reward pair.1 root who =
      quittingRootQuitPayoff reward pair.2 root who :=
    quittingRootQuitPayoff_continuation_invariant
      reward pair.1 pair.2 root who
  have hcontinue :
      quittingRootContinuePayoff reward
          (Function.update pair.1 who (pair.2 who)) root who =
        quittingRootContinuePayoff reward pair.2 root who := by
    apply quittingRootExpectedPayoff_continuation_congr
    simp
  unfold quittingTerminalSemanticDebt quittingTerminalSemanticPrefix
    quittingRootCoordinateNashDefect
  dsimp only
  rw [hquit, hcontinue]
  have htransport := quittingRootSuccessorPayoff_sub_eq_continueMass_mul
    reward pair.2 pair.1 root who
  linarith

/-- At a global minimum of total semantic debt, every root pays for its
absorption mass through total cap Nash defect. -/
theorem minimumTerminalSemantic_absorption_mul_debtSum_le_capDefect
    (pair : QuittingTerminalSemanticPair ι) (root : ι → PMF Bool)
    {M : ℝ} (hM : 0 ≤ M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hpair : pair ∈ quittingTerminalSemanticCarrier reward)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum pair ≤
        quittingTerminalSemanticDebtSum candidate) :
    quittingRootAbsorptionMass root *
        quittingTerminalSemanticDebtSum pair ≤
      quittingRootTotalNashDefect reward pair.2 root := by
  let prefixed := quittingTerminalSemanticPrefix reward root pair
  have hprefixed : prefixed ∈ quittingTerminalSemanticCarrier reward :=
    quittingTerminalSemanticPrefix_mem_carrier
      reward root pair hM hreward hpair
  have hminPrefix : quittingTerminalSemanticDebtSum pair ≤
      quittingTerminalSemanticDebtSum prefixed :=
    hminimum prefixed hprefixed
  have hsum : quittingTerminalSemanticDebtSum prefixed =
      quittingRootTotalNashDefect reward pair.2 root +
        quittingStationaryContinueMass root *
          quittingTerminalSemanticDebtSum pair := by
    dsimp only [prefixed]
    unfold quittingTerminalSemanticDebtSum quittingRootTotalNashDefect
    simp_rw [quittingTerminalSemanticDebt_prefix_eq_capDefect_add_transport
      (reward := reward) pair root]
    rw [Finset.sum_add_distrib, Finset.mul_sum]
  unfold quittingRootAbsorptionMass
  rw [hsum] at hminPrefix
  nlinarith

end GameTheory
