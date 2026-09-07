/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Cycles.PeriodOneTangentAtlas
import UniformEquilibrium.Quitting.Root.TerminalSemanticPair
import UniformEquilibrium.Quitting.Root.NashDefect

/-!
# Terminal-semantic debt under an auxiliary Nash prefix

A root selected against a lower auxiliary continuation can be prefixed to a
terminal-semantic pair. The resulting coordinate debt is bounded by transported
old debt, the singleton absorption mass times the auxiliary shift, and the
literal coordinate Nash defect. The exact Nash bound is its zero-defect case.
-/

noncomputable section

namespace GameTheory

open Math.Probability Math.PMFProduct

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}

/-- Prefix debt against the actual cap is controlled by the coordinate Nash
defect at the lower auxiliary continuation. -/
theorem quittingTerminalSemanticDebt_prefix_le_auxiliaryNashDefect
    (pair : QuittingTerminalSemanticPair ι) (h : Payoff ι)
    (root : ι → PMF Bool) (who : ι) (hh : 0 ≤ h who) :
    quittingTerminalSemanticDebt
        (quittingTerminalSemanticPrefix reward root pair) who ≤
      quittingStationaryContinueMass root *
          quittingTerminalSemanticDebt pair who +
        quittingRootCoalitionMass root {who} * h who +
          quittingRootCoordinateNashDefect reward (pair.2 - h) root who := by
  let auxiliary : Payoff ι := pair.2 - h
  let quitValue := quittingRootQuitPayoff reward pair.1 root who
  let continueAux := quittingRootContinuePayoff reward auxiliary root who
  let opponentContinue := quittingRootOpponentContinueMass root who
  let defect := quittingRootCoordinateNashDefect reward auxiliary root who
  have hauxiliary : auxiliary who + h who = pair.2 who := by
    dsimp [auxiliary]
    ring
  have hquitInvariant : quittingRootQuitPayoff reward auxiliary root who =
      quitValue := quittingRootQuitPayoff_continuation_invariant
        reward auxiliary pair.1 root who
  have hcontinueActual :
      quittingRootContinuePayoff reward
          (Function.update pair.1 who (pair.2 who)) root who =
        continueAux + opponentContinue * h who := by
    calc
      _ = quittingRootContinuePayoff reward
          (Function.update auxiliary who (pair.2 who)) root who := by
        unfold quittingRootContinuePayoff
        apply quittingRootExpectedPayoff_continuation_congr
        simp
      _ = quittingRootContinuePayoff reward
          (Function.update auxiliary who (auxiliary who + h who)) root who := by
        rw [hauxiliary]
      _ = _ := quittingRootContinuePayoff_update_add
        reward auxiliary root who (h who)
  have hincrement : 0 ≤ opponentContinue * h who := mul_nonneg
    (quittingRootOpponentContinueMass_nonneg root who) hh
  have henvelope :
      (quittingTerminalSemanticPrefix reward root pair).2 who ≤
        quittingRootSuccessorPayoff reward auxiliary root who + defect +
          opponentContinue * h who := by
    change max quitValue
        (quittingRootContinuePayoff reward
          (Function.update pair.1 who (pair.2 who)) root who) ≤ _
    rw [hcontinueActual]
    dsimp only [defect]
    rw [quittingRootCoordinateNashDefect]
    rw [hquitInvariant]
    apply max_le
    · linarith [le_max_left quitValue continueAux]
    · linarith [le_max_right quitValue continueAux]
  have hsuccessorDifference :
      quittingRootSuccessorPayoff reward auxiliary root who -
          quittingRootSuccessorPayoff reward pair.1 root who =
        quittingStationaryContinueMass root *
          (quittingTerminalSemanticDebt pair who - h who) := by
    rw [quittingRootSuccessorPayoff_sub_eq_continueMass_mul]
    dsimp [auxiliary, quittingTerminalSemanticDebt]
    ring
  have hsingleton : opponentContinue - quittingStationaryContinueMass root =
      quittingRootCoalitionMass root {who} :=
    quittingRootOpponentContinue_sub_continue_eq_singletonMass root who
  unfold quittingTerminalSemanticDebt
  change (quittingTerminalSemanticPrefix reward root pair).2 who -
      quittingRootSuccessorPayoff reward pair.1 root who ≤ _
  calc
    _ ≤ (quittingRootSuccessorPayoff reward auxiliary root who + defect +
          opponentContinue * h who) -
        quittingRootSuccessorPayoff reward pair.1 root who :=
      sub_le_sub_right henvelope _
    _ = _ := by
      rw [show opponentContinue = quittingRootCoalitionMass root {who} +
          quittingStationaryContinueMass root by linarith [hsingleton]]
      rw [show quittingRootSuccessorPayoff reward auxiliary root who =
          quittingRootSuccessorPayoff reward pair.1 root who +
            quittingStationaryContinueMass root *
              (quittingTerminalSemanticDebt pair who - h who) by
        linarith [hsuccessorDifference]]
      simp only [quittingTerminalSemanticDebt]
      dsimp only [defect, auxiliary]
      ring

/-- The exact-root auxiliary ledger is the zero-defect specialization. -/
theorem quittingTerminalSemanticDebt_prefix_le_auxiliaryNash
    (pair : QuittingTerminalSemanticPair ι) (h : Payoff ι)
    (root : ι → PMF Bool) (who : ι) (hh : 0 ≤ h who)
    (hnash : IsεQuittingRootNash reward (pair.2 - h) 0 root) :
    quittingTerminalSemanticDebt
        (quittingTerminalSemanticPrefix reward root pair) who ≤
      quittingStationaryContinueMass root *
          quittingTerminalSemanticDebt pair who +
        quittingRootCoalitionMass root {who} * h who := by
  have hbound := quittingTerminalSemanticDebt_prefix_le_auxiliaryNashDefect
    (reward := reward) pair h root who hh
  have hzero :=
    (isZeroQuittingRootNash_iff_coordinateNashDefect_eq_zero
      reward (pair.2 - h) root).mp hnash who
  rw [hzero, add_zero] at hbound
  exact hbound

end GameTheory
