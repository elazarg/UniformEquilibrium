/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Cycles.PeriodOneTangentAtlas
import UniformEquilibrium.Quitting.Root.TerminalSemanticPair

/-!
# Terminal-semantic debt under an auxiliary Nash prefix

An exact Nash root selected against a lower auxiliary continuation can be
prefixed to an actual terminal-semantic pair.  The resulting coordinate debt
is bounded by transported old debt plus the selected player's singleton
absorption mass times the auxiliary shift.
-/

noncomputable section

namespace GameTheory

open Math.Probability Math.PMFProduct

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}

/-- Prefix debt against the actual semantic pair is controlled by an exact
Nash root selected against the lower auxiliary continuation `pair.2 - h`.
The extra coefficient is exactly the singleton absorption mass of the player.
-/
theorem quittingTerminalSemanticDebt_prefix_le_auxiliaryNash
    (pair : QuittingTerminalSemanticPair ι) (h : Payoff ι)
    (root : ι → PMF Bool) (who : ι)
    (hh : 0 ≤ h who)
    (hnash : IsεQuittingRootNash reward (pair.2 - h) 0 root) :
    quittingTerminalSemanticDebt
        (quittingTerminalSemanticPrefix reward root pair) who ≤
      quittingStationaryContinueMass root *
          quittingTerminalSemanticDebt pair who +
        quittingRootCoalitionMass root {who} * h who := by
  let auxiliary : Payoff ι := pair.2 - h
  let quitValue := quittingRootQuitPayoff reward pair.1 root who
  let continueAux := quittingRootContinuePayoff reward auxiliary root who
  let opponentContinue := quittingRootOpponentContinueMass root who
  have hauxiliary : auxiliary who + h who = pair.2 who := by
    dsimp [auxiliary]
    ring
  have hquitInvariant : quittingRootQuitPayoff reward auxiliary root who =
      quitValue := by
    exact quittingRootQuitPayoff_continuation_invariant
      reward auxiliary pair.1 root who
  have hcontinueActual :
      quittingRootContinuePayoff reward
          (Function.update pair.1 who (pair.2 who)) root who =
        continueAux + opponentContinue * h who := by
    calc
      quittingRootContinuePayoff reward
          (Function.update pair.1 who (pair.2 who)) root who =
          quittingRootContinuePayoff reward
            (Function.update auxiliary who (pair.2 who)) root who := by
              unfold quittingRootContinuePayoff
              apply quittingRootExpectedPayoff_continuation_congr
              simp
      _ = quittingRootContinuePayoff reward
            (Function.update auxiliary who (auxiliary who + h who))
              root who := by rw [hauxiliary]
      _ = continueAux + opponentContinue * h who := by
            exact quittingRootContinuePayoff_update_add
              reward auxiliary root who (h who)
  have hopponentContinueNonneg : 0 ≤ opponentContinue :=
    quittingRootOpponentContinueMass_nonneg root who
  have hincrementNonneg : 0 ≤ opponentContinue * h who :=
    mul_nonneg hopponentContinueNonneg hh
  have henvelope :
      (quittingTerminalSemanticPrefix reward root pair).2 who ≤
        quittingRootSuccessorPayoff reward auxiliary root who +
          opponentContinue * h who := by
    change max quitValue
        (quittingRootContinuePayoff reward
          (Function.update pair.1 who (pair.2 who)) root who) ≤ _
    rw [hcontinueActual,
      quittingRootSuccessorPayoff_eq_max_of_isZeroNash
        reward auxiliary root who hnash,
      hquitInvariant]
    apply max_le
    · exact (le_max_left _ _).trans
        (le_add_of_nonneg_right hincrementNonneg)
    · dsimp only [continueAux]
      have hright := le_max_right quitValue
        (quittingRootContinuePayoff reward auxiliary root who)
      linarith
  have hsuccessorDifference :
      quittingRootSuccessorPayoff reward auxiliary root who -
          quittingRootSuccessorPayoff reward pair.1 root who =
        quittingStationaryContinueMass root *
          (quittingTerminalSemanticDebt pair who - h who) := by
    rw [quittingRootSuccessorPayoff_sub_eq_continueMass_mul]
    dsimp [auxiliary, quittingTerminalSemanticDebt]
    ring
  have hsingleton : opponentContinue -
      quittingStationaryContinueMass root =
        quittingRootCoalitionMass root {who} := by
    exact quittingRootOpponentContinue_sub_continue_eq_singletonMass root who
  unfold quittingTerminalSemanticDebt
  change (quittingTerminalSemanticPrefix reward root pair).2 who -
      quittingRootSuccessorPayoff reward pair.1 root who ≤ _
  calc
    (quittingTerminalSemanticPrefix reward root pair).2 who -
        quittingRootSuccessorPayoff reward pair.1 root who ≤
      (quittingRootSuccessorPayoff reward auxiliary root who +
          opponentContinue * h who) -
        quittingRootSuccessorPayoff reward pair.1 root who :=
      sub_le_sub_right henvelope _
    _ = quittingStationaryContinueMass root *
          quittingTerminalSemanticDebt pair who +
        quittingRootCoalitionMass root {who} * h who := by
      calc
        (quittingRootSuccessorPayoff reward auxiliary root who +
              opponentContinue * h who) -
            quittingRootSuccessorPayoff reward pair.1 root who =
          (quittingRootSuccessorPayoff reward auxiliary root who -
              quittingRootSuccessorPayoff reward pair.1 root who) +
            opponentContinue * h who := by ring
        _ = _ := by
          rw [hsuccessorDifference, ← hsingleton]
          ring

end GameTheory
