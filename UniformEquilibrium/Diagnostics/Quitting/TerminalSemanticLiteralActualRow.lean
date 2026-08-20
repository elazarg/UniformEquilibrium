/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticPlateauLocalizedOtherDefect

/-!
# Literal data at an actual quitting-game row

This module names the shifted semantic tail, product root, and canonical
better-endpoint gain at one reached live row of an executable behavior
profile. These definitions are shared by transport, localization, and
root--tail complementarity arguments.
-/

noncomputable section

namespace GameTheory

open Math.Probability Math.PMFProduct

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The shifted semantic tail used by the actual row at `stage`. -/
def quittingLiteralActualRowTail
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (stage : ℕ) :
    QuittingTerminalSemanticPair ι :=
  quittingTerminalSemanticPair reward
    (quittingAllContinueProfileSpine reward profile (stage + 1))

/-- The literal product root played on the actual live history at `stage`. -/
def quittingLiteralActualRowRoot
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (stage : ℕ) :
    ι → PMF Bool :=
  quittingProfileLiveRoot reward profile stage

/-- The canonical legal gain obtained by replacing the actual marginal at one
reached row by its better pure endpoint and leaving the tail unchanged. -/
def quittingLiteralActualRowBestEndpointGain
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (who : ι) (stage : ℕ) : ℝ :=
  let tail := quittingLiteralActualRowTail reward profile stage
  let root := quittingLiteralActualRowRoot reward profile stage
  let action := quittingRootBestEndpointAction reward tail.1 root who
  let deviation := quittingStagePureEndpointBehaviorDeviation
    reward profile who stage action
  quittingTerminalPayoff reward (Function.update profile who deviation) who -
    quittingTerminalPayoff reward profile who

end GameTheory
