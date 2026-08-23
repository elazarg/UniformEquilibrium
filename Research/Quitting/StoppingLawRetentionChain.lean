/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.StoppingLaw.TerminalSemanticStoppingLawRetentionChain
import Research.General.FiveCycleIncidenceSupportRigidity

/-!
# Five-cycle incidence from a stopping-law retention chain

The production retention-chain interface preserves one selected positive
singleton atom across every phase. For the exceptional five-cycle, the separate
support-rigidity theorem turns that common label into a consecutive two-edge
window omitting a player.
-/

noncomputable section

namespace GameTheory

open StochasticGame Math.Probability Math.PMFProduct

/-- A common retained singleton label gives the constant-incidence input to
five-cycle support rigidity. -/
theorem exists_commonIncidence_omittedWindow_of_halfRetentionChain
    (reward : {S : Finset (Fin 5) // S.Nonempty} → Payoff (Fin 5))
    (profiles : ℕ → (quittingGame reward).BehaviorProfile)
    (incidenceLabel : Fin 5) (time : ℕ)
    (hstep : RetainsQuittingStageAtomOnInterval reward (1 / 2) profiles 0 4
      (quittingSingletonTerminal incidenceLabel) time)
    (hpositive : 0 < quittingStageCoalitionMass reward (profiles 0) time
      (quittingSingletonTerminal incidenceLabel)) :
    let support : Fin 5 → Finset (Fin 5) := fun phase =>
      quittingPositiveSingletonStageSupport reward (profiles phase.val) time
    ∃ incidence : Fin 5 → Fin 5,
      IsSupportedIncidenceSelection support incidence ∧
        ∃ phase omitted,
          omitted ∉ fiveCycleResetRoleWindow incidence phase ∪
            fiveCycleResetRoleWindow incidence (phase + 1) := by
  dsimp only
  apply exists_supported_constantIncidence_omittedWindow
  intro phase
  have hphaseRetention :=
    RetainsQuittingStageAtomOnInterval.mono_steps
      reward (1 / 2) profiles 0
        (quittingSingletonTerminal incidenceLabel) time hstep
        (Nat.le_sub_one_of_lt phase.isLt)
  have hphase := stageCoalitionMass_pos_of_resetChain
    reward profiles (1 / 2) (by norm_num) 0 phase.val
      (quittingSingletonTerminal incidenceLabel) time hphaseRetention hpositive
  simpa [quittingPositiveSingletonStageSupport] using hphase

end GameTheory
