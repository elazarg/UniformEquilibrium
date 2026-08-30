/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.AbsorptionPath.DiscreteRootSequencePath
import UniformEquilibrium.Quitting.Bellman.Finite.BooleanMobiusAdapter
import UniformEquilibrium.Quitting.Cycles.PhaseSwitchProfile

/-!
# Prefix and post-stage tail payoffs of root sequences

The initial value of a root sequence is its cumulative terminal reward before
a cutoff plus the surviving mass times the conditional value at that cutoff.
This is the finite payoff identity used to identify chronological jump-tail
limits.  It makes no equilibrium assertion.
-/

noncomputable section

namespace GameTheory.QuittingAbsorptionPath

open Finset

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Exact prefix plus surviving post-prefix tail decomposition, expressed in
the chronological coalition coordinates. -/
theorem quittingRootSequenceTerminalValue_eq_prefixReward_add_survival_mul_tail
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι) (cutoff : ℕ) :
    quittingRootSequenceTerminalValue reward roots who 0 =
      (∑ coalition,
        quittingRootSequenceCumulativeCoalitionMass roots cutoff coalition *
          reward coalition who) +
        quittingRootSequenceSurvival roots cutoff *
          quittingRootSequenceTailVector reward roots cutoff who := by
  rw [quittingRootSequenceTerminalValue_eq_truncated_add_jointSurvival_mul,
    quittingRootSequenceTerminalValue_quittingTruncatedRoots_eq_sum]
  change
    (∑ stage ∈ Finset.range cutoff,
      quittingRootSequenceSurvival roots stage *
        quittingRootAbsorbingContribution reward (roots stage) who) +
      quittingRootSequenceSurvival roots cutoff *
        quittingRootSequenceTailVector reward roots cutoff who = _
  congr 1
  simp_rw [quittingRootAbsorbingContribution_eq_sum_nonemptyCoalitionMass,
    Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro coalition _
  unfold quittingRootSequenceCumulativeCoalitionMass
    quittingRootSequenceStageCoalitionMass quittingRootCoalitionMass
    quittingRootQuitRates hazardOfRoot
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro stage _
  ring

end GameTheory.QuittingAbsorptionPath
