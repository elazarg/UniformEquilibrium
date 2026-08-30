/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Paths.SurvivalWindowLanding
import UniformEquilibrium.Quitting.Terminal.TailCompression.ElementaryCaps

/-!
# Vanishing-Nash root-sequence families

This module owns the low source interface for families of actual quitting root
sequences whose global Nash errors and probabilities of never absorbing both
vanish.  It does not assert complete absorption, path compactness, or
stagewise perfection.
-/

noncomputable section

namespace GameTheory

open Filter StochasticGame Math.Probability

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- A source family of actual root sequences with vanishing Nash error and
vanishing `Never` mass.  The reward is fixed across the family. -/
structure QuittingRootSequenceVanishingNashFamily
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) where
  roots : ℕ → ℕ → ι → PMF Bool
  error : ℕ → ℝ
  nash : ∀ index,
    IsεQuittingRootSequenceNash reward (error index) (roots index)
  error_tendsto_zero : Tendsto error atTop (nhds 0)
  never_tendsto_zero :
    Tendsto (fun index => quittingJointSurvivalLimit (roots index) 0)
      atTop (nhds 0)

namespace QuittingRootSequenceVanishingNashFamily

variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}

/-- The global Nash certificate controls every stage deviation after
multiplication by that stage's reach probability. -/
theorem reach_mul_stageDeviationGain_le
    (source : QuittingRootSequenceVanishingNashFamily reward)
    (index : ℕ) (who : ι) (stage : ℕ) (deviation : PMF Bool)
    (tail : ℕ → PMF Bool) :
    quittingJointSurvivalWeight (source.roots index) 0 stage *
        (quittingRootSuccessorPayoff reward
            (fun _ => quittingRootSequenceHazardTerminalValue reward
              (fun time => source.roots index (stage + 1 + time)) who tail 0)
            (Function.update (source.roots index stage) who deviation) who -
          quittingRootSequenceTerminalValue reward
            (source.roots index) who stage) ≤ source.error index :=
  quittingJointSurvivalWeight_mul_stageDeviationGain_le reward
    (source.roots index) (source.nash index) who stage deviation tail

/-- The global Nash certificate controls an arbitrary tail deviation after a
reached stage, again in the division-free weighted form. -/
theorem reach_mul_tailDeviationGain_le
    (source : QuittingRootSequenceVanishingNashFamily reward)
    (index : ℕ) (who : ι) (start : ℕ) (hazard : ℕ → PMF Bool) :
    quittingJointSurvivalWeight (source.roots index) 0 start *
        (quittingRootSequenceHazardTerminalValue reward
            (fun offset => source.roots index (start + offset)) who hazard 0 -
          quittingRootSequenceTerminalValue reward
            (source.roots index) who start) ≤ source.error index :=
  quittingJointSurvivalWeight_mul_tailDeviationGain_le reward
    (source.roots index) (source.nash index) who start hazard

/-- At every positively reached stage, the actual row is one-stage Nash
against its actual suffix value with the exact inverse-reach error. -/
theorem reachedRootNash
    (source : QuittingRootSequenceVanishingNashFamily reward)
    (index stage : ℕ)
    (hreach : 0 <
      quittingJointSurvivalWeight (source.roots index) 0 stage) :
    IsεQuittingRootNash reward
      (quittingRootSequenceTailVector reward (source.roots index) (stage + 1))
      (source.error index /
        quittingJointSurvivalWeight (source.roots index) 0 stage)
      (source.roots index stage) :=
  isεQuittingRootNash_tailVector_of_isεQuittingRootSequenceNash reward
    (source.roots index) (source.nash index) stage hreach

/-- Restarting after a uniformly reached prefix preserves global Nash with
the exact inverse-reach error scaling. -/
theorem shiftedNash_of_reach_ge
    (source : QuittingRootSequenceVanishingNashFamily reward)
    (index start : ℕ) {rho : ℝ} (herror : 0 ≤ source.error index)
    (hrho : 0 < rho)
    (hreach : rho ≤
      quittingJointSurvivalWeight (source.roots index) 0 start) :
    IsεQuittingRootSequenceNash reward (source.error index / rho)
      (fun offset => source.roots index (start + offset)) :=
  isεQuittingRootSequenceNash_shift_of_survival_ge reward
    (source.roots index) herror hrho (source.nash index) start hreach

end QuittingRootSequenceVanishingNashFamily

end GameTheory
