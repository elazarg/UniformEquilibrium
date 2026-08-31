/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Paths.BehaviorStoppingLaw

/-!
# Behavioral reconstruction from a complete stopping law

This module owns the canonical conditional-hazard realization of one complete
live-spine stopping law and its exact stopping-law roundtrip.
-/

noncomputable section

namespace GameTheory

open StochasticGame
open Math.Probability Math.Probability.DiscreteHazard

variable {iota : Type} [Fintype iota] [DecidableEq iota]

/-- The canonical behavioral realization of an arbitrary complete stopping
law. -/
def quittingStoppingLawBehaviorStrategy
    (reward : {S : Finset iota // S.Nonempty} -> Payoff iota)
    (who : iota) (law : PMF (Option Nat)) :
    (quittingGame reward).BehaviorStrategy who :=
  fun time _history => (StoppingLaw.toScalarHazard law).toBoolean time

omit [DecidableEq iota] in
@[simp] theorem quittingBehaviorStoppingLaw_stoppingLawBehaviorStrategy
    (reward : {S : Finset iota // S.Nonempty} -> Payoff iota)
    (who : iota) (law : PMF (Option Nat)) :
    quittingBehaviorStoppingLaw reward
        (quittingStoppingLawBehaviorStrategy reward who law) = law := by
  unfold quittingBehaviorStoppingLaw quittingHazardStoppingLaw
    quittingStoppingLawBehaviorStrategy quittingBehaviorLiveHazard
  rw [ScalarHazard.toScalar_toBoolean,
    StoppingLaw.stoppingLaw_toScalarHazard]

end GameTheory
