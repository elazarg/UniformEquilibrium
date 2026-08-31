/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import MathUE.ProbabilityMassFunction.CompactStoppingLaw
import UniformEquilibrium.Quitting.Paths.StoppingLawReconstruction

/-!
# Behavior profiles reconstructed from compact stopping laws

This module realizes a player-indexed compact stopping-law family as a literal
quitting behavior profile and records its coordinatewise law identity.
-/

noncomputable section

namespace GameTheory

open StochasticGame Math.Probability

variable {ι : Type} [Fintype ι] [DecidableEq ι] [Nontrivial ι]

/-- Realize a finite family of compact complete stopping laws as one literal
behavior profile by reconstructing each player's conditional hazards. -/
def quittingCompactStoppingLawProfile
    (reward : {S : Finset ι // S.Nonempty} -> Payoff ι)
    (laws : ι -> CompactStoppingLaw) :
    (quittingGame reward).BehaviorProfile :=
  fun who => quittingStoppingLawBehaviorStrategy reward who (laws who).toPMF

omit [DecidableEq ι] [Nontrivial ι] in
@[simp] theorem quittingBehaviorStoppingLaw_compactStoppingLawProfile
    (reward : {S : Finset ι // S.Nonempty} -> Payoff ι)
    (laws : ι -> CompactStoppingLaw) (who : ι) :
    quittingBehaviorStoppingLaw reward
        (quittingCompactStoppingLawProfile reward laws who) =
      (laws who).toPMF := by
  simp [quittingCompactStoppingLawProfile]

end GameTheory
