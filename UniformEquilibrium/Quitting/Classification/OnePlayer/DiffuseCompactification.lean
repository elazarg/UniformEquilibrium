/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Classification.Existence.DiffuseStationaryPrefixSourceAttachments
import UniformEquilibrium.Quitting.Classification.OnePlayer.StationaryBranch

/-!
# Diffuse compactification is stationary for one player

The two actual-source AKRS attachment seams are genuinely multi-player.
With a unique player, the stationary branch holds independently of the source
family, so both attachment obligations and their diffuse capstone close.
-/

noncomputable section

namespace GameTheory

open StochasticGame

variable {ι : Type} [Fintype ι] [DecidableEq ι] [Unique ι]

/-- Positive whole-prefix reach is already in the stationary branch for a
one-player game. -/
theorem hasPositiveJointPrefixReachAttachment_onePlayer
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) :
    HasPositiveJointPrefixReachAttachment reward := by
  intro _source
  exact Or.inl (quittingStationaryεEquilibriumExistence_onePlayer reward)

/-- The exceptional deleted-clock source is already in the stationary branch
for a one-player game. -/
theorem hasUniqueExceptionalOwnerAttachment_onePlayer
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) :
    HasUniqueExceptionalOwnerAttachment reward := by
  intro _source
  exact Or.inl (quittingStationaryεEquilibriumExistence_onePlayer reward)

/-- The exact AKRS diffuse compactification dependency holds for every
one-player quitting game. -/
theorem hasDiffuseStationarilyGeneratedCompactification_onePlayer
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) :
    HasDiffuseStationarilyGeneratedCompactification reward :=
  hasDiffuseStationarilyGeneratedCompactification_of_sourceAttachments
    (hasPositiveJointPrefixReachAttachment_onePlayer reward)
    (hasUniqueExceptionalOwnerAttachment_onePlayer reward)

end GameTheory
