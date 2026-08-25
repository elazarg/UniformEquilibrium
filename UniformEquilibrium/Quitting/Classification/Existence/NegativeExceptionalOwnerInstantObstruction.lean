/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Classification.Existence.StationarilyGeneratedNegativeOwnerBoundary
import UniformEquilibrium.Quitting.Punishment.InstantPunishment

/-!
# Instant-punishment obstruction at a negative exceptional owner

The naive closure of a negative exceptional owner is to make that owner Quit
surely and punish continuation.  The exact instant-punishment criterion shows
precisely what can stop this construction: either the owner's behavioral
punishment floor lies strictly above the negative singleton payoff, or some
other player strictly gains by joining the owner's singleton exit.

These inequalities are not fields of the exceptional-owner source.  Thus the
remaining negative-owner seam is strategic, not a missing horizon or
probabilistic-concentration argument.
-/

noncomputable section

namespace GameTheory

open StochasticGame

variable {iota : Type} [Fintype iota] [DecidableEq iota]

/-- A divergent negative exceptional owner either closes S.2 through the
sure-owner instant root, or exposes one of the two exact scalar obstructions
to that root: punishment-floor individual rationality or a profitable join. -/
theorem
    QuittingDivergentNegativeExceptionalOwnerResidual.instant_or_floorAboveSolo_or_joinGain
    {reward : {S : Finset iota // S.Nonempty} → Payoff iota}
    (residual : QuittingDivergentNegativeExceptionalOwnerResidual reward) :
    QuittingInstantPunishmentεEquilibriumExistence reward ∨
      quittingSoloReward reward residual.source.owner residual.source.owner <
        quittingPunishmentValue reward residual.source.owner ∨
      ∃ other, other ≠ residual.source.owner ∧
        quittingSoloReward reward residual.source.owner other <
          quittingSingletonCollisionReward reward residual.source.owner other := by
  let owner := residual.source.owner
  by_cases hIR : IsQuittingInstantPunishmentIR reward owner
  · by_cases hnoJoin : IsQuittingInstantNoJoin reward owner
    · left
      intro epsilon hepsilon
      obtain ⟨punishRow, hpunish⟩ :=
        exists_quittingStationaryPunishmentRoot_lt_add
          reward owner hepsilon
      refine ⟨owner, quittingInstantRoot owner, punishRow, ?_,
        hpunish.le, ?_⟩
      · simp [quittingInstantRoot, quittingSoloStationaryRoot]
      · exact isεAsymptoticNash_quittingInstantPunishmentProfile
          reward owner hIR hnoJoin hepsilon.le hpunish.le
    · right
      right
      unfold IsQuittingInstantNoJoin at hnoJoin
      push Not at hnoJoin
      obtain ⟨other, hother, hgain⟩ := hnoJoin
      exact ⟨other, hother, hgain⟩
  · right
    left
    unfold IsQuittingInstantPunishmentIR at hIR
    exact lt_of_not_ge hIR

/-- After S.2 is excluded, every divergent negative exceptional owner carries
one of those two explicit obstructions. -/
theorem
    QuittingDivergentNegativeExceptionalOwnerResidual.floorAboveSolo_or_joinGain_of_not_instant
    {reward : {S : Finset iota // S.Nonempty} → Payoff iota}
    (residual : QuittingDivergentNegativeExceptionalOwnerResidual reward)
    (hnoInstant : ¬QuittingInstantPunishmentεEquilibriumExistence reward) :
    quittingSoloReward reward residual.source.owner residual.source.owner <
        quittingPunishmentValue reward residual.source.owner ∨
      ∃ other, other ≠ residual.source.owner ∧
        quittingSoloReward reward residual.source.owner other <
          quittingSingletonCollisionReward reward residual.source.owner other := by
  rcases residual.instant_or_floorAboveSolo_or_joinGain with
    hinstant | hobstruction
  · exact False.elim (hnoInstant hinstant)
  · exact hobstruction

end GameTheory
