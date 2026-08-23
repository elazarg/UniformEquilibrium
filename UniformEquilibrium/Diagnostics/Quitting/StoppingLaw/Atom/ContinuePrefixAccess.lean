/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.StoppingLaw.Atom.ExactPrefixStackAccess
import UniformEquilibrium.Diagnostics.Quitting.StoppingLaw.ContinuePrefixAtomAccess

/-!
# Continue-prefix access for stopping-law atoms

This adapter applies the generic finite-word Continue-through construction to
an atom exact-prefix stack.  Mover-deleted survival tends to one along
that stack, so its terminal atom alternative is eventually visible at
the front of the prefix.
-/

noncomputable section

namespace GameTheory

open Filter Math.Probability

variable {ι : Type} [Fintype ι] [DecidableEq ι]

namespace QuittingStoppingLawAtomExactPrefixStackAccess

/-- **Preemption-free atom access.**  Every atom exact-prefix stack has
eventually positive atoms at its front after one legal Continue-through
deviation by the mover.  This conclusion does not require joint prescribed
survival and therefore also consumes the singleton-active preemption branch.
-/
theorem continuePrefix_atomAlternative_eventually
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {frontier : QuittingPositiveMinimumDebtTangentFamily reward}
    (stack : QuittingStoppingLawAtomExactPrefixStackAccess frontier) :
    ∀ᶠ rank in atTop,
      HasQuittingContinuePrefixDebtSlopeAtomAlternative reward
        (stack.roots rank)
        (frontier.source rank) stack.mover.1
        stack.observer
        (frontier.replacement stack.mover rank)
        (stack.charge / 2) := by
  have hsurvival := stack.opponentSurvival_tendsto_one
    stack.mover.2
  have hhalf : ∀ᶠ rank in atTop, 1 / 2 ≤
      quittingLiteralRootStackOpponentSurvival
        (stack.roots rank) stack.mover.1 :=
    hsurvival.eventually (Ioi_mem_nhds (show (1 / 2 : ℝ) < 1 by norm_num)) |>.mono
      fun _ h => h.le
  filter_upwards [stack.atom_eventually, hhalf] with rank hatom hsurvivalRank
  exact hasQuittingContinuePrefixDebtSlopeAtomAlternative_of_halfSurvival
    reward (stack.roots rank)
      (frontier.source rank) stack.mover.1
      stack.observer
      (frontier.replacement stack.mover rank)
      stack.charge_pos.le hsurvivalRank hatom

/-- Explicit singleton-active specialization: the unique active owner is the
mover of the accessed atom, so all possible owner preemption is removed by
the same legal Continue-through deviation. -/
theorem singletonActive_continuePrefix_atomAlternative_eventually
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {frontier : QuittingPositiveMinimumDebtTangentFamily reward}
    (stack : QuittingStoppingLawAtomExactPrefixStackAccess frontier)
    (owner : ι) (hactive : frontier.positiveDebtSupport = {owner}) :
    stack.mover.1 = owner ∧
      ∀ᶠ rank in atTop,
        HasQuittingContinuePrefixDebtSlopeAtomAlternative reward
          (stack.roots rank)
          (frontier.source rank) owner
          stack.observer
          (frontier.replacement stack.mover rank)
          (stack.charge / 2) := by
  have hmover : stack.mover.1 = owner := by
    simpa [hactive] using stack.mover.2
  subst owner
  exact ⟨rfl, stack.continuePrefix_atomAlternative_eventually⟩

end QuittingStoppingLawAtomExactPrefixStackAccess

end GameTheory
