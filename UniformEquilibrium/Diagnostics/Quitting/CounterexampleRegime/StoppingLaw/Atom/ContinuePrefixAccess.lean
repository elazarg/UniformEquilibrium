/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegime.StoppingLaw.Atom.ExactPrefixChronology
import UniformEquilibrium.Diagnostics.Quitting.StoppingLaw.ContinuePrefixAtomAccess

/-!
# Continue-prefix access for counterexample stopping-law atoms

This adapter applies the generic finite-word Continue-through construction to
an atom exact-prefix chronology.  Mover-deleted survival tends to one along
that chronology, so its terminal atom alternative is eventually visible at
the front of the prefix.
-/

noncomputable section

namespace GameTheory

open Filter Math.Probability

variable {ι : Type} [Fintype ι] [DecidableEq ι]

namespace QuittingStoppingLawAtomExactPrefixChronology

/-- **Preemption-free atom access.**  Every atom exact-prefix chronology has
eventually positive atoms at its front after one legal Continue-through
deviation by the mover.  This conclusion does not require joint prescribed
survival and therefore also consumes the singleton-active preemption branch.
-/
theorem continuePrefix_atomAlternative_eventually
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {witness : QuittingTerminalExploitabilityWitness reward}
    {frontier : QuittingCounterexampleStoppingLawFrontier witness}
    (chronology : QuittingStoppingLawAtomExactPrefixChronology frontier) :
    ∀ᶠ rank in atTop,
      HasQuittingContinuePrefixDebtSlopeAtomAlternative reward
        (chronology.roots rank)
        (frontier.profiles (frontier.subseq rank)) chronology.mover.1
        chronology.observer
        (frontier.bestResponse chronology.mover (frontier.subseq rank))
        (chronology.charge / 2) := by
  have hsurvival := chronology.opponentSurvival_tendsto_one
    chronology.mover.2
  have hhalf : ∀ᶠ rank in atTop, 1 / 2 ≤
      quittingLiteralRootStackOpponentSurvival
        (chronology.roots rank) chronology.mover.1 :=
    hsurvival.eventually (Ioi_mem_nhds (show (1 / 2 : ℝ) < 1 by norm_num)) |>.mono
      fun _ h => h.le
  filter_upwards [chronology.atom_eventually, hhalf] with rank hatom hsurvivalRank
  exact hasQuittingContinuePrefixDebtSlopeAtomAlternative_of_halfSurvival
    reward (chronology.roots rank)
      (frontier.profiles (frontier.subseq rank)) chronology.mover.1
      chronology.observer
      (frontier.bestResponse chronology.mover (frontier.subseq rank))
      chronology.charge_pos.le hsurvivalRank hatom

/-- Explicit singleton-active specialization: the unique active owner is the
mover of the accessed atom, so all possible owner preemption is removed by
the same legal Continue-through deviation. -/
theorem singletonActive_continuePrefix_atomAlternative_eventually
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {witness : QuittingTerminalExploitabilityWitness reward}
    {frontier : QuittingCounterexampleStoppingLawFrontier witness}
    (chronology : QuittingStoppingLawAtomExactPrefixChronology frontier)
    (owner : ι) (hactive : frontier.active = {owner}) :
    chronology.mover.1 = owner ∧
      ∀ᶠ rank in atTop,
        HasQuittingContinuePrefixDebtSlopeAtomAlternative reward
          (chronology.roots rank)
          (frontier.profiles (frontier.subseq rank)) owner
          chronology.observer
          (frontier.bestResponse chronology.mover (frontier.subseq rank))
          (chronology.charge / 2) := by
  have hmover : chronology.mover.1 = owner := by
    simpa [hactive] using chronology.mover.2
  subst owner
  exact ⟨rfl, chronology.continuePrefix_atomAlternative_eventually⟩

end QuittingStoppingLawAtomExactPrefixChronology

end GameTheory
