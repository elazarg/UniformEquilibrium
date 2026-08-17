/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegime.Players.SmallPlayers
import UniformEquilibrium.Quitting.Classification.BlockDeletion
import UniformEquilibrium.Quitting.Classification.PlayerReindex

/-!
# Block deletion down to at most three survivors

`UniformEquilibrium/Quitting/Classification/BlockDeletion.lean` produces a
uniform-equilibrium payoff of the original game from one of the survivor game,
provided every deleted player passes the block dispensability gate.  Here the
survivor game is solved outright rather than assumed: at most three players
carry the unconditional one-, two-, and three-player existence theorems, and
the empty player type is excluded by
`QuittingCounterexampleRegime.elim_isEmpty`.

The resulting producer
`quittingGame_exists_uniformEquilibriumPayoff_of_blockDispensable_card_le_three`
uses no minimality or induction hypothesis, so its contrapositive
`exists_not_blockDispensable_of_not_exists_uniformEquilibriumPayoff` is a
necessary condition on any table with no uniform-equilibrium payoff, at every
block leaving at most three survivors.
-/

noncomputable section

namespace GameTheory

open StochasticGame

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-! ## The unconditional small-survivor producer -/

/-- Every finite quitting game with at most three players has a
uniform-equilibrium payoff.  This collects the unconditional one-, two-, and
three-player existence theorems and the empty player type. -/
theorem quittingGame_exists_uniformEquilibriumPayoff_of_card_le_three
    {κ : Type} [Fintype κ] [DecidableEq κ] (hcard : Fintype.card κ ≤ 3)
    (reward : {S : Finset κ // S.Nonempty} → Payoff κ) :
    ∃ payoff : Payoff κ,
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff := by
  interval_cases hcase : Fintype.card κ
  · letI : IsEmpty κ := Fintype.card_eq_zero_iff.mp hcase
    by_contra hno
    obtain ⟨regime⟩ :=
      (not_exists_uniformEquilibriumPayoff_iff_nonempty_counterexampleRegime
        reward).1 hno
    exact QuittingCounterexampleRegime.elim_isEmpty regime
  · letI : Unique κ := (Fintype.card_eq_one_iff_nonempty_unique.mp hcase).some
    exact quittingGame_exists_uniformEquilibriumPayoff_onePlayer reward
  · exact quittingGame_exists_uniformEquilibriumPayoff_of_card_eq_two hcase reward
  · exact quittingGame_exists_uniformEquilibriumPayoff_of_card_eq_three hcase reward

/-- **The unconditional small-survivor producer.**  At any player count, a
finite quitting game whose players outside a block of at most three survivors
all pass the block gate has a uniform-equilibrium payoff.  No minimality or
induction hypothesis is used: the survivor game is solved outright by the
small-cardinality existence theorems. -/
theorem quittingGame_exists_uniformEquilibriumPayoff_of_blockDispensable_card_le_three
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (B : Finset ι)
    (hgate : ∀ d ∈ B, QuittingBlockDispensable reward B d)
    (hcard : Fintype.card (QuittingBlockSurvivor B) ≤ 3) :
    ∃ payoff : Payoff ι,
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff :=
  quittingGame_exists_uniformEquilibriumPayoff_of_blockDispensable reward B hgate
    (quittingGame_exists_uniformEquilibriumPayoff_of_card_le_three hcard
      (quittingDeleteBlockReward reward B))

/-- **The minimal-counterexample necessary condition.**  A finite quitting
game with no uniform-equilibrium payoff has, for every block whose survivors
number at most three, a member of that block failing the gate.  The statement
carries no minimality hypothesis. -/
theorem exists_not_blockDispensable_of_not_exists_uniformEquilibriumPayoff
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hno : ¬ ∃ payoff : Payoff ι,
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff)
    (B : Finset ι) (hcard : Fintype.card (QuittingBlockSurvivor B) ≤ 3) :
    ∃ d ∈ B, ¬ QuittingBlockDispensable reward B d := by
  by_contra hall
  push Not at hall
  exact hno
    (quittingGame_exists_uniformEquilibriumPayoff_of_blockDispensable_card_le_three
      reward B hall hcard)


end GameTheory
