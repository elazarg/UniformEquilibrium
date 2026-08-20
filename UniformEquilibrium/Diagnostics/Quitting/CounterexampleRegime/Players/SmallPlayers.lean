/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegime
import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegime.Toggles
import UniformEquilibrium.Quitting.Classification.OnePlayer.Existence
import UniformEquilibrium.Quitting.Classification.PlayerReindex
import UniformEquilibrium.Quitting.Classification.ThreePlayer.Existence
import UniformEquilibrium.Quitting.Classification.TwoPlayer.Existence

/-!
# Counterexample-regime exclusions at small player types

One-, two-, and three-player quitting games have unconditional production
existence theorems.  Together with the terminal-gap toggle restriction, they
force every counterexample regime to have at least four players.
-/

noncomputable section

namespace GameTheory
namespace QuittingCounterexampleRegime

open StochasticGame

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}

/-- The regime is empty over an empty player type: terminal exploitability
promises an improving player, but the type has none. -/
theorem elim_isEmpty [IsEmpty ι]
    (regime : QuittingCounterexampleRegime reward) : False := by
  obtain ⟨who, -, -⟩ :=
    regime.terminalExploitability fun i ↦ isEmptyElim i
  exact isEmptyElim who

/-- The regime is empty over any one-element player type. -/
theorem elim_unique [Unique ι]
    (regime : QuittingCounterexampleRegime reward) : False :=
  regime.not_exists_uniformEquilibriumPayoff
    (quittingGame_exists_uniformEquilibriumPayoff_onePlayer reward)

/-- The regime is empty over `Bool`. -/
theorem elim_twoPlayer
    {reward : {S : Finset Bool // S.Nonempty} → Payoff Bool}
    (regime : QuittingCounterexampleRegime reward) : False :=
  regime.not_exists_uniformEquilibriumPayoff
    (QuittingTwoPlayerExistence.quittingGame_exists_uniformEquilibriumPayoff_twoPlayer
      reward)

/-- The regime is empty over `Fin 3`. -/
theorem elim_threePlayer
    {reward : {S : Finset (Fin 3) // S.Nonempty} → Payoff (Fin 3)}
    (regime : QuittingCounterexampleRegime reward) : False :=
  regime.not_exists_uniformEquilibriumPayoff
    (quittingGame_exists_uniformEquilibriumPayoff_threePlayer reward)

/-- Any counterexample has at least four players. -/
theorem three_lt_card (regime : QuittingCounterexampleRegime reward) :
    3 < Fintype.card ι := by
  by_contra hle
  rw [not_lt] at hle
  have htwo := regime.one_lt_card
  have hcase : Fintype.card ι = 2 ∨ Fintype.card ι = 3 := by omega
  rcases hcase with hcard | hcard
  · exact regime.not_exists_uniformEquilibriumPayoff
      (quittingGame_exists_uniformEquilibriumPayoff_of_card_eq_two
        hcard reward)
  · exact regime.not_exists_uniformEquilibriumPayoff
      (quittingGame_exists_uniformEquilibriumPayoff_of_card_eq_three
        hcard reward)

end QuittingCounterexampleRegime
end GameTheory
