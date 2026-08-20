/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Punishment.ZeroSoloDisjunct
import UniformEquilibrium.Quitting.Punishment.OwnerSoloCertification
import UniformEquilibrium.Quitting.Stationary.SingletonStationaryRoot

/-!
# Uniform-equilibrium existence for one-player quitting games

For an arbitrary `Unique` player type, a nonpositive solo-quit reward is the
zero-solo branch and all-Continue delivers zero.  With a positive solo reward,
quitting surely is an owner-solo stationary equilibrium; every inactive-player
condition is vacuous.
-/

noncomputable section

namespace GameTheory

open StochasticGame

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- **Every one-player finite quitting game has a uniform-equilibrium
payoff.**  Stated for an arbitrary `Unique` player type.  If the single
player's solo-quit reward is nonpositive, the weight is zero-solo and the
all-continue profile delivers the zero vector.  Otherwise the player quits
surely: the owner-solo certification applies with the sure hazard, and its
inactive-player inequalities are vacuous because there is no other player. -/
theorem quittingGame_exists_uniformEquilibriumPayoff_onePlayer
    [Unique ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) :
    ∃ payoff : Payoff ι,
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff := by
  by_cases hsolo : quittingSoloReward reward default default ≤ 0
  · refine exists_uniformEquilibriumPayoff_of_zeroSolo reward ?_
    intro who
    rw [Unique.eq_default who]
    exact hsolo
  · rw [not_le] at hsolo
    exact ⟨quittingSoloReward reward default,
      isUniformEquilibriumPayoff_soloReward_of_inactive reward default
        (quittingHazardCoin 1 zero_le_one le_rfl)
        (by rw [quittingHazardCoin_true_toReal]; exact one_pos)
        hsolo.le
        (fun other hother ↦ absurd (Unique.eq_default other) hother)⟩

end GameTheory
