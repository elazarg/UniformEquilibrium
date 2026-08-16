/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Classification.ThreePlayer.SingletonMixtureCompiler
import UniformEquilibrium.Quitting.Stationary.MinMax

/-!
# Charge-normalized tangent data for quitting games

This module owns the reusable data carried by a first-order boundary blow-up:
singleton-owner occupation, a common boundary payoff, and displacement per unit
absorbed mass.  It makes no counterexample or tail-extraction assumption.
-/

namespace GameTheory

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- First-order boundary data normalized by a positive absorption charge. -/
structure QuittingChargeTangentData
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) where
  /-- Conditional singleton owner occupation. -/
  mass : ι → ℝ
  /-- Common boundary payoff. -/
  boundary : Payoff ι
  /-- Endpoint displacement per unit absorbed mass. -/
  tangent : Payoff ι
  mass_nonneg : ∀ owner, 0 ≤ mass owner
  mass_sum : ∑ owner, mass owner = 1
  tangent_eq : ∀ who,
    tangent who = quittingSingletonMixture reward mass who - boundary who
  solo_le_boundary : ∀ who,
    reward (quittingSingletonTerminal who) who ≤ boundary who
  punishment_le_boundary : ∀ who,
    quittingPunishmentValue reward who ≤ boundary who
  positive_mass_pins_boundary : ∀ owner, 0 < mass owner →
    boundary owner = reward (quittingSingletonTerminal owner) owner

/-- Charge-normalized tangent data with genuine nonzero motion. -/
structure QuittingChargeTangentPacket
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    extends QuittingChargeTangentData reward where
  tangent_ne_zero : tangent ≠ 0

end GameTheory
