/-
Copyright (c) 2026 UniformEquilibrium contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: UniformEquilibrium contributors
-/

import MathUE.RenewedChargedPathPotentialRecharge
import UniformEquilibrium.Diagnostics.Quitting.FinFourUnboundedExactBlockHazardCapacity
import UniformEquilibrium.Quitting.Bellman.Finite.FullBoxExactPredecessorAbsorptionBudget

/-!
# Fin4 full-box exact-predecessor capacity

If a four-player quitting game has no uniform-equilibrium payoff, the checked
finite exact-block marginal-hazard bound yields a finite joint-absorption
budget on the full canonical boxed predecessor relation.  Its budget-to-go is
therefore a bounded potential.

A supplied renewed sequence of positively charged exact-predecessor paths
must restore this potential at a linear rate across its horizontal moves.
The sequence interface stores the horizontal target and its literal equality
with the next source.  This module does not construct such a sequence or make
the horizontal moves admissible predecessor edges.
-/

noncomputable section

namespace GameTheory

open Math.ChargedPathBudget
open scoped BigOperators

/-- In a Fin4 game without a uniform-equilibrium payoff, every finite path in
the full canonical boxed exact-predecessor relation has one common
joint-absorption charge bound. -/
theorem finFour_quittingFullBoxExactPredecessor_hasFiniteBudget_of_no_uniformPayoff
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (hnot : ¬ ∃ payoff : Payoff (Fin 4),
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff) :
    (quittingPunishmentFloorBoxChargedRelation reward).HasFiniteBudget := by
  exact quittingFullBoxExactPredecessor_hasFiniteBudget_of_boundedHazardCapacity
    (finFour_hasBoundedFiniteExactNashBellmanHazardCapacity_of_no_uniformPayoff
      reward hnot)

/-- The canonical full-box budget-to-go is a bounded potential in every
Fin4 game without a uniform-equilibrium payoff. -/
theorem finFour_quittingFullBoxExactPredecessor_value_isBoundedPotential_of_no_uniformPayoff
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (hnot : ¬ ∃ payoff : Payoff (Fin 4),
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff) :
    (quittingPunishmentFloorBoxChargedRelation reward).IsBoundedPotential
      (quittingPunishmentFloorBoxChargedRelation reward).value := by
  exact quittingFullBoxExactPredecessor_value_isBoundedPotential_of_boundedHazardCapacity
    (finFour_hasBoundedFiniteExactNashBellmanHazardCapacity_of_no_uniformPayoff
      reward hnot)

/-- Every supplied positively charged renewed Fin4 predecessor sequence
restores the canonical full-box capacity at least linearly, up to the one
global path-budget boundary term. -/
theorem finFour_card_mul_minimumCharge_sub_fullBoxBudget_le_sum_valueRecharge
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (hnot : ¬ ∃ payoff : Payoff (Fin 4),
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff)
    (sequence :
      (quittingPunishmentFloorBoxChargedRelation reward).RenewedPathSequence)
    (horizon : ℕ) :
    (horizon : ℝ) * sequence.minimumCharge -
        (quittingPunishmentFloorBoxChargedRelation reward).budget ≤
      ∑ phase ∈ Finset.range horizon,
        sequence.potentialRecharge
          (quittingPunishmentFloorBoxChargedRelation reward).value phase := by
  exact sequence.card_mul_minimumCharge_sub_budget_le_sum_valueRecharge
    (finFour_quittingFullBoxExactPredecessor_hasFiniteBudget_of_no_uniformPayoff
      reward hnot) horizon

end GameTheory
