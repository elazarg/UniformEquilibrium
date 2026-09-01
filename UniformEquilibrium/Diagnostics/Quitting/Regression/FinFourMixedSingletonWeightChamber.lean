/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticNonnegativeWeightChamber

/-!
# A mixed-singleton chamber beyond subset indicators

This concrete four-player reward table is closed by the nonnegative weight
`(1,2,3,4)`, while every equal-weight test on a player subset of cardinality
at least two fails on that subset's own terminal coalition.
-/

noncomputable section

namespace GameTheory

/-- Strictly increasing positive player weights `(1,2,3,4)`. -/
def finFourMixedSingletonWeight (player : Fin 4) : ℝ := player.val + 1

/-- The mixed singleton vector `(1,-1/2,0,0)`. -/
def finFourMixedSingletonVector (player : Fin 4) : ℝ :=
  if player = 0 then 1 else if player = 1 then -(1 / 2) else 0

/-- Least-weight member of a nonempty coalition. -/
def finFourMixedSingletonLow
    (terminal : {S : Finset (Fin 4) // S.Nonempty}) : Fin 4 :=
  if 0 ∈ terminal.val then 0
  else if 1 ∈ terminal.val then 1
  else if 2 ∈ terminal.val then 2
  else 3

/-- Greatest-weight member of a nonempty coalition. -/
def finFourMixedSingletonHigh
    (terminal : {S : Finset (Fin 4) // S.Nonempty}) : Fin 4 :=
  if 3 ∈ terminal.val then 3
  else if 2 ∈ terminal.val then 2
  else if 1 ∈ terminal.val then 1
  else 0

/-- Singleton coalitions receive the full mixed singleton vector.  At a
nonsingleton coalition, the least and greatest weight coordinates receive
the opposite weight increments and every other increment is zero. -/
def finFourMixedSingletonReward
    (terminal : {S : Finset (Fin 4) // S.Nonempty}) : Payoff (Fin 4) :=
  fun player =>
    finFourMixedSingletonVector player +
      if terminal.val.card = 1 then 0
      else if player = finFourMixedSingletonLow terminal then
        finFourMixedSingletonWeight (finFourMixedSingletonHigh terminal)
      else if player = finFourMixedSingletonHigh terminal then
        -finFourMixedSingletonWeight (finFourMixedSingletonLow terminal)
      else 0

/-- The table's own singleton rewards are exactly the displayed mixed
singleton vector. -/
theorem finFourMixedSingletonReward_singleton
    (player : Fin 4) :
    finFourMixedSingletonReward (quittingSingletonTerminal player) player =
      finFourMixedSingletonVector player := by
  simp [finFourMixedSingletonReward, quittingSingletonTerminal]

/-- The chosen weight annihilates the weighted singleton vector. -/
theorem finFourMixedSingleton_weightedSingleton_eq_zero :
    quittingWeightedSingletonReward finFourMixedSingletonReward
      finFourMixedSingletonWeight = 0 := by
  unfold quittingWeightedSingletonReward
  simp_rw [finFourMixedSingletonReward_singleton]
  simp +decide [finFourMixedSingletonWeight, finFourMixedSingletonVector,
    Fin.sum_univ_four]
  norm_num

/-- Every finite terminal has the same zero weighted value. -/
theorem finFourMixedSingleton_weightedTerminal_eq_zero
    (terminal : {S : Finset (Fin 4) // S.Nonempty}) :
    quittingWeightedTerminalOutcomeReward finFourMixedSingletonReward
      finFourMixedSingletonWeight (some terminal) = 0 := by
  fin_cases terminal
  all_goals simp +decide [quittingWeightedTerminalOutcomeReward,
      quittingTerminalOutcomeReward, finFourMixedSingletonReward,
      finFourMixedSingletonWeight, finFourMixedSingletonVector,
      finFourMixedSingletonLow, finFourMixedSingletonHigh,
      Fin.sum_univ_four]
  all_goals norm_num

/-- Every equal-weight test on a player subset of cardinality at least two
fails at that subset's own terminal coalition. -/
theorem finFourMixedSingleton_subsetIndicator_fails
    (players : Finset (Fin 4)) (hcard : 1 < players.card) :
    (∑ player ∈ players,
        finFourMixedSingletonVector player) <
      ∑ player ∈ players,
        finFourMixedSingletonReward ⟨players,
          Finset.card_pos.mp (lt_trans Nat.zero_lt_one hcard)⟩ player := by
  fin_cases players
  all_goals simp +decide [finFourMixedSingletonReward,
      finFourMixedSingletonWeight,
      finFourMixedSingletonVector, finFourMixedSingletonLow,
      finFourMixedSingletonHigh] at hcard ⊢
  all_goals norm_num at hcard ⊢

/-- The arbitrary nonnegative-weight chamber closes the concrete table and
produces a uniform-equilibrium payoff against unrestricted behavioral
deviations. -/
theorem exists_uniformEquilibriumPayoff_finFourMixedSingletonReward :
    ∃ payoff : Payoff (Fin 4),
      (quittingGame finFourMixedSingletonReward).IsUniformEquilibriumPayoff
        none payoff := by
  apply exists_uniformEquilibriumPayoff_of_nonnegativeWeightChamber
    finFourMixedSingletonWeight 0 1 (by norm_num)
  · intro player
    unfold finFourMixedSingletonWeight
    positivity
  · norm_num [finFourMixedSingletonWeight]
  · norm_num [finFourMixedSingletonWeight]
  · rw [finFourMixedSingleton_weightedSingleton_eq_zero]
  · intro terminal
    rw [finFourMixedSingleton_weightedTerminal_eq_zero,
      finFourMixedSingleton_weightedSingleton_eq_zero]

end GameTheory
