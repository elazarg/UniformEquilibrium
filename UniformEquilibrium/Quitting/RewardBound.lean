/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.Models.Quitting.Game

/-!
# Canonical finite reward bounds for quitting games

The terminal reward table of a finite quitting game is finite.  This module
packages the corresponding canonical bound so callers do not have to carry a
manually chosen bound and coordinatewise reward hypotheses.
-/

noncomputable section

namespace GameTheory

open StochasticGame
open scoped BigOperators

variable {ι : Type} [Fintype ι]

/-- A canonical finite bound for every coordinate of a quitting payoff
table. The sum form also controls finite row and subtable totals without
introducing additional cardinality factors. -/
def quittingRewardBound
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) : ℝ :=
  ∑ terminal, ∑ who, |reward terminal who|

/-- The canonical quitting reward bound is nonnegative. -/
theorem quittingRewardBound_nonneg
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) :
    0 ≤ quittingRewardBound reward := by
  unfold quittingRewardBound
  positivity

/-- Every terminal reward coordinate is below the canonical finite bound. -/
theorem abs_reward_le_quittingRewardBound
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (terminal : {S : Finset ι // S.Nonempty}) (who : ι) :
    |reward terminal who| ≤ quittingRewardBound reward := by
  unfold quittingRewardBound
  have hcoordinate : |reward terminal who| ≤
      ∑ player, |reward terminal player| := by
    exact Finset.single_le_sum
      (fun player _ ↦ abs_nonneg (reward terminal player))
      (Finset.mem_univ who)
  have hterminal : (∑ player, |reward terminal player|) ≤
      ∑ target, ∑ player, |reward target player| := by
    exact Finset.single_le_sum
      (fun target _ ↦ Finset.sum_nonneg fun player _ ↦
        abs_nonneg (reward target player))
      (Finset.mem_univ terminal)
  exact hcoordinate.trans hterminal

/-- Every finite quitting reward table admits a nonnegative coordinate bound. -/
theorem exists_quittingRewardBound
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ terminal who, |reward terminal who| ≤ M :=
  ⟨quittingRewardBound reward, quittingRewardBound_nonneg reward,
    abs_reward_le_quittingRewardBound reward⟩

end GameTheory
