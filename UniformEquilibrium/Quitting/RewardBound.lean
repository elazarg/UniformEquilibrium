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

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- A canonical finite bound for every coordinate of a quitting payoff
table.  The sum form avoids any nonempty maximum convention. -/
def quittingRewardBound
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) : ℝ :=
  ∑ S, ∑ who, |reward S who|

omit [DecidableEq ι] in
/-- The canonical quitting reward bound is nonnegative. -/
theorem quittingRewardBound_nonneg
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) :
    0 ≤ quittingRewardBound reward := by
  unfold quittingRewardBound
  positivity

omit [DecidableEq ι] in
/-- Every terminal reward coordinate is below the canonical finite bound. -/
theorem abs_reward_le_quittingRewardBound
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (terminal : {S : Finset ι // S.Nonempty}) (who : ι) :
    |reward terminal who| ≤ quittingRewardBound reward := by
  unfold quittingRewardBound
  have hcoordinate : |reward terminal who| ≤
      ∑ player, |reward terminal player| := by
    exact Finset.single_le_sum
      (fun player _ => abs_nonneg (reward terminal player))
      (Finset.mem_univ who)
  have hterminal : (∑ player, |reward terminal player|) ≤
      ∑ S, ∑ player, |reward S player| := by
    exact Finset.single_le_sum
      (fun S _ => Finset.sum_nonneg fun player _ =>
        abs_nonneg (reward S player))
      (Finset.mem_univ terminal)
  exact hcoordinate.trans hterminal

end GameTheory
