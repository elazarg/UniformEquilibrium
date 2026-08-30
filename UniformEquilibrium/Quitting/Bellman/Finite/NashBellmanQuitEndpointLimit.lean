/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Debt.Marked.FenceIteration
import UniformEquilibrium.Quitting.Bellman.Finite.NashBellmanValueConvergence
import UniformEquilibrium.Quitting.Paths.QuitEndpointOpponentBound

/-!
# Active Quit endpoints on a summable-clock Nash--Bellman spine

When a player has positive Quit probability at an exact Nash root, the
current prescribed value equals that player's pure-Quit endpoint.  The pure
Quit endpoint differs from the singleton reward only on the event that an
opponent also quits, so its distance from the singleton reward is at most
twice the payoff bound times opponent absorption.

Combining this estimate with convergence of the value coordinate and decay
of a summable opponent clock shows that a limiting value strictly above the
singleton reward forces the player's own Quit hazard to vanish eventually.
-/

noncomputable section

namespace GameTheory

open Filter Math.Probability

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- At an active own-Quit root of a canonical exact spine, the current value
is within the opponent-clock error of the singleton reward. -/
theorem IsCanonicalExactQuittingNashBellmanSpine.abs_value_sub_singleton_le_of_quit_pos
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (value : ℕ → Payoff ι) (roots : ℕ → ι → PMF Bool)
    (hspine : IsCanonicalExactQuittingNashBellmanSpine reward value roots)
    (who : ι) (time : ℕ)
    (hquit : 0 < (roots time who true).toReal) :
    |value time who - reward (quittingSingletonTerminal who) who| ≤
      2 * quittingRewardBound reward *
        quittingOpponentClockCharge roots who time := by
  have hendpoint :
      quittingRootQuitPayoff reward (value (time + 1))
          (roots time) who = value time who := by
    calc
      quittingRootQuitPayoff reward (value (time + 1))
          (roots time) who =
          quittingRootSuccessorPayoff reward (value (time + 1))
            (roots time) who :=
        quittingRootQuitPayoff_eq_successor_of_quitProbability_pos
          reward (value (time + 1)) (roots time) who
            (hspine.2.2 time) hquit
      _ = value time who := (congrFun (hspine.2.1 time) who).symm
  rw [← hendpoint]
  exact
    abs_quittingRootQuitPayoff_sub_singletonReward_le_two_mul_opponentAbsorptionMass
      reward (value (time + 1)) (roots time) who
      (quittingRewardBound reward)
      (abs_reward_le_quittingRewardBound reward)

/-- If the convergent owner value lies strictly above the singleton reward,
then summability of the opponent clock forces the owner's Quit probability
to be exactly zero from some time onward. -/
theorem IsCanonicalExactQuittingNashBellmanSpine.eventually_quit_eq_zero_of_tendsto_gt_singleton
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (value : ℕ → Payoff ι) (roots : ℕ → ι → PMF Bool)
    (hspine : IsCanonicalExactQuittingNashBellmanSpine reward value roots)
    (who : ι)
    (hclock : Summable (quittingOpponentClockCharge roots who))
    (limit : ℝ)
    (hvalue : Tendsto (fun time => value time who) atTop (nhds limit))
    (hstrict : reward (quittingSingletonTerminal who) who < limit) :
    ∀ᶠ time : ℕ in atTop, (roots time who true).toReal = 0 := by
  let singletonReward := reward (quittingSingletonTerminal who) who
  let midpoint := (limit + singletonReward) / 2
  have hmidpoint_lt_limit : midpoint < limit := by
    dsimp only [midpoint, singletonReward]
    linarith
  have hsingleton_lt_midpoint : singletonReward < midpoint := by
    dsimp only [midpoint, singletonReward]
    linarith
  have hvalueEventually : ∀ᶠ time : ℕ in atTop,
      midpoint < value time who :=
    hvalue.eventually (Ioi_mem_nhds hmidpoint_lt_limit)
  have hscaled : Tendsto (fun time =>
      2 * quittingRewardBound reward *
        quittingOpponentClockCharge roots who time) atTop (nhds 0) := by
    simpa using hclock.tendsto_atTop_zero.const_mul
      (2 * quittingRewardBound reward)
  have hgap : 0 < midpoint - singletonReward := sub_pos.mpr
    hsingleton_lt_midpoint
  have hclockEventually : ∀ᶠ time : ℕ in atTop,
      2 * quittingRewardBound reward *
          quittingOpponentClockCharge roots who time <
        midpoint - singletonReward :=
    hscaled.eventually (Iio_mem_nhds hgap)
  filter_upwards [hvalueEventually, hclockEventually] with time htime hcharge
  by_contra hne
  have hquit : 0 < (roots time who true).toReal :=
    lt_of_le_of_ne ENNReal.toReal_nonneg (Ne.symm hne)
  have hdistance :=
    hspine.abs_value_sub_singleton_le_of_quit_pos
      reward value roots who time hquit
  have hlower : midpoint - singletonReward <
      |value time who - singletonReward| := by
    exact (sub_lt_sub_right htime singletonReward).trans_le
      (le_abs_self (value time who - singletonReward))
  linarith

/-- A summable-clock coordinate admits a limit, and any such selected limit
strictly above the singleton reward has the eventual zero-own-hazard
property. -/
theorem IsCanonicalExactQuittingNashBellmanSpine.exists_valueLimit_eventually_zero_quit
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (value : ℕ → Payoff ι) (roots : ℕ → ι → PMF Bool)
    (hspine : IsCanonicalExactQuittingNashBellmanSpine reward value roots)
    (who : ι)
    (hclock : Summable (quittingOpponentClockCharge roots who)) :
    ∃ limit : ℝ,
      Tendsto (fun time => value time who) atTop (nhds limit) ∧
        (reward (quittingSingletonTerminal who) who < limit →
          ∀ᶠ time : ℕ in atTop, (roots time who true).toReal = 0) := by
  obtain ⟨limit, hlimit⟩ :=
    hspine.exists_tendsto_value_of_summableClock
      reward value roots who hclock
  exact ⟨limit, hlimit, fun hstrict =>
    hspine.eventually_quit_eq_zero_of_tendsto_gt_singleton
      reward value roots who hclock limit hlimit hstrict⟩

end GameTheory
