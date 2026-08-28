/-
Copyright (c) 2026 UniformEquilibrium contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: UniformEquilibrium contributors
-/

import Research.Quitting.FiniteDeadlineProjectiveCompatibility

/-!
# Vanishing adjacent distance along a selected family of deadlines

A selected family of consecutive finite-deadline timing Nash pairs whose
adjacent marginal total-variation distances tend to zero realizes terminal
approximate Nash profiles whose errors tend to zero.  If the prescribed
terminal payoffs of those realizations also converge, their limit is a
uniform-equilibrium payoff.

The realized error is `4 * bound` times the adjacent distance, which bounds
unrestricted behavioral semantic debt.  It is not the deadline escape charge
of `quittingFiniteDeadlineEscapeCharge`, which retains an opponent-survival
factor that adjacent distance does not control.
-/

noncomputable section

namespace GameTheory

open Filter Math.Probability

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- **Vanishing-distance consumer with an identified target.**  Consecutive
finite-deadline timing Nash pairs whose adjacent distances tend to zero, and
whose realized prescribed payoffs tend to one target, make that target a
uniform-equilibrium payoff.  The indexing filter is arbitrary, so the selected
deadlines need not be cofinal in the natural numbers. -/
theorem quittingGame_isUniformEquilibriumPayoff_of_adjacentTV_tendsto
    {index : Type} {filter : Filter index} [filter.NeBot]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (target : Payoff ι)
    (deadlines : index → ℕ)
    (old : ∀ n, ι → PMF (QuittingFiniteDeadlineTimingAction (deadlines n)))
    (new : ∀ n, ι → PMF (QuittingFiniteDeadlineTimingAction (deadlines n + 1)))
    (holdNash : ∀ n, (quittingFiniteDeadlineTimingGame reward
      (deadlines n)).mixedExtension.IsNash (old n))
    (hnewNash : ∀ n, (quittingFiniteDeadlineTimingGame reward
      (deadlines n + 1)).mixedExtension.IsNash (new n))
    {bound : ℝ} (hbound : 0 ≤ bound)
    (hreward : ∀ terminal player, |reward terminal player| ≤ bound)
    (hdistance : Tendsto (fun n =>
      quittingFiniteDeadlineAdjacentTV (deadlines n) (old n) (new n))
      filter (nhds 0))
    (htarget : Tendsto (fun n => quittingTerminalPayoff reward
        (quittingFiniteDeadlineTimingProfile reward (deadlines n) (old n)))
      filter (nhds target)) :
    (quittingGame reward).IsUniformEquilibriumPayoff none target := by
  apply quittingGame_isUniformEquilibriumPayoff_of_terminalNash_tendsto
    reward target
    (fun n => 4 * bound *
      quittingFiniteDeadlineAdjacentTV (deadlines n) (old n) (new n))
    (fun n => quittingFiniteDeadlineTimingProfile reward (deadlines n) (old n))
  · simpa only [mul_zero] using
      (tendsto_const_nhds (x := 4 * bound) (f := filter)).mul hdistance
  · refine Filter.Frequently.of_forall fun n => ?_
    exact quittingFiniteDeadlineTimingProfile_isεAsymptoticNash_of_adjacentTV
      reward (deadlines n) (old n) (new n) (holdNash n) (hnewNash n)
      hbound hreward le_rfl
  · exact htarget

/-- Sequential form along deadlines escaping to infinity.  Cofinality of the
selected deadlines is recorded but unused: the estimate at each selected pair
is already uniform in the deadline. -/
theorem quittingGame_isUniformEquilibriumPayoff_of_adjacentTV_tendsto_atTop
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (target : Payoff ι)
    (deadlines : ℕ → ℕ)
    (_hcofinal : Tendsto deadlines atTop atTop)
    (old : ∀ n, ι → PMF (QuittingFiniteDeadlineTimingAction (deadlines n)))
    (new : ∀ n, ι → PMF (QuittingFiniteDeadlineTimingAction (deadlines n + 1)))
    (holdNash : ∀ n, (quittingFiniteDeadlineTimingGame reward
      (deadlines n)).mixedExtension.IsNash (old n))
    (hnewNash : ∀ n, (quittingFiniteDeadlineTimingGame reward
      (deadlines n + 1)).mixedExtension.IsNash (new n))
    {bound : ℝ} (hbound : 0 ≤ bound)
    (hreward : ∀ terminal player, |reward terminal player| ≤ bound)
    (hdistance : Tendsto (fun n =>
      quittingFiniteDeadlineAdjacentTV (deadlines n) (old n) (new n))
      atTop (nhds 0))
    (htarget : Tendsto (fun n => quittingTerminalPayoff reward
        (quittingFiniteDeadlineTimingProfile reward (deadlines n) (old n)))
      atTop (nhds target)) :
    (quittingGame reward).IsUniformEquilibriumPayoff none target :=
  quittingGame_isUniformEquilibriumPayoff_of_adjacentTV_tendsto
    reward target deadlines old new holdNash hnewNash hbound hreward
    hdistance htarget

end GameTheory
