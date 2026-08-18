/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Bellman.Finite.BellmanTelescope
import UniformEquilibrium.Quitting.Cycles.InfinitePureTimeExtremality

/-!
# A Bellman supersolution dominates every deterministic stop

`IsQuittingLiveBellmanSupersolution` asks a sequence to sit above the one-stage
Bellman value along a live path.  This file proves the supersolution half of
optimal stopping for that predicate: against a fixed sequence of opponent
roots, the terminal value of any deterministic quit time never exceeds the
supersolution read at the starting stage.

The proof is a bare induction on the remaining fuel.  It uses no contraction,
no periodicity, and no exactness of the prescribed roots, so it applies to every
root sequence a stopping argument may present.

This module exists because the statement pairs
`IsQuittingLiveBellmanSupersolution` with the deterministic-stop evaluator
`quittingRootSequencePureTimeTerminalValue`, which are introduced in modules
neither of which imports the other.

## Main results

* `quittingRootSequencePureTimeTerminalValue_le_of_bellmanSupersolution` — a
  supersolution dominates every deterministic stop
-/

noncomputable section

namespace GameTheory

open Math.Probability

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- **A Bellman supersolution dominates every deterministic stop.**  This is
the supersolution half of the optimal-stopping identification: it needs no
contraction, no periodicity, no exactness of the prescribed root, and no
Bellman equality. -/
theorem quittingRootSequencePureTimeTerminalValue_le_of_bellmanSupersolution
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι) (cap : ℕ → ℝ)
    (hcap : IsQuittingLiveBellmanSupersolution reward roots who cap)
    (start fuel : ℕ) :
    quittingRootSequencePureTimeTerminalValue reward roots who
        (some (start + fuel)) start ≤ cap start := by
  induction fuel generalizing start with
  | zero =>
      rw [Nat.add_zero,
        quittingRootSequencePureTimeTerminalValue_some_self_eq_fixedOpponents]
      have hstep := hcap start
      rw [quittingLiveBellmanValue] at hstep
      exact le_trans (le_max_left _ _) hstep
  | succ fuel ih =>
      have hne : start ≠ start + (fuel + 1) := by omega
      have hidx : start + (fuel + 1) = start + 1 + fuel := by omega
      have htail : quittingRootSequenceHazardTerminalValue reward roots who
          (quittingPureTimeHazard (some (start + (fuel + 1)))) (start + 1) ≤
          cap (start + 1) := by
        simpa only [quittingRootSequencePureTimeTerminalValue, hidx]
          using ih (start + 1)
      have hmass : 0 ≤ quittingFixedOpponentsContinueMass roots who start :=
        quittingStationaryContinueMass_nonneg
          (Function.update (roots start) who (PMF.pure false))
      have hstep := hcap start
      rw [quittingLiveBellmanValue] at hstep
      have hcontinue := le_trans (le_max_right
        (quittingFixedOpponentsQuitValue reward roots who start)
        (quittingFixedOpponentsContinueReward reward roots who start +
          quittingFixedOpponentsContinueMass roots who start * cap (start + 1)))
        hstep
      unfold quittingRootSequencePureTimeTerminalValue
      rw [quittingRootSequenceHazardTerminalValue_eq_hazardBellman,
        quittingPureTimeHazard_some_of_ne hne]
      simp only [PMF.pure_apply, if_neg (by decide : (true : Bool) ≠ false),
        ENNReal.toReal_zero, if_true, ENNReal.toReal_one, zero_mul, one_mul]
      have hscaled := mul_le_mul_of_nonneg_left htail hmass
      linarith

end GameTheory
