/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import MathUE.SurvivalSegmentBalance
import UniformEquilibrium.Quitting.Cycles.SoloPeriodicBlockCompiler

/-!
# The inter-visit balance of a single-quitter periodic schedule

The single-quitter periodic compiler of
`UniformEquilibrium/Quitting/Cycles/SoloPeriodicBlockCompiler.lean` indexes
phases by `Fin (n + 1)` and schedules one player per phase, so the same player
may be scheduled at several phases — a *multi-visit* schedule.  This module
records the screen those schedules face and single-visit ones do not.

Between two of its own visits a scheduled player is a spectator, and its
displayed value obeys the two-term recursion of the compiler at every
intermediate phase.  Its own indifference at each visit pins the value at both
ends of the segment to the same number, its own solo reward.  Unrolling the
segment therefore equates that number with a convex combination of itself and
the solo rewards the player collects from the intermediate quitters, and the
weights of that combination sum to one.  What is left is a weighted sum of
*margins* — each the solo reward of an intermediate quitter minus the player's
own — equal to zero, with strictly positive weights whenever the intermediate
hazards are interior.

So the margins a player sees strictly between two of its own visits are either
all zero, or include both a positive and a negative one.  The segment of
length one is the special case that a gap-two revisit forces a zero margin.

The balance and the sign screen themselves are game-independent and live in
`MathUE/SurvivalSegmentBalance.lean`, over the unrolling of
`MathUE/CyclicMaxAffineBound.lean`.  What this module supplies is the reading:
which certificate obligations make a segment of a periodic schedule satisfy
their hypotheses.

Nothing here is specific to a rotation-symmetric table: the margin is read off
the solo rows directly.  For a table with circulant singleton rows the margin
at an intermediate phase is the circulant margin at the distance from the
spectator to that phase's quitter.

## Main definitions

* `segmentPhase` — the phase index `k + 1 + t` of a segment, clamped

## Main results

* `interVisitBalance_of_isSoloPeriodicCertificate` — the balance read off a
  certificate of the single-quitter periodic compiler
* `interVisitScreen_of_isSoloPeriodicCertificate` — and the screen it implies
-/

noncomputable section

namespace GameTheory
namespace SoloPeriodicInterVisitBalance

open Math.Probability Math.CyclicMaxAffine SoloPeriodicBlockCompiler

/-! ## Reading a segment off a periodic certificate -/

variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ℕ}
  {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
  {w : Fin (n + 1) → ι} {marginal : Fin (n + 1) → PMF Bool}
  {value : Fin (n + 2) → Payoff ι}

/-- The phase `k + 1 + t` of a segment starting after phase `k`, clamped to
the last phase so as to be defined for every natural `t`. -/
def segmentPhase (n k t : ℕ) : Fin (n + 1) := ⟨min (k + 1 + t) n, by omega⟩

theorem segmentPhase_val {n k t : ℕ} (h : k + 1 + t ≤ n) :
    (segmentPhase n k t : ℕ) = k + 1 + t := by
  rw [segmentPhase]
  exact min_eq_left h

theorem succ_segmentPhase {n k t : ℕ} (h : k + 1 + (t + 1) ≤ n) :
    Fin.succ (segmentPhase n k t) = Fin.castSucc (segmentPhase n k (t + 1)) := by
  refine Fin.ext ?_
  rw [Fin.val_succ, Fin.val_castSucc, segmentPhase_val (by omega),
    segmentPhase_val h]
  omega

/-- The two Boolean masses of a phase sum to one. -/
theorem quit_add_continue (μ : PMF Bool) : (μ true).toReal + (μ false).toReal = 1 := by
  simpa [Fintype.sum_bool, add_comm] using pmf_toReal_sum_one μ

/-- The two Boolean masses of a phase sum to one, continuation first. -/
theorem continue_add_quit (μ : PMF Bool) : (μ false).toReal + (μ true).toReal = 1 := by
  rw [add_comm]
  exact quit_add_continue μ

/-- **The inter-visit balance of a certified periodic schedule.**  If the
player `y` is scheduled at phase `k` and again at phase `k + 1 + L`, the
margins it collects at the `L` phases in between are weighted to zero.

Both ends of the segment are pinned to `y`'s own solo reward: the anchor at
phase `k` gives it directly, and at phase `k + 1 + L` the value recursion
mixes `y`'s own solo reward with the anchor's value, both equal to it. -/
theorem interVisitBalance_of_isSoloPeriodicCertificate
    (hcert : IsSoloPeriodicCertificate reward w marginal value)
    {y : ι} {k L : ℕ} (hk : k + 1 + L ≤ n)
    (hfirst : w ⟨k, by omega⟩ = y)
    (hsecond : w ⟨k + 1 + L, by omega⟩ = y) :
    ∑ t ∈ Finset.range L,
        survivalProduct (fun u ↦ (marginal (segmentPhase n k u) false).toReal) t *
            (marginal (segmentPhase n k t) true).toReal *
            (reward (quittingSingletonTerminal (w (segmentPhase n k t))) y -
              reward (quittingSingletonTerminal y) y) = 0 := by
  refine Math.sum_survivalProduct_mul_deviation_eq_zero
    (V := fun t ↦ value (Fin.castSucc (segmentPhase n k t)) y)
    (R := reward (quittingSingletonTerminal y) y)
    (fun t ↦ quit_add_continue (marginal (segmentPhase n k t))) ?_ ?_ ?_
  · intro t ht
    have hnext : Fin.succ (segmentPhase n k t) =
        Fin.castSucc (segmentPhase n k (t + 1)) := succ_segmentPhase (by omega)
    rw [hcert.succ (segmentPhase n k t) y, hnext]
  · have hphase : Fin.castSucc (segmentPhase n k 0) =
        Fin.succ (⟨k, by omega⟩ : Fin (n + 1)) := by
      refine Fin.ext ?_
      rw [Fin.val_castSucc, Fin.val_succ, segmentPhase_val (by omega)]
    have hanchor := hcert.anchor (⟨k, by omega⟩ : Fin (n + 1))
    rw [hfirst] at hanchor
    show value (Fin.castSucc (segmentPhase n k 0)) y = _
    rw [hphase]
    exact hanchor.symm
  · have hphase : segmentPhase n k L = (⟨k + 1 + L, by omega⟩ : Fin (n + 1)) :=
      Fin.ext (segmentPhase_val hk)
    have hanchor := hcert.anchor (⟨k + 1 + L, by omega⟩ : Fin (n + 1))
    rw [hsecond] at hanchor
    show value (Fin.castSucc (segmentPhase n k L)) y = _
    rw [hphase, hcert.succ (⟨k + 1 + L, by omega⟩ : Fin (n + 1)) y, hsecond,
      ← hanchor, ← add_mul, quit_add_continue, one_mul]

/-- **The screen on a certified periodic schedule.**  Between two visits of
the same player, at interior hazards, the margins it collects cannot be all of
one sign unless they all vanish. -/
theorem interVisitScreen_of_isSoloPeriodicCertificate
    (hcert : IsSoloPeriodicCertificate reward w marginal value)
    {y : ι} {k L : ℕ} (hk : k + 1 + L ≤ n)
    (hfirst : w ⟨k, by omega⟩ = y)
    (hsecond : w ⟨k + 1 + L, by omega⟩ = y)
    (hquit : ∀ t, t < L → 0 < (marginal (segmentPhase n k t) true).toReal)
    (hcontinue : ∀ t, t < L → 0 < (marginal (segmentPhase n k t) false).toReal)
    {t₀ : ℕ} (ht₀ : t₀ < L)
    (hne : reward (quittingSingletonTerminal (w (segmentPhase n k t₀))) y ≠
      reward (quittingSingletonTerminal y) y) :
    (∃ t, t < L ∧ reward (quittingSingletonTerminal y) y <
        reward (quittingSingletonTerminal (w (segmentPhase n k t))) y) ∧
      (∃ t, t < L ∧ reward (quittingSingletonTerminal (w (segmentPhase n k t))) y <
        reward (quittingSingletonTerminal y) y) :=
  Math.exists_lt_and_exists_gt_of_segmentBalance hcontinue hquit
    (interVisitBalance_of_isSoloPeriodicCertificate hcert hk hfirst hsecond) ht₀ hne

end SoloPeriodicInterVisitBalance
end GameTheory
