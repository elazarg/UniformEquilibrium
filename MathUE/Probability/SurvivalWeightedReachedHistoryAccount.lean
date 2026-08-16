/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Interval
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# A game-free reached-history debt account

This file isolates the algebra behind survival-weighted localization.  A debt
process obeys the exact one-step account

`debt t = defect t + survival t * debt (t + 1)`.

The recursively accumulated reach weight turns this into an exact finite
telescope.  Nonnegative defects and terminal debt then localize every marked
event: event mass times the defect at its reached row is already bounded by
the initial debt.

There is no game-theoretic content here.  In particular, an adapter must
separately prove that its local defect is the gain of a legal deviation and
that its event mass belongs to the same literal history.
-/

namespace Math
namespace Probability

/-- Probability-like weight of reaching `time` under one-step survival
factors.  No interval assumptions are built into the definition. -/
def reachedHistoryWeight (survival : ℕ → ℝ) : ℕ → ℝ
  | 0 => 1
  | time + 1 => reachedHistoryWeight survival time * survival time

@[simp] theorem reachedHistoryWeight_zero (survival : ℕ → ℝ) :
    reachedHistoryWeight survival 0 = 1 := rfl

@[simp] theorem reachedHistoryWeight_succ
    (survival : ℕ → ℝ) (time : ℕ) :
    reachedHistoryWeight survival (time + 1) =
      reachedHistoryWeight survival time * survival time := rfl

/-- Nonnegative one-step survival factors give nonnegative reach weights. -/
theorem reachedHistoryWeight_nonneg
    {survival : ℕ → ℝ} (hsurvival : ∀ time, 0 ≤ survival time) :
    ∀ time, 0 ≤ reachedHistoryWeight survival time := by
  intro time
  induction time with
  | zero => exact zero_le_one
  | succ time ih => exact mul_nonneg ih (hsurvival time)

/-- The one-step account after multiplication by the exact reach weight. -/
theorem reachedHistoryWeight_mul_debt_eq
    (survival defect debt : ℕ → ℝ)
    (haccount : ∀ time,
      debt time = defect time + survival time * debt (time + 1))
    (time : ℕ) :
    reachedHistoryWeight survival time * debt time =
      reachedHistoryWeight survival time * defect time +
        reachedHistoryWeight survival (time + 1) * debt (time + 1) := by
  rw [haccount time, mul_add, reachedHistoryWeight_succ]
  ring

/-- Exact finite telescope of a reached-history debt account. -/
theorem debt_zero_eq_sum_reachedHistoryWeight_mul_defect_add
    (survival defect debt : ℕ → ℝ)
    (haccount : ∀ time,
      debt time = defect time + survival time * debt (time + 1)) :
    ∀ cutoff,
      debt 0 =
        (∑ time ∈ Finset.range cutoff,
          reachedHistoryWeight survival time * defect time) +
        reachedHistoryWeight survival cutoff * debt cutoff := by
  intro cutoff
  induction cutoff with
  | zero => simp
  | succ cutoff ih =>
      calc
        debt 0 =
            (∑ time ∈ Finset.range cutoff,
              reachedHistoryWeight survival time * defect time) +
            reachedHistoryWeight survival cutoff * debt cutoff := ih
        _ = (∑ time ∈ Finset.range cutoff,
              reachedHistoryWeight survival time * defect time) +
            (reachedHistoryWeight survival cutoff * defect cutoff +
              reachedHistoryWeight survival (cutoff + 1) * debt (cutoff + 1)) := by
                rw [← reachedHistoryWeight_mul_debt_eq
                  survival defect debt haccount cutoff]
        _ = (∑ time ∈ Finset.range (cutoff + 1),
              reachedHistoryWeight survival time * defect time) +
            reachedHistoryWeight survival (cutoff + 1) * debt (cutoff + 1) := by
                rw [Finset.sum_range_succ]
                ring

/-- Maximal mixed transport/prefix account.  `gain` records payoff gained by
a strategy transport, `envelopeDrift` records the change in the transported
player's best-response envelope, and `defect` records the next prefix root's
cap-Nash error.  Fixed-opponent transports have zero `envelopeDrift`; without
that restriction the signed drift is the exact additional term. -/
theorem debt_zero_eq_sum_reachedHistoryWeight_mul_gain_sub_drift_add_defect
    (survival gain envelopeDrift defect debt : ℕ → ℝ)
    (haccount : ∀ time,
      debt time = gain time - envelopeDrift time + defect time +
        survival time * debt (time + 1)) :
    ∀ cutoff,
      debt 0 =
        (∑ time ∈ Finset.range cutoff,
          reachedHistoryWeight survival time *
            (gain time - envelopeDrift time + defect time)) +
        reachedHistoryWeight survival cutoff * debt cutoff := by
  intro cutoff
  apply debt_zero_eq_sum_reachedHistoryWeight_mul_defect_add
    survival (fun time =>
      gain time - envelopeDrift time + defect time) debt
  exact haccount

/-- A defect at one marked reached row is bounded by the initial debt. -/
theorem reachedHistoryWeight_mul_defect_le_debt_zero
    {survival defect debt : ℕ → ℝ}
    (haccount : ∀ time,
      debt time = defect time + survival time * debt (time + 1))
    (hsurvival : ∀ time, 0 ≤ survival time)
    (hdefect : ∀ time, 0 ≤ defect time)
    (hdebt : ∀ time, 0 ≤ debt time)
    (marked : ℕ) :
    reachedHistoryWeight survival marked * defect marked ≤ debt 0 := by
  have htelescope :=
    debt_zero_eq_sum_reachedHistoryWeight_mul_defect_add
      survival defect debt haccount (marked + 1)
  have htermNonneg : ∀ time,
      0 ≤ reachedHistoryWeight survival time * defect time :=
    fun time => mul_nonneg (reachedHistoryWeight_nonneg hsurvival time)
      (hdefect time)
  have hmarked :
      reachedHistoryWeight survival marked * defect marked ≤
        ∑ time ∈ Finset.range (marked + 1),
          reachedHistoryWeight survival time * defect time :=
    Finset.single_le_sum (fun time _ => htermNonneg time)
      (Finset.mem_range.mpr (Nat.lt_succ_self marked))
  have hremainder : 0 ≤
      reachedHistoryWeight survival (marked + 1) * debt (marked + 1) :=
    mul_nonneg (reachedHistoryWeight_nonneg hsurvival (marked + 1))
      (hdebt (marked + 1))
  linarith

/-- Marked-event localization.  If an event at `marked` has mass no larger
than the reach weight, its mass-weighted defect is bounded by initial debt. -/
theorem eventMass_mul_defect_le_debt_zero
    {survival defect debt : ℕ → ℝ}
    (haccount : ∀ time,
      debt time = defect time + survival time * debt (time + 1))
    (hsurvival : ∀ time, 0 ≤ survival time)
    (hdefect : ∀ time, 0 ≤ defect time)
    (hdebt : ∀ time, 0 ≤ debt time)
    {marked : ℕ} {eventMass : ℝ}
    (heventReach : eventMass ≤ reachedHistoryWeight survival marked) :
    eventMass * defect marked ≤ debt 0 := by
  have hweighted : eventMass * defect marked ≤
      reachedHistoryWeight survival marked * defect marked :=
    mul_le_mul_of_nonneg_right heventReach (hdefect marked)
  exact hweighted.trans
    (reachedHistoryWeight_mul_defect_le_debt_zero
      haccount hsurvival hdefect hdebt marked)

/-! ## Positive-floor return barriers -/

/-- One-sided finite telescope when each one-step account is allowed a
nonnegative approximation error. -/
theorem debt_zero_le_sum_reachedHistoryWeight_mul_defectError_add
    (survival defect error debt : ℕ → ℝ)
    (haccount : ∀ time,
      debt time ≤ defect time + error time +
        survival time * debt (time + 1))
    (hsurvival : ∀ time, 0 ≤ survival time) :
    ∀ cutoff,
      debt 0 ≤
        (∑ time ∈ Finset.range cutoff,
          reachedHistoryWeight survival time *
            (defect time + error time)) +
        reachedHistoryWeight survival cutoff * debt cutoff := by
  intro cutoff
  induction cutoff with
  | zero => simp
  | succ cutoff ih =>
      have hweight := mul_le_mul_of_nonneg_left (haccount cutoff)
        (reachedHistoryWeight_nonneg hsurvival cutoff)
      have hweight' :
          reachedHistoryWeight survival cutoff * debt cutoff ≤
            reachedHistoryWeight survival cutoff *
                (defect cutoff + error cutoff) +
              reachedHistoryWeight survival (cutoff + 1) *
                debt (cutoff + 1) := by
        calc
          _ ≤ reachedHistoryWeight survival cutoff *
              (defect cutoff + error cutoff +
                survival cutoff * debt (cutoff + 1)) := hweight
          _ = _ := by rw [reachedHistoryWeight_succ]; ring
      calc
        debt 0 ≤
            (∑ time ∈ Finset.range cutoff,
              reachedHistoryWeight survival time *
                (defect time + error time)) +
            reachedHistoryWeight survival cutoff * debt cutoff := ih
        _ ≤ (∑ time ∈ Finset.range cutoff,
              reachedHistoryWeight survival time *
                (defect time + error time)) +
            (reachedHistoryWeight survival cutoff *
                (defect cutoff + error cutoff) +
              reachedHistoryWeight survival (cutoff + 1) *
                debt (cutoff + 1)) := by linarith
        _ = (∑ time ∈ Finset.range (cutoff + 1),
              reachedHistoryWeight survival time *
                (defect time + error time)) +
            reachedHistoryWeight survival (cutoff + 1) *
              debt (cutoff + 1) := by
                rw [Finset.sum_range_succ]
                ring

/-- Exact positive-floor account.  If the initial and terminal debts are
written as a common positive floor plus excess, the survival loss is paid
exactly by terminal excess and reached local defects, with initial excess
carrying the favorable sign. -/
theorem floor_mul_one_sub_reachedHistoryWeight_eq
    (survival defect debt : ℕ → ℝ)
    (haccount : ∀ time,
      debt time = defect time + survival time * debt (time + 1))
    (floor initialExcess terminalExcess : ℝ) (cutoff : ℕ)
    (hinitial : debt 0 = floor + initialExcess)
    (hterminal : debt cutoff = floor + terminalExcess) :
    floor * (1 - reachedHistoryWeight survival cutoff) =
      reachedHistoryWeight survival cutoff * terminalExcess +
        (∑ time ∈ Finset.range cutoff,
          reachedHistoryWeight survival time * defect time) -
        initialExcess := by
  have htelescope := debt_zero_eq_sum_reachedHistoryWeight_mul_defect_add
    survival defect debt haccount cutoff
  rw [hinitial, hterminal] at htelescope
  linarith

/-- A marked absorption weight no larger than total survival loss cannot be
carried by an exact near-floor return for free. -/
theorem floor_mul_eventWeight_le_terminalExcess_add_defectBudget
    (survival defect debt : ℕ → ℝ)
    (haccount : ∀ time,
      debt time = defect time + survival time * debt (time + 1))
    (floor initialExcess terminalExcess eventWeight : ℝ) (cutoff : ℕ)
    (hfloor : 0 ≤ floor)
    (hinitialExcess : 0 ≤ initialExcess)
    (hevent : eventWeight ≤
      1 - reachedHistoryWeight survival cutoff)
    (hinitial : debt 0 = floor + initialExcess)
    (hterminal : debt cutoff = floor + terminalExcess) :
    floor * eventWeight ≤
      reachedHistoryWeight survival cutoff * terminalExcess +
        ∑ time ∈ Finset.range cutoff,
          reachedHistoryWeight survival time * defect time := by
  have hweighted := mul_le_mul_of_nonneg_left hevent hfloor
  have hidentity := floor_mul_one_sub_reachedHistoryWeight_eq
    survival defect debt haccount floor initialExcess terminalExcess cutoff
      hinitial hterminal
  linarith

/-- Approximate positive-floor barrier.  All matching and Bellman errors can
be inserted into `error`; survival weighting prevents an artificial cost per
unreached row. -/
theorem floor_mul_eventWeight_le_terminalExcess_add_defectErrorBudget
    (survival defect error debt : ℕ → ℝ)
    (haccount : ∀ time,
      debt time ≤ defect time + error time +
        survival time * debt (time + 1))
    (hsurvival : ∀ time, 0 ≤ survival time)
    (floor initialExcess terminalExcess eventWeight : ℝ) (cutoff : ℕ)
    (hfloor : 0 ≤ floor)
    (hinitialExcess : 0 ≤ initialExcess)
    (hevent : eventWeight ≤
      1 - reachedHistoryWeight survival cutoff)
    (hinitial : debt 0 = floor + initialExcess)
    (hterminal : debt cutoff = floor + terminalExcess) :
    floor * eventWeight ≤
      reachedHistoryWeight survival cutoff * terminalExcess +
        ∑ time ∈ Finset.range cutoff,
          reachedHistoryWeight survival time *
            (defect time + error time) := by
  have htelescope :=
    debt_zero_le_sum_reachedHistoryWeight_mul_defectError_add
      survival defect error debt haccount hsurvival cutoff
  rw [hinitial, hterminal] at htelescope
  have hweighted := mul_le_mul_of_nonneg_left hevent hfloor
  linarith

end Probability
end Math
