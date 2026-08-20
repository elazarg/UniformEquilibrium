/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Boundary.Repair.JointComplementarity
import UniformEquilibrium.Quitting.Terminal.TailCompression.ElementaryCaps

/-!
# Joint survival of a periodic root sequence

A root sequence that repeats after `period` stages has a multiplicative
joint survival weight across whole periods: over `multiple` periods the
weight of `quittingJointSurvivalWeight` is the one-period weight raised to
that power (`quittingJointSurvivalWeight_mul_period`).

Consequently a single date of the period at which the all-continue mass
`quittingStationaryContinueMass` is below one forces the survival limit
`quittingJointSurvivalLimit` to vanish
(`quittingJointSurvivalLimit_eq_zero_of_periodic`): the one-period weight is
then strictly below one, its powers tend to zero, and the limit — an
infimum over all horizons — is squeezed between zero and those powers.

The roots are arbitrary, the period is arbitrary, and the absorbing date may
sit anywhere inside the period.  No summability, stationarity, or
soloness hypothesis is used.
-/

noncomputable section

namespace GameTheory

open Filter

variable {ι : Type} [Fintype ι]

/-- Over a sequence of period `period` the joint survival weight of
`multiple` whole periods is the one-period weight raised to that power. -/
theorem quittingJointSurvivalWeight_mul_period
    {roots : ℕ → ι → PMF Bool} {period : ℕ}
    (hperiodic : ∀ time, roots (time + period) = roots time)
    (start multiple : ℕ) :
    quittingJointSurvivalWeight roots start (multiple * period) =
      quittingJointSurvivalWeight roots start period ^ multiple := by
  induction multiple with
  | zero => simp [quittingJointSurvivalWeight_eq_prod]
  | succ multiple ih =>
      have hshift : quittingJointSurvivalWeight roots
          (start + multiple * period) period =
          quittingJointSurvivalWeight roots start period := by
        rw [quittingJointSurvivalWeight_eq_prod,
          quittingJointSurvivalWeight_eq_prod]
        refine Finset.prod_congr rfl fun offset _ => ?_
        have hrep := Function.Periodic.nat_mul hperiodic multiple (start + offset)
        rw [Nat.cast_id] at hrep
        rw [show start + multiple * period + offset =
          start + offset + multiple * period from by ring, hrep]
      rw [show (multiple + 1) * period = multiple * period + period from by ring,
        quittingJointSurvivalWeight_add, ih, hshift, pow_succ]

/-- **A periodic sequence with one absorbing date absorbs almost surely.**
The joint survival weight of a single period is strictly below one, so its
powers vanish and the joint survival limit is zero. -/
theorem quittingJointSurvivalLimit_eq_zero_of_periodic
    (roots : ℕ → ι → PMF Bool) {start period date : ℕ}
    (hperiodic : ∀ time, roots (time + period) = roots time)
    (hdate : date < period)
    (habsorbing :
      quittingStationaryContinueMass (roots (start + date)) < 1) :
    quittingJointSurvivalLimit roots start = 0 := by
  have hmem : date ∈ Finset.range period := Finset.mem_range.2 hdate
  have hfactor0 : ∀ offset,
      0 ≤ quittingStationaryContinueMass (roots (start + offset)) :=
    fun offset => quittingStationaryContinueMass_nonneg (roots (start + offset))
  have hperiodWeight0 : 0 ≤ quittingJointSurvivalWeight roots start period :=
    quittingJointSurvivalWeight_nonneg roots start period
  have hperiodWeight1 : quittingJointSurvivalWeight roots start period < 1 := by
    rw [quittingJointSurvivalWeight_eq_prod]
    have hsplit := Finset.mul_prod_erase (Finset.range period)
      (fun offset => quittingStationaryContinueMass (roots (start + offset)))
      hmem
    have hrest : (∏ offset ∈ (Finset.range period).erase date,
        quittingStationaryContinueMass (roots (start + offset))) ≤ 1 :=
      Finset.prod_le_one (fun offset _ => hfactor0 offset)
        (fun offset _ =>
          quittingStationaryContinueMass_le_one (roots (start + offset)))
    have hrest0 : 0 ≤ (∏ offset ∈ (Finset.range period).erase date,
        quittingStationaryContinueMass (roots (start + offset))) :=
      Finset.prod_nonneg fun offset _ => hfactor0 offset
    nlinarith [hsplit, hrest, hrest0, habsorbing, hfactor0 date]
  have hpow : Tendsto
      (fun multiple => quittingJointSurvivalWeight roots start period ^ multiple)
      atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one hperiodWeight0 hperiodWeight1
  have hbdd : BddBelow (Set.range fun fuel =>
      quittingJointSurvivalWeight roots start fuel) := by
    refine ⟨0, ?_⟩
    rintro value ⟨fuel, rfl⟩
    exact quittingJointSurvivalWeight_nonneg roots start fuel
  have hle : ∀ multiple, quittingJointSurvivalLimit roots start ≤
      quittingJointSurvivalWeight roots start period ^ multiple := by
    intro multiple
    rw [← quittingJointSurvivalWeight_mul_period hperiodic start multiple]
    exact ciInf_le hbdd (multiple * period)
  refine le_antisymm ?_ (quittingJointSurvivalLimit_nonneg roots start)
  exact ge_of_tendsto' hpow hle

end GameTheory
