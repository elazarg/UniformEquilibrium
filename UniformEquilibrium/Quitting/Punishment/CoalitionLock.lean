/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Bellman.Finite.PunishmentFloorChargeCapacity
import UniformEquilibrium.Quitting.Paths.SureExitSet

/-!
# Pure coalition locks in quitting games

A pure quitting coalition is *locked* when it is nonempty and no player gains
by changing membership in the coalition.  Stability itself implies that its
exit payoff dominates the behavioral punishment floor.  The associated pure
root is then an exact Nash--Bellman self-loop, and every traversal has
absorption charge one.  Repeating the loop therefore gives exact
punishment-floor prefixes of arbitrary charge.

This module records the construction at three levels.

* `quittingCoalitionLockFinitePrefix` is the literal repeated exact prefix;
* `punishmentFloorPrefixChargeCapacity_eq_top_of_coalitionLock` shows that a
  lock makes the canonical prefix capacity infinite; and
* `quittingPunishmentValue_le_setReward_of_isQuittingSureExitSet` derives the
  punishment-floor inequality from pure-coalition stability.

The singleton member's Continue deviation is not identified with the empty-set
payoff.  At the one-stage self-loop it reaches the same singleton continuation
value.  The fixed-point and root-Nash proofs below pass through the stationary
profile identity, which treats this boundary case exactly.
-/

noncomputable section

namespace GameTheory

open QuittingSureSetOwnerRepair

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}

/-- A nonempty pure quitting coalition stable against every unilateral
membership toggle. -/
def IsQuittingCoalitionLock
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (S : Finset ι) : Prop :=
  S.Nonempty ∧ IsQuittingSureExitSet reward S

/-- The set reward is a Bellman fixed point of its pure set root.  This is
valid even for the empty set.  In particular, at a singleton the owner's
Continue endpoint rolls into the same singleton continuation value. -/
theorem quittingPureSetRoot_setReward_fixedPoint (S : Finset ι) :
    quittingSetReward reward S =
      quittingRootSuccessorPayoff reward (quittingSetReward reward S)
        (quittingPureSetRoot S) := by
  funext who
  let profile :=
    quittingStationaryProfile reward (quittingPureSetRoot S)
  calc
    quittingSetReward reward S who =
        quittingTerminalPayoff reward profile who := by
      symm
      exact quittingTerminalPayoff_pureSetRoot reward S who
    _ = quittingRootExpectedPayoff reward
          (fun player => quittingTerminalPayoff reward profile player)
          (quittingPureSetRoot S) who :=
      quittingTerminalPayoff_stationary_eq_rootExpectedPayoff
        reward (quittingPureSetRoot S) who
    _ = quittingRootExpectedPayoff reward
          (quittingSetReward reward S) (quittingPureSetRoot S) who := by
      apply quittingRootExpectedPayoff_continuation_congr
      exact quittingTerminalPayoff_pureSetRoot reward S who

/-- A stable pure quitting coalition is an exact root Nash action against its
own set reward.  The result includes singleton and empty coalitions. -/
theorem isZeroQuittingRootNash_pureSetRoot_setReward
    (S : Finset ι) (hstable : IsQuittingSureExitSet reward S) :
    IsεQuittingRootNash reward (quittingSetReward reward S) 0
      (quittingPureSetRoot S) := by
  have hbehavior :=
    (isεAsymptoticNash_pureSetRoot_iff_isQuittingSureExitSet reward S).2
      hstable
  have hroot := isεQuittingRootNash_of_isεAsymptoticNash_stationary
    reward (quittingPureSetRoot S) 0 hbehavior
  simpa only [quittingTerminalPayoff_pureSetRoot] using hroot

/-- Stability already places a pure set reward above the behavioral
punishment floor: the punishment value is below the stationary unilateral
cap, and stability bounds both membership toggles by the set reward. -/
theorem quittingPunishmentValue_le_setReward_of_isQuittingSureExitSet
    (S : Finset ι) (hstable : IsQuittingSureExitSet reward S) (who : ι) :
    quittingPunishmentValue reward who ≤
      quittingSetReward reward S who := by
  have hfloor := quittingPunishmentValue_le_stationaryUnilateralCap
    reward who (quittingPureSetRoot S)
  rw [quittingStationaryUnilateralCap_pureSetRoot] at hfloor
  exact hfloor.trans
    ((isQuittingSureExitSet_iff_forall_max reward S).1 hstable who)

omit [Fintype ι] in
/-- Every nonempty stable pure quitting coalition canonically supplies a
coalition lock. -/
theorem isQuittingCoalitionLock_of_isQuittingSureExitSet
    {S : Finset ι} (hS : S.Nonempty)
    (hstable : IsQuittingSureExitSet reward S) :
    IsQuittingCoalitionLock reward S :=
  ⟨hS, hstable⟩

/-- Repeat a coalition lock for a prescribed finite horizon.  Every row and
value is literally constant; the orientation is the forward-prefix
orientation used by `QuittingPunishmentFloorFinitePrefix`. -/
def quittingCoalitionLockFinitePrefix
    {S : Finset ι} (hlock : IsQuittingCoalitionLock reward S)
    (horizon : ℕ) : QuittingPunishmentFloorFinitePrefix reward where
  roots := fun _ => quittingPureSetRoot S
  value := fun _ => quittingSetReward reward S
  horizon := horizon
  value_mem := by
    intro _ _
    have hbound : ∀ who,
        |quittingSetReward reward S who| ≤ quittingRewardBound reward := by
      intro who
      rw [quittingSetReward_of_nonempty reward hlock.1]
      exact abs_reward_le_quittingRewardBound reward _ who
    constructor <;> intro who
    · exact (abs_le.mp (hbound who)).1
    · exact (abs_le.mp (hbound who)).2
  anchor_floor := fun who =>
    quittingPunishmentValue_le_setReward_of_isQuittingSureExitSet
      S hlock.2 who
  policy := by
    intro _ _
    exact quittingPureSetRoot_setReward_fixedPoint S
  exactNash := by
    intro _ _
    exact isZeroQuittingRootNash_pureSetRoot_setReward S hlock.2

/-- A repeated nonempty coalition lock has exactly one unit of absorption
charge per stage. -/
@[simp] theorem quittingCoalitionLockFinitePrefix_charge
    {S : Finset ι} (hlock : IsQuittingCoalitionLock reward S)
    (horizon : ℕ) :
    (quittingCoalitionLockFinitePrefix hlock horizon).charge = horizon := by
  simp [quittingCoalitionLockFinitePrefix,
    QuittingPunishmentFloorFinitePrefix.charge,
    quittingRootAbsorptionMass_pureSetRoot_of_nonempty hlock.1]

/-- A coalition lock makes the canonical exact punishment-floor prefix
capacity infinite. -/
theorem punishmentFloorPrefixChargeCapacity_eq_top_of_coalitionLock
    {S : Finset ι} (hlock : IsQuittingCoalitionLock reward S) :
    quittingPunishmentFloorPrefixChargeCapacity reward = ⊤ := by
  rw [punishmentFloorPrefixChargeCapacity_eq_top_iff]
  intro target _
  obtain ⟨horizon, hhorizon⟩ := exists_nat_gt target
  refine ⟨quittingCoalitionLockFinitePrefix hlock horizon, ?_⟩
  simpa using hhorizon

end GameTheory
