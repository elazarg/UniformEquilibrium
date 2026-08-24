/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import MathUE.FiniteAffineIntervalFeasibility
import UniformEquilibrium.Quitting.Boundary.Repair.CollisionRepairCharacterization

/-!
# Finite elimination of the collision-repair rate

The sure-blocker collision repair has one real rate in the unit interval.
Owner optimality pins that rate to zero or one unless the owner is indifferent
between the blocker singleton and the owner--blocker pair.  On the indifference
face, all remaining conditions are one finite family of affine inequalities,
so `Math.finiteAffineIntervalFeasible_iff` removes the rate quantifier by a
finite sign and cross-product test.

This module is the exact rate-elimination layer.  It does not obtain the
endpoint defects from singleton-packet data and does not assert that either
orientation of a supported pair passes the resulting finite test.
-/

noncomputable section

namespace GameTheory

open QuittingSureSetOwnerRepair

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The blocker and all spectators are exactly the collision constraints
remaining after the owner's endpoint condition is separated. -/
abbrev QuittingCollisionConstraintPlayer (owner : ι) :=
  {who : ι // who ≠ owner}

/-- Rate-zero endpoint defect for a blocker or spectator collision row. -/
def quittingCollisionConstraintLower
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (owner blocker : ι) (index : QuittingCollisionConstraintPlayer owner) : ℝ :=
  if index.1 = blocker then
    quittingPunishmentValue reward blocker -
      quittingSetReward reward ({blocker} : Finset ι) blocker
  else
    quittingSetReward reward ({index.1, blocker} : Finset ι) index.1 -
      quittingSetReward reward ({blocker} : Finset ι) index.1

/-- Rate-one endpoint defect for a blocker or spectator collision row. -/
def quittingCollisionConstraintUpper
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (owner blocker : ι) (index : QuittingCollisionConstraintPlayer owner) : ℝ :=
  if index.1 = blocker then
    quittingSetReward reward ({owner} : Finset ι) blocker -
      quittingSetReward reward ({owner, blocker} : Finset ι) blocker
  else
    quittingSetReward reward
        ({owner, index.1, blocker} : Finset ι) index.1 -
      quittingSetReward reward ({owner, blocker} : Finset ι) index.1

/-- The blocker balance and every spectator no-join inequality are precisely
the affine interpolation of their endpoint defects. -/
theorem quittingCollisionConstraints_iff
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    {owner blocker : ι} (hne : owner ≠ blocker) (rate : ℝ) :
    (∀ index : QuittingCollisionConstraintPlayer owner,
      (1 - rate) *
          quittingCollisionConstraintLower reward owner blocker index +
        rate * quittingCollisionConstraintUpper reward owner blocker index ≤ 0) ↔
      QuittingCollisionSpectatorNoJoin reward owner blocker rate ∧
        QuittingCollisionBlockerBalance reward owner blocker rate := by
  constructor
  · intro hconstraints
    constructor
    · intro spectator hspectatorOwner hspectatorBlocker
      have h := hconstraints ⟨spectator, hspectatorOwner⟩
      simp only [quittingCollisionConstraintLower,
        quittingCollisionConstraintUpper, if_neg hspectatorBlocker] at h
      rw [quittingCollisionRepairValue_apply]
      linarith
    · rw [quittingCollisionBlockerBalance_iff]
      have h := hconstraints
        (⟨blocker, Ne.symm hne⟩ : QuittingCollisionConstraintPlayer owner)
      rw [quittingCollisionConstraintLower,
        quittingCollisionConstraintUpper, if_pos rfl, if_pos rfl] at h
      linarith
  · rintro ⟨hspectators, hblocker⟩ index
    by_cases hindex : index.1 = blocker
    · rw [quittingCollisionBlockerBalance_iff] at hblocker
      rw [quittingCollisionConstraintLower,
        quittingCollisionConstraintUpper, if_pos hindex, if_pos hindex]
      linarith
    · have h := hspectators index.1 index.2 hindex
      rw [quittingCollisionRepairValue_apply] at h
      simp only [quittingCollisionConstraintLower,
        quittingCollisionConstraintUpper, if_neg hindex]
      linarith

/-- When the pair is strictly worse for the owner than the blocker singleton,
a legal collision repair exists exactly when every rate-zero blocker or
spectator defect is nonpositive. -/
theorem exists_quittingCollisionRepairWorks_iff_lower_of_owner_lt
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    {owner blocker : ι} (hne : owner ≠ blocker)
    (hlt : quittingSetReward reward ({owner, blocker} : Finset ι) owner <
      quittingSetReward reward ({blocker} : Finset ι) owner) :
    (∃ (rate : ℝ) (hrate0 : 0 ≤ rate) (hrate1 : rate ≤ 1),
      QuittingCollisionRepairWorks reward owner blocker rate hrate0 hrate1) ↔
      ∀ index : QuittingCollisionConstraintPlayer owner,
        quittingCollisionConstraintLower reward owner blocker index ≤ 0 := by
  constructor
  · rintro ⟨rate, hrate0, hrate1, hworks⟩
    have hconditions :=
      (quittingCollisionRepairWorks_iff reward hne hrate0 hrate1).1 hworks
    have hrate := eq_zero_of_quittingCollisionOwnerOptimal_of_lt
      hrate0 hlt hconditions.1
    have hconstraints :=
      (quittingCollisionConstraints_iff reward hne rate).2 hconditions.2
    simpa [hrate] using hconstraints
  · intro hlower
    have howner : QuittingCollisionOwnerOptimal reward owner blocker 0 := by
      unfold QuittingCollisionOwnerOptimal
      rw [quittingCollisionRepairValue_apply, max_eq_right hlt.le]
      simp
    have hconstraints : ∀ index : QuittingCollisionConstraintPlayer owner,
        (1 - (0 : ℝ)) *
            quittingCollisionConstraintLower reward owner blocker index +
          0 * quittingCollisionConstraintUpper reward owner blocker index ≤ 0 := by
      simpa using hlower
    have hremaining :=
      (quittingCollisionConstraints_iff reward hne 0).1 hconstraints
    exact ⟨0, le_rfl, zero_le_one,
      (quittingCollisionRepairWorks_iff reward hne le_rfl zero_le_one).2
        ⟨howner, hremaining⟩⟩

/-- When the pair is strictly better for the owner than the blocker singleton,
a legal collision repair exists exactly when every rate-one blocker or
spectator defect is nonpositive. -/
theorem exists_quittingCollisionRepairWorks_iff_upper_of_owner_lt
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    {owner blocker : ι} (hne : owner ≠ blocker)
    (hlt : quittingSetReward reward ({blocker} : Finset ι) owner <
      quittingSetReward reward ({owner, blocker} : Finset ι) owner) :
    (∃ (rate : ℝ) (hrate0 : 0 ≤ rate) (hrate1 : rate ≤ 1),
      QuittingCollisionRepairWorks reward owner blocker rate hrate0 hrate1) ↔
      ∀ index : QuittingCollisionConstraintPlayer owner,
        quittingCollisionConstraintUpper reward owner blocker index ≤ 0 := by
  constructor
  · rintro ⟨rate, hrate0, hrate1, hworks⟩
    have hconditions :=
      (quittingCollisionRepairWorks_iff reward hne hrate0 hrate1).1 hworks
    have hrate := eq_one_of_quittingCollisionOwnerOptimal_of_lt
      hrate1 hlt hconditions.1
    have hconstraints :=
      (quittingCollisionConstraints_iff reward hne rate).2 hconditions.2
    simpa [hrate] using hconstraints
  · intro hupper
    have howner : QuittingCollisionOwnerOptimal reward owner blocker 1 := by
      unfold QuittingCollisionOwnerOptimal
      rw [quittingCollisionRepairValue_apply, max_eq_left hlt.le]
      simp
    have hconstraints : ∀ index : QuittingCollisionConstraintPlayer owner,
        (1 - (1 : ℝ)) *
            quittingCollisionConstraintLower reward owner blocker index +
          1 * quittingCollisionConstraintUpper reward owner blocker index ≤ 0 := by
      simpa using hupper
    have hremaining :=
      (quittingCollisionConstraints_iff reward hne 1).1 hconstraints
    exact ⟨1, zero_le_one, le_rfl,
      (quittingCollisionRepairWorks_iff reward hne zero_le_one le_rfl).2
        ⟨howner, hremaining⟩⟩

/-- On the owner's indifference face, existence of a legal collision repair
is exactly the finite division-free endpoint criterion. -/
theorem exists_quittingCollisionRepairWorks_iff_finiteCriterion_of_owner_eq
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    {owner blocker : ι} (hne : owner ≠ blocker)
    (heq : quittingSetReward reward ({blocker} : Finset ι) owner =
      quittingSetReward reward ({owner, blocker} : Finset ι) owner) :
    (∃ (rate : ℝ) (hrate0 : 0 ≤ rate) (hrate1 : rate ≤ 1),
      QuittingCollisionRepairWorks reward owner blocker rate hrate0 hrate1) ↔
      Math.FiniteAffineIntervalCriterion
        (quittingCollisionConstraintLower reward owner blocker)
        (quittingCollisionConstraintUpper reward owner blocker) := by
  rw [← Math.finiteAffineIntervalFeasible_iff]
  constructor
  · rintro ⟨rate, hrate0, hrate1, hworks⟩
    have hconditions :=
      (quittingCollisionRepairWorks_iff reward hne hrate0 hrate1).1 hworks
    exact ⟨rate, hrate0, hrate1,
      (quittingCollisionConstraints_iff reward hne rate).2 hconditions.2⟩
  · rintro ⟨rate, hrate0, hrate1, hconstraints⟩
    have howner : QuittingCollisionOwnerOptimal reward owner blocker rate := by
      unfold QuittingCollisionOwnerOptimal
      rw [quittingCollisionRepairValue_apply, ← heq, max_self]
      ring_nf
      exact le_rfl
    have hremaining :=
      (quittingCollisionConstraints_iff reward hne rate).1 hconstraints
    exact ⟨rate, hrate0, hrate1,
      (quittingCollisionRepairWorks_iff reward hne hrate0 hrate1).2
        ⟨howner, hremaining⟩⟩

end GameTheory
