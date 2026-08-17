/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import MathUE.FiniteSerialRelation
import UniformEquilibrium.Quitting.Classification.ImmediateSingletonCollision
import UniformEquilibrium.Quitting.Classification.PreemptionCycle

/-!
# Realization of preemption geometries

Solo-preemption geometry places no hidden algebraic restriction on a quitting
reward table.  Every irreflexive directed relation on a finite player type can
be realized exactly as the margin-one solo-preemption relation, while any
chosen ordered pair of distinct players simultaneously carries a margin-one
immediate singleton collision.

Consequently, every one of the seventeen marked four-player lasso positions
is possible as payoff-table geometry.  Eliminating a position requires
additional game-semantic information; it cannot follow from the named edges
alone.
-/

noncomputable section

namespace GameTheory

variable {player : Type} [Fintype player] [DecidableEq player]

omit [Fintype player] in
/-- When the collision's collider is also an immediate preemptor of its owner,
both the collider's solo row and the joint collision row beat the owner's solo
row at the same margin. -/
theorem QuittingImmediateSingletonCollision.base_add_margin_le_min_of_preempts
    {reward : {S : Finset player // S.Nonempty} → Payoff player}
    {margin : ℝ}
    (certificate : QuittingImmediateSingletonCollision reward margin)
    (hpreempts : QuittingSoloPreempts reward margin
      certificate.owner certificate.collider) :
    quittingSoloReward reward certificate.owner certificate.collider + margin ≤
      min
        (quittingSingletonCollisionReward reward certificate.owner
          certificate.collider)
        (quittingSoloReward reward certificate.collider certificate.collider) :=
  le_min certificate.collider_gain_floor hpreempts.2

/-- Singleton-row coordinates realizing a directed relation at margin one. -/
def quittingPreemptionRelationSoloReward
    (R : player → player → Prop) [DecidableRel R]
    (owner who : player) : ℝ :=
  if owner = who then 1 else if R owner who then 0 else 2

/-- A set reward supported on singleton rows. -/
def quittingPreemptionRelationSetReward
    (R : player → player → Prop) [DecidableRel R]
    (terminal : Finset player) (who : player) : ℝ :=
  ∑ owner ∈ terminal,
    if terminal = {owner} then
      quittingPreemptionRelationSoloReward R owner who
    else 0

/-- Reward table realizing `R` as its margin-one preemption relation and
placing an immediate collision at `collisionOwner, collisionCollider`. -/
def quittingPreemptionGeometryReward
    (R : player → player → Prop) [DecidableRel R]
    (collisionOwner collisionCollider : player)
    (terminal : {S : Finset player // S.Nonempty}) : Payoff player :=
  fun who ↦
    quittingPreemptionRelationSetReward R terminal.1 who +
      if terminal.1 = {collisionOwner, collisionCollider} ∧
          who = collisionCollider then
        quittingPreemptionRelationSoloReward R collisionOwner
            collisionCollider + 1
      else 0

omit [Fintype player] in
@[simp]
theorem quittingPreemptionRelationSetReward_singleton
    (R : player → player → Prop) [DecidableRel R]
    (owner who : player) :
    quittingPreemptionRelationSetReward R {owner} who =
      quittingPreemptionRelationSoloReward R owner who := by
  simp [quittingPreemptionRelationSetReward]

omit [Fintype player] in
@[simp]
theorem quittingPreemptionGeometryReward_solo
    (R : player → player → Prop) [DecidableRel R]
    {collisionOwner collisionCollider : player}
    (hcollision : collisionCollider ≠ collisionOwner)
    (owner who : player) :
    quittingSoloReward
        (quittingPreemptionGeometryReward R collisionOwner collisionCollider)
        owner who =
      quittingPreemptionRelationSoloReward R owner who := by
  have hpair : ({owner} : Finset player) ≠
      {collisionOwner, collisionCollider} := by
    intro heq
    have howner : collisionOwner = owner := by
      have : collisionOwner ∈ ({owner} : Finset player) := by
        rw [heq]
        simp
      simpa using this
    have hcollider : collisionCollider = owner := by
      have : collisionCollider ∈ ({owner} : Finset player) := by
        rw [heq]
        simp
      simpa using this
    exact hcollision (hcollider.trans howner.symm)
  unfold quittingSoloReward quittingPreemptionGeometryReward
  rw [quittingPreemptionRelationSetReward_singleton]
  simp [hpair]

omit [Fintype player] in
@[simp]
theorem quittingPreemptionGeometryReward_collision
    (R : player → player → Prop) [DecidableRel R]
    {collisionOwner collisionCollider : player}
    (hcollision : collisionCollider ≠ collisionOwner) :
    quittingSingletonCollisionReward
        (quittingPreemptionGeometryReward R collisionOwner collisionCollider)
        collisionOwner collisionCollider =
      quittingPreemptionRelationSoloReward R collisionOwner
          collisionCollider + 1 := by
  have howner : ({collisionOwner, collisionCollider} : Finset player) ≠
      {collisionOwner} := by
    intro heq
    have : collisionCollider ∈ ({collisionOwner} : Finset player) := by
      rw [← heq]
      simp
    exact hcollision (by simpa using this)
  have hcollider : ({collisionOwner, collisionCollider} : Finset player) ≠
      {collisionCollider} := by
    intro heq
    have : collisionOwner ∈ ({collisionCollider} : Finset player) := by
      rw [← heq]
      simp
    have hequal : collisionOwner = collisionCollider := by simpa using this
    exact hcollision hequal.symm
  unfold quittingSingletonCollisionReward quittingPreemptionGeometryReward
  simp [quittingPreemptionRelationSetReward, howner, hcollider]

omit [Fintype player] in
/-- The constructed table's margin-one preemption relation is exactly `R`. -/
theorem quittingSoloPreempts_preemptionGeometryReward_iff
    (R : player → player → Prop) [DecidableRel R]
    (hirreflexive : ∀ owner, ¬ R owner owner)
    {collisionOwner collisionCollider owner other : player}
    (hcollision : collisionCollider ≠ collisionOwner) :
    QuittingSoloPreempts
        (quittingPreemptionGeometryReward R collisionOwner collisionCollider)
        1 owner other ↔
      R owner other := by
  rw [QuittingSoloPreempts,
    quittingPreemptionGeometryReward_solo R hcollision,
    quittingPreemptionGeometryReward_solo R hcollision]
  by_cases hsame : owner = other
  · subst other
    simp [hirreflexive, quittingPreemptionRelationSoloReward]
  · by_cases hedge : R owner other
    · have hother : other ≠ owner := Ne.symm hsame
      simp [hsame, hother, hedge, quittingPreemptionRelationSoloReward]
    · norm_num [hsame, hedge, quittingPreemptionRelationSoloReward]

/-- Any ordered pair of distinct players is an immediate singleton collision
in the constructed table. -/
def quittingPreemptionGeometryCollision
    (R : player → player → Prop) [DecidableRel R]
    {collisionOwner collisionCollider : player}
    (hcollision : collisionCollider ≠ collisionOwner) :
    QuittingImmediateSingletonCollision
      (quittingPreemptionGeometryReward R collisionOwner collisionCollider) 1 where
  owner := collisionOwner
  collider := collisionCollider
  collider_ne_owner := hcollision
  owner_solo_floor := by
    rw [quittingPreemptionGeometryReward_solo R hcollision]
    simp [quittingPreemptionRelationSoloReward]
  collider_gain_floor := by
    rw [quittingPreemptionGeometryReward_solo R hcollision,
      quittingPreemptionGeometryReward_collision R hcollision]

omit [Fintype player] in
/-- **Universal table-level realization.**  Every irreflexive directed
relation and every marked ordered pair of distinct players occur together as
the exact margin-one preemption graph and an immediate singleton collision of
one quitting reward table. -/
theorem exists_reward_realizing_preemptionRelation_and_collision
    (R : player → player → Prop) [DecidableRel R]
    (hirreflexive : ∀ owner, ¬ R owner owner)
    {collisionOwner collisionCollider : player}
    (hcollision : collisionCollider ≠ collisionOwner) :
    ∃ reward : {S : Finset player // S.Nonempty} → Payoff player,
      (∀ owner other,
        QuittingSoloPreempts reward 1 owner other ↔ R owner other) ∧
      Nonempty (QuittingImmediateSingletonCollision reward 1) := by
  refine ⟨quittingPreemptionGeometryReward R collisionOwner collisionCollider,
    ?_, ⟨quittingPreemptionGeometryCollision R hcollision⟩⟩
  intro owner other
  exact quittingSoloPreempts_preemptionGeometryReward_iff
    R hirreflexive hcollision

end GameTheory
