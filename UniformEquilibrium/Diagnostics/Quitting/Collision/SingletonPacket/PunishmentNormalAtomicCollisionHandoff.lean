/-
Copyright (c) 2026 UniformEquilibrium contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: UniformEquilibrium contributors
-/

import
  UniformEquilibrium.Diagnostics.Quitting.Collision.SingletonPacket.TwoCycleLassoArmConsumers
import UniformEquilibrium.Quitting.Boundary.Repair.PunishmentNormalAtomicCollision

/-!
# Atomic collision handoff from the punishment-normal Fin4 residual

Every player in the maintained full-support hard residual is punishment
normal.  Combining that actual source field with the residual's terminal
exploitability witness forces a full-gap collision at every singleton row.

In the rooted-two owner-leave chain, applying this collision at the spectator
singleton either follows the chain's existing outsider-join arm or produces a
new joiner outside the collider/spectator pair.  Reusing the collider would
give two opposite gap inequalities and contradict positivity.
-/

noncomputable section

namespace GameTheory

open QuittingLCPClassification QuittingSureSetOwnerRepair

namespace FinFourQuantitativeFullSupportHardResidual

/-- Every singleton row in the actual Fin4 hard residual has a distinct
player whose literal collision gain is at least the same terminal gap. -/
theorem exists_terminalGap_collision_at_singleton
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    {bound : ℝ}
    (residual : FinFourQuantitativeFullSupportHardResidual reward bound)
    (owner : Fin 4) :
    ∃ other, other ≠ owner ∧
      quittingSetReward reward {owner} other +
          residual.witness.terminalGap ≤
        quittingSetReward reward {owner, other} other := by
  obtain ⟨other, hne, hgain⟩ :=
    residual.witness.exists_atomicCollision_gain_of_normal owner
      (residual.all_punishmentNormal owner)
  exact ⟨other, hne, by
    simpa only [quittingSetReward_singleton_eq_soloReward,
      quittingSetReward_pair_right] using hgain⟩

/-- Finite choice packages the four singleton collision rows as a
fixed-point-free map.  The map is output data, not a field of the residual. -/
theorem exists_fixedPointFree_terminalGap_collisionMap
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    {bound : ℝ}
    (residual : FinFourQuantitativeFullSupportHardResidual reward bound) :
    ∃ next : Fin 4 → Fin 4,
      (∀ owner, next owner ≠ owner) ∧
        ∀ owner,
          quittingSetReward reward {owner} (next owner) +
              residual.witness.terminalGap ≤
            quittingSetReward reward {owner, next owner} (next owner) := by
  choose next hnextNe hnextGain using
    fun owner ↦ residual.exists_terminalGap_collision_at_singleton owner
  exact ⟨next, hnextNe, hnextGain⟩

/-- In the rooted-two owner-leave chain, either its enlarged pair already has
a full-gap outsider join, or the collider leave is followed by a full-gap
join at the spectator singleton by a genuinely third label. -/
theorem ownerLeaveCollisionChain_outsiderJoin_or_thirdLabelHandoff
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    {bound : ℝ}
    (residual : FinFourQuantitativeFullSupportHardResidual reward bound)
    (certificate : QuittingImmediateSingletonCollision reward
      residual.witness.terminalGap)
    (chain :
      FinFourRootedTwoNextOwnerLeaveCollisionChain residual certificate) :
    (∃ outsider ∉
        ({chain.spectator, certificate.collider} : Finset (Fin 4)),
      quittingSetReward reward {chain.spectator, certificate.collider}
            outsider + residual.witness.terminalGap ≤
        quittingSetReward reward
          (insert outsider {chain.spectator, certificate.collider}) outsider) ∨
      ∃ next ∉
          ({chain.spectator, certificate.collider} : Finset (Fin 4)),
        quittingSetReward reward {chain.spectator, certificate.collider}
              certificate.collider + residual.witness.terminalGap ≤
            quittingSetReward reward {chain.spectator} certificate.collider ∧
          quittingSetReward reward {chain.spectator} next +
              residual.witness.terminalGap ≤
            quittingSetReward reward {chain.spectator, next} next := by
  rcases chain.second_gap_toggle with hcolliderLeave | houtsideJoin
  · right
    obtain ⟨next, hnextSpectator, hnextJoin⟩ :=
      residual.exists_terminalGap_collision_at_singleton chain.spectator
    have hnextCollider : next ≠ certificate.collider := by
      intro heq
      subst next
      linarith [residual.witness.terminalGap_pos]
    refine ⟨next, ?_, hcolliderLeave, hnextJoin⟩
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨hnextSpectator, hnextCollider⟩
  · exact Or.inl houtsideJoin

end FinFourQuantitativeFullSupportHardResidual

end GameTheory
