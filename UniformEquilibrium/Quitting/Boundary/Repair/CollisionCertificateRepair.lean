/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Boundary.Repair.CollisionRepairCharacterization
import UniformEquilibrium.Quitting.Classification.ImmediateSingletonCollision

/-!
# Collision certificates inside the sure-blocker repair

An immediate singleton collision supplies the positive term in the exact
blocker-balance identity.  If the collider's punishment value does not exceed
its own solo reward, the remaining term is also nonnegative.  Thus the
blocker-floor condition is automatic at every legal collision rate.
-/

noncomputable section

namespace GameTheory

open QuittingSureSetOwnerRepair

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}

/-- A nonnegative-margin collision certificate and a collider solo floor make
the exact blocker-balance condition automatic at every legal rate. -/
theorem QuittingImmediateSingletonCollision.blockerBalance_of_punishmentValue_le_solo
    {margin rate : ℝ}
    (certificate : QuittingImmediateSingletonCollision reward margin)
    (hmargin : 0 ≤ margin)
    (hpunishment : quittingPunishmentValue reward certificate.collider ≤
      quittingSoloReward reward certificate.collider certificate.collider)
    (hrate0 : 0 ≤ rate) (hrate1 : rate ≤ 1) :
    QuittingCollisionBlockerBalance reward certificate.owner
      certificate.collider rate := by
  rw [quittingCollisionBlockerBalance_iff]
  simp only [quittingSetReward_singleton_eq_soloReward,
    quittingSetReward_pair_right]
  have hweight : 0 ≤ 1 - rate := sub_nonneg.mpr hrate1
  have hsolo : 0 ≤ (1 - rate) *
      (quittingSoloReward reward certificate.collider certificate.collider -
        quittingPunishmentValue reward certificate.collider) :=
    mul_nonneg hweight (sub_nonneg.mpr hpunishment)
  have hcollision : 0 ≤ rate *
      (quittingSingletonCollisionReward reward certificate.owner
          certificate.collider -
        quittingSoloReward reward certificate.owner certificate.collider) := by
    apply mul_nonneg hrate0
    linarith [certificate.collider_gain_floor]
  linarith

end GameTheory
