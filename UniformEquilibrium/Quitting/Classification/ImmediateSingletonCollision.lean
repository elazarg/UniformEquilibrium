/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Paths.SureExitSet

/-!
# Immediate singleton collision geometry

A singleton collision certificate selects an owner who Quits surely at the
initial row and a distinct collider whose immediate Quit deviation improves
its terminal payoff by a fixed margin.  When the margin is nonnegative, the
owner's solo payoff is nonnegative and its behavioral debt is exactly zero.
The collider's debt is then exactly its collision gain and retains the full
margin.

The statements use all behavioral deviations through the terminal-semantic
best-response envelope.  The explicit immediate-Quit strategy is only the
witness attaining the displayed collision payoff.
-/

noncomputable section

namespace GameTheory

open QuittingSureSetOwnerRepair

variable {player : Type} [Fintype player] [DecidableEq player]
variable {reward : {S : Finset player // S.Nonempty} → Payoff player}

/-- Table-level data for one absorbing singleton row with a profitable
collision by a distinct player. -/
structure QuittingImmediateSingletonCollision (reward) (margin : ℝ) where
  owner : player
  collider : player
  collider_ne_owner : collider ≠ owner
  owner_solo_floor : margin ≤ quittingSoloReward reward owner owner
  collider_gain_floor :
    quittingSoloReward reward owner collider + margin ≤
      quittingSingletonCollisionReward reward owner collider

namespace QuittingImmediateSingletonCollision

variable {margin : ℝ}

/-- The executable profile at which only the selected owner Quits surely. -/
def profile (certificate : QuittingImmediateSingletonCollision reward margin) :
    (quittingGame reward).BehaviorProfile :=
  quittingStationaryProfile reward (quittingPureSetRoot {certificate.owner})

/-- The collider's legal immediate-Quit deviation. -/
def colliderDeviation
    (certificate : QuittingImmediateSingletonCollision reward margin) :
    (quittingGame reward).BehaviorStrategy certificate.collider :=
  quittingPureTimeBehaviorStrategy reward certificate.collider (some 0)

/-- The selected singleton root absorbs with probability one. -/
theorem root_absorptionMass_eq_one
    (certificate : QuittingImmediateSingletonCollision reward margin) :
    quittingRootAbsorptionMass
        (quittingPureSetRoot ({certificate.owner} : Finset player)) = 1 :=
  quittingRootAbsorptionMass_pureSetRoot_of_nonempty
    (Finset.singleton_nonempty certificate.owner)

/-- Every prescribed coordinate at the selected row is the corresponding
solo-reward coordinate of the owner. -/
theorem terminalPayoff_eq_soloReward
    (certificate : QuittingImmediateSingletonCollision reward margin)
    (who : player) :
    quittingTerminalPayoff reward certificate.profile who =
      quittingSoloReward reward certificate.owner who := by
  rw [profile, quittingTerminalPayoff_pureSetRoot,
    quittingSetReward_singleton_eq_soloReward]

/-- The selected owner's debt is exactly the positive part of the gap between
the singleton-row best-response envelope and its solo payoff. -/
theorem owner_debt_eq_max_solo_sub_solo
    (certificate : QuittingImmediateSingletonCollision reward margin) :
    quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward certificate.profile)
        certificate.owner =
      max (quittingSoloReward reward certificate.owner certificate.owner) 0 -
        quittingSoloReward reward certificate.owner certificate.owner := by
  rw [profile, quittingTerminalSemanticDebt_pureSetRoot_eq,
    Finset.insert_eq_self.mpr
      (Finset.mem_singleton_self certificate.owner), Finset.erase_singleton,
    quittingSetReward_empty, quittingSetReward_singleton_eq_soloReward]

/-- Every player distinct from the selected owner has debt equal to the
positive part of its singleton-collision excess over its solo payoff. -/
theorem debt_eq_max_collision_sub_solo_of_ne_owner
    (certificate : QuittingImmediateSingletonCollision reward margin)
    {who : player} (hwho : who ≠ certificate.owner) :
    quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward certificate.profile) who =
      max (quittingSingletonCollisionReward reward certificate.owner who -
        quittingSoloReward reward certificate.owner who) 0 := by
  have hnotMem : who ∉ ({certificate.owner} : Finset player) := by
    simpa using hwho
  rw [profile, quittingTerminalSemanticDebt_pureSetRoot_eq,
    Finset.erase_eq_of_notMem hnotMem, quittingSetReward_insert_singleton,
    quittingSetReward_singleton_eq_soloReward]
  by_cases hle : quittingSingletonCollisionReward reward certificate.owner who ≤
      quittingSoloReward reward certificate.owner who
  · rw [max_eq_right hle, max_eq_right (sub_nonpos.mpr hle)]
    ring
  · have hge : quittingSoloReward reward certificate.owner who ≤
        quittingSingletonCollisionReward reward certificate.owner who :=
      le_of_not_ge hle
    rw [max_eq_left hge, max_eq_left (sub_nonneg.mpr hge)]

/-- The collider's displayed deviation pays the singleton-collision reward
exactly. -/
theorem terminalPayoff_update_collider_eq_collisionReward
    (certificate : QuittingImmediateSingletonCollision reward margin) :
    quittingTerminalPayoff reward
        (Function.update certificate.profile certificate.collider
          certificate.colliderDeviation) certificate.collider =
      quittingSingletonCollisionReward reward certificate.owner
        certificate.collider := by
  rw [profile, colliderDeviation,
    quittingTerminalPayoff_update_pureSetRoot_quitNow,
    quittingSetReward_insert_singleton]

/-- The collider's literal immediate-Quit gain is exactly its table-level
collision gain. -/
theorem collider_gain_eq
    (certificate : QuittingImmediateSingletonCollision reward margin) :
    quittingTerminalPayoff reward
          (Function.update certificate.profile certificate.collider
            certificate.colliderDeviation) certificate.collider -
        quittingTerminalPayoff reward certificate.profile
          certificate.collider =
      quittingSingletonCollisionReward reward certificate.owner
          certificate.collider -
        quittingSoloReward reward certificate.owner certificate.collider := by
  rw [certificate.terminalPayoff_update_collider_eq_collisionReward,
    certificate.terminalPayoff_eq_soloReward]

/-- The collider's legal immediate-Quit deviation gains at least the stored
margin. -/
theorem margin_le_collider_gain
    (certificate : QuittingImmediateSingletonCollision reward margin) :
    margin ≤
      quittingTerminalPayoff reward
          (Function.update certificate.profile certificate.collider
            certificate.colliderDeviation) certificate.collider -
        quittingTerminalPayoff reward certificate.profile
          certificate.collider := by
  rw [certificate.collider_gain_eq]
  linarith [certificate.collider_gain_floor]

/-- At a nonnegative margin, the owner has exactly zero terminal-semantic
debt at the singleton row. -/
theorem owner_debt_eq_zero
    (certificate : QuittingImmediateSingletonCollision reward margin)
    (hmargin : 0 ≤ margin) :
    quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward certificate.profile)
        certificate.owner = 0 := by
  have hsolo : 0 ≤ quittingSoloReward reward certificate.owner
      certificate.owner := hmargin.trans certificate.owner_solo_floor
  rw [certificate.owner_debt_eq_max_solo_sub_solo, max_eq_left hsolo]
  ring

/-- At a nonnegative margin, the collider's terminal-semantic debt is exactly
its singleton-collision gain. -/
theorem collider_debt_eq_collisionGain
    (certificate : QuittingImmediateSingletonCollision reward margin)
    (hmargin : 0 ≤ margin) :
    quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward certificate.profile)
        certificate.collider =
      quittingSingletonCollisionReward reward certificate.owner
          certificate.collider -
        quittingSoloReward reward certificate.owner certificate.collider := by
  have hcollision : quittingSoloReward reward certificate.owner
      certificate.collider ≤
        quittingSingletonCollisionReward reward certificate.owner
          certificate.collider := by
    linarith [certificate.collider_gain_floor]
  rw [certificate.debt_eq_max_collision_sub_solo_of_ne_owner
      certificate.collider_ne_owner, max_eq_left (sub_nonneg.mpr hcollision)]

/-- The collider retains at least the stored nonnegative margin as literal
terminal-semantic debt. -/
theorem margin_le_collider_debt
    (certificate : QuittingImmediateSingletonCollision reward margin)
    (hmargin : 0 ≤ margin) :
    margin ≤ quittingTerminalSemanticDebt
      (quittingTerminalSemanticPair reward certificate.profile)
        certificate.collider := by
  rw [certificate.collider_debt_eq_collisionGain hmargin]
  linarith [certificate.collider_gain_floor]

end QuittingImmediateSingletonCollision

end GameTheory
