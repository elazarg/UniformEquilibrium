/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Boundary.Repair.SureSetOwnerRepair
import UniformEquilibrium.Quitting.Stationary.MinMax

/-!
# Coordinatewise clipping at the punishment floor

Clipping a continuation target upward at the behavioral punishment value
produces a floor-admissible target.  A strict punishment-to-singleton gap and
a uniform target deficit leave a strict gap after clipping.
-/

noncomputable section

namespace GameTheory

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}

/-- Coordinatewise clipping of a target at the behavioral punishment floor. -/
def quittingPunishmentFloorClip
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (target : Payoff ι) : Payoff ι :=
  fun who => max (quittingPunishmentValue reward who) (target who)

@[simp] theorem quittingPunishmentFloorClip_apply
    (target : Payoff ι) (who : ι) :
    quittingPunishmentFloorClip reward target who =
      max (quittingPunishmentValue reward who) (target who) := rfl

/-- The clipped target dominates every punishment coordinate. -/
theorem punishmentValue_le_quittingPunishmentFloorClip
    (target : Payoff ι) (who : ι) :
    quittingPunishmentValue reward who ≤
      quittingPunishmentFloorClip reward target who := by
  exact le_max_left _ _

/-- A strict punishment-to-singleton gap and a uniform target deficit leave a
strict uniform gap after floor clipping. -/
theorem exists_pos_gap_quittingPunishmentFloorClip_le_singleton_sub
    (target : Payoff ι) (who : ι) (eta : ℝ)
    (heta : 0 < eta)
    (htarget : target who ≤
      reward (quittingSingletonTerminal who) who - eta)
    (hpunishment : quittingPunishmentValue reward who <
      reward (quittingSingletonTerminal who) who) :
    ∃ gap : ℝ, 0 < gap ∧
      quittingPunishmentFloorClip reward target who ≤
        reward (quittingSingletonTerminal who) who - gap := by
  let solo := reward (quittingSingletonTerminal who) who
  let floor := quittingPunishmentValue reward who
  let gap := min eta ((solo - floor) / 2)
  have hgap : 0 < gap := by
    exact lt_min heta (half_pos (sub_pos.mpr hpunishment))
  have hgapEta : gap ≤ eta := min_le_left _ _
  have hgapSlack : gap ≤ (solo - floor) / 2 := min_le_right _ _
  have htarget' : target who ≤ solo - gap := by
    dsimp only [solo]
    linarith
  have hfloor' : floor ≤ solo - gap := by
    linarith
  exact ⟨gap, hgap, by
    rw [quittingPunishmentFloorClip_apply, max_le_iff]
    exact ⟨hfloor', htarget'⟩⟩

/-- If a singleton reward fails to strictly dominate its punishment value,
then either the singleton reward is negative or the two values coincide. -/
theorem singletonReward_neg_or_punishmentValue_eq_of_singleton_le
    (who : ι)
    (hreverse : reward (quittingSingletonTerminal who) who ≤
      quittingPunishmentValue reward who) :
    reward (quittingSingletonTerminal who) who < 0 ∨
      quittingPunishmentValue reward who =
        reward (quittingSingletonTerminal who) who := by
  by_cases hsolo : reward (quittingSingletonTerminal who) who < 0
  · exact Or.inl hsolo
  · right
    have hsoloNonneg : 0 ≤ reward (quittingSingletonTerminal who) who :=
      le_of_not_gt hsolo
    have hupper := quittingPunishmentValue_le_max_solo reward who
    rw [QuittingSureSetOwnerRepair.quittingSetReward_of_nonempty reward
      (Finset.singleton_nonempty who) who] at hupper
    change quittingPunishmentValue reward who ≤
      max (reward (quittingSingletonTerminal who) who) 0 at hupper
    rw [max_eq_left hsoloNonneg] at hupper
    exact le_antisymm hupper hreverse

end GameTheory
