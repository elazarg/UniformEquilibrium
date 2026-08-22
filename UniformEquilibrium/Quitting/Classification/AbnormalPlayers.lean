/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Stationary.MinMax

/-!
# Normal and abnormal players in a quitting game

A player is normal when quitting alone gives at least her behavioral
punishment value. An abnormal player has a strict deficit. For a finite game,
the minimum deficit over the abnormal players is attained and is positive.

This is the quantitative input used by the abnormal-player discussion in
Simon (2012). It does not supply the paper's omitted topological construction.
-/

noncomputable section

namespace GameTheory

open Set

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- A player's payoff when she is the unique quitter. -/
def quittingSoloSelfPayoff
    (reward : {coalition : Finset ι // coalition.Nonempty} → Payoff ι)
    (who : ι) : ℝ :=
  reward ⟨{who}, Finset.singleton_nonempty who⟩ who

/-- A player is normal when her solo payoff covers her punishment value. -/
def IsQuittingNormalPlayer
    (reward : {coalition : Finset ι // coalition.Nonempty} → Payoff ι)
    (who : ι) : Prop :=
  quittingPunishmentValue reward who ≤ quittingSoloSelfPayoff reward who

/-- A player is abnormal when her punishment value strictly exceeds her solo payoff. -/
def IsQuittingAbnormalPlayer
    (reward : {coalition : Finset ι // coalition.Nonempty} → Payoff ι)
    (who : ι) : Prop :=
  quittingSoloSelfPayoff reward who < quittingPunishmentValue reward who

/-- The strict punishment-value deficit of a player. -/
def quittingAbnormalGap
    (reward : {coalition : Finset ι // coalition.Nonempty} → Payoff ι)
    (who : ι) : ℝ :=
  quittingPunishmentValue reward who - quittingSoloSelfPayoff reward who

/-- A game has an abnormal player. -/
def HasQuittingAbnormalPlayer
    (reward : {coalition : Finset ι // coalition.Nonempty} → Payoff ι) : Prop :=
  ∃ who, IsQuittingAbnormalPlayer reward who

/-- The set of deficits of the abnormal players. -/
def quittingAbnormalGapSet
    (reward : {coalition : Finset ι // coalition.Nonempty} → Payoff ι) : Set ℝ :=
  {gap | ∃ who, IsQuittingAbnormalPlayer reward who ∧
    gap = quittingAbnormalGap reward who}

/-- The smallest abnormal-player deficit. Its value matters only when an
abnormal player exists. -/
def minimumQuittingAbnormalGap
    (reward : {coalition : Finset ι // coalition.Nonempty} → Payoff ι) : ℝ :=
  sInf (quittingAbnormalGapSet reward)

/-- An abnormal player's deficit is positive. -/
theorem quittingAbnormalGap_pos
    (reward : {coalition : Finset ι // coalition.Nonempty} → Payoff ι)
    {who : ι} (habnormal : IsQuittingAbnormalPlayer reward who) :
    0 < quittingAbnormalGap reward who := by
  exact sub_pos.mpr habnormal

/-- The finite set of abnormal-player deficits is finite. -/
theorem quittingAbnormalGapSet_finite
    (reward : {coalition : Finset ι // coalition.Nonempty} → Payoff ι) :
    (quittingAbnormalGapSet reward).Finite := by
  apply (Set.finite_range fun who ↦ quittingAbnormalGap reward who).subset
  rintro gap ⟨who, _, rfl⟩
  exact ⟨who, rfl⟩

/-- If there is an abnormal player, the minimum deficit is attained by one. -/
theorem minimumQuittingAbnormalGap_mem
    (reward : {coalition : Finset ι // coalition.Nonempty} → Payoff ι)
    (habnormal : HasQuittingAbnormalPlayer reward) :
    minimumQuittingAbnormalGap reward ∈ quittingAbnormalGapSet reward := by
  apply Set.Nonempty.csInf_mem
  · obtain ⟨who, hwho⟩ := habnormal
    exact ⟨quittingAbnormalGap reward who, who, hwho, rfl⟩
  · exact quittingAbnormalGapSet_finite reward

/-- The minimum abnormal-player deficit is strictly positive. -/
theorem minimumQuittingAbnormalGap_pos
    (reward : {coalition : Finset ι // coalition.Nonempty} → Payoff ι)
    (habnormal : HasQuittingAbnormalPlayer reward) :
    0 < minimumQuittingAbnormalGap reward := by
  obtain ⟨who, hwho, hgap⟩ := minimumQuittingAbnormalGap_mem reward habnormal
  rw [hgap]
  exact quittingAbnormalGap_pos reward hwho

/-- A positive accuracy below one third of the minimum abnormal deficit exists. -/
theorem exists_accuracy_lt_third_minimumQuittingAbnormalGap
    (reward : {coalition : Finset ι // coalition.Nonempty} → Payoff ι)
    (habnormal : HasQuittingAbnormalPlayer reward) :
    ∃ accuracy : ℝ, 0 < accuracy ∧
      accuracy < minimumQuittingAbnormalGap reward / 3 := by
  have hgap := minimumQuittingAbnormalGap_pos reward habnormal
  exact ⟨minimumQuittingAbnormalGap reward / 6, by positivity, by linarith⟩

end GameTheory
