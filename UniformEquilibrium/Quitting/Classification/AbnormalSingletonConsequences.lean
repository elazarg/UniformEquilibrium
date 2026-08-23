/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Classification.AbnormalSingletonFloor

/-!
# Sign and singleton-floor consequences of abnormality

The all-Continue opponent row bounds every behavioral punishment value by the
maximum of zero and the player's own singleton payoff.  Consequently an
abnormal player's own singleton payoff is strictly negative and her punishment
value is nonpositive.  Combined with the singleton-floor theorem, every other
singleton row lies weakly above the punishment value and strictly above the
abnormal player's own singleton payoff.
-/

noncomputable section

namespace GameTheory

open Math.Probability

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- An abnormal player's own singleton payoff is strictly negative. -/
theorem quittingSoloSelfPayoff_neg_of_abnormal
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    {who : ι} (habnormal : IsQuittingAbnormalPlayer reward who) :
    quittingSoloSelfPayoff reward who < 0 := by
  have hcap := quittingPunishmentValue_le_stationaryUnilateralCap reward who
    (quittingSoloStationaryRoot who (PMF.pure false))
  rw [quittingStationaryUnilateralCap_solo_owner] at hcap
  by_contra hnot
  have hnonneg : 0 ≤ quittingSoloSelfPayoff reward who := le_of_not_gt hnot
  have hsolo : quittingSoloReward reward who who =
      quittingSoloSelfPayoff reward who := by
    rfl
  rw [hsolo, max_eq_left hnonneg] at hcap
  exact (not_lt_of_ge hcap) habnormal

/-- An abnormal player's punishment value is nonpositive. -/
theorem quittingPunishmentValue_nonpos_of_abnormal
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    {who : ι} (habnormal : IsQuittingAbnormalPlayer reward who) :
    quittingPunishmentValue reward who ≤ 0 := by
  have hcap := quittingPunishmentValue_le_stationaryUnilateralCap reward who
    (quittingSoloStationaryRoot who (PMF.pure false))
  rw [quittingStationaryUnilateralCap_solo_owner] at hcap
  have hsolo : quittingSoloReward reward who who =
      quittingSoloSelfPayoff reward who := by
    rfl
  rw [hsolo, max_eq_right
    (quittingSoloSelfPayoff_neg_of_abnormal reward habnormal).le] at hcap
  exact hcap

/-- Every other singleton row lies above an abnormal player's punishment
value, which in turn lies strictly above that player's own singleton row. -/
theorem abnormal_singletonFloor_chain
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    {abnormal owner : ι}
    (habnormal : IsQuittingAbnormalPlayer reward abnormal)
    (hne : abnormal ≠ owner) :
    quittingSoloReward reward abnormal abnormal <
        quittingPunishmentValue reward abnormal ∧
      quittingPunishmentValue reward abnormal ≤
        quittingSoloReward reward owner abnormal := by
  constructor
  · exact habnormal
  · exact quittingPunishmentValue_le_soloReward_of_abnormal
      reward habnormal hne

/-- Any probability mixture of singleton rows that assigns zero mass to an
abnormal player's own row remains above that player's punishment value.  This
is the finite-mixture protected-face interface used when a path is supported
on a subtype that omits the abnormal player. -/
theorem quittingPunishmentValue_le_singletonMixture_of_abnormal
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    {abnormal : ι} (habnormal : IsQuittingAbnormalPlayer reward abnormal)
    (weight : ι → ℝ) (hweight : ∀ owner, 0 ≤ weight owner)
    (htotal : ∑ owner, weight owner = 1)
    (hself : weight abnormal = 0) :
    quittingPunishmentValue reward abnormal ≤
      ∑ owner, weight owner * quittingSoloReward reward owner abnormal := by
  calc
    quittingPunishmentValue reward abnormal =
        ∑ owner, weight owner * quittingPunishmentValue reward abnormal := by
      rw [← Finset.sum_mul, htotal, one_mul]
    _ ≤ ∑ owner, weight owner *
        quittingSoloReward reward owner abnormal := by
      apply Finset.sum_le_sum
      intro owner howner
      by_cases hownerSelf : owner = abnormal
      · subst owner
        simp [hself]
      · exact mul_le_mul_of_nonneg_left
          (quittingPunishmentValue_le_soloReward_of_abnormal
            reward habnormal (Ne.symm hownerSelf))
          (hweight owner)

/-- The protected singleton mixture is strictly above the abnormal player's
own singleton payoff. -/
theorem quittingSoloSelfPayoff_lt_singletonMixture_of_abnormal
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    {abnormal : ι} (habnormal : IsQuittingAbnormalPlayer reward abnormal)
    (weight : ι → ℝ) (hweight : ∀ owner, 0 ≤ weight owner)
    (htotal : ∑ owner, weight owner = 1)
    (hself : weight abnormal = 0) :
    quittingSoloSelfPayoff reward abnormal <
      ∑ owner, weight owner * quittingSoloReward reward owner abnormal := by
  exact habnormal.trans_le
    (quittingPunishmentValue_le_singletonMixture_of_abnormal
      reward habnormal weight hweight htotal hself)

end GameTheory
