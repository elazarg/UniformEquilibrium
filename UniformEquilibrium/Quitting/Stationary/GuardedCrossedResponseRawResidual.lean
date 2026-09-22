import UniformEquilibrium.Quitting.Stationary.GuardedCrossedResponseRawSums

/-! # Exact crossed-response residual on literal partner faces -/

noncomputable section

namespace GameTheory

open Math.Finset

variable {n : ℕ}

/-- At a sure partner, the continuation mass vanishes. -/
theorem quittingCrossed_continueMassExcl_partner_one
    (hazard : Fin n → ℝ) (recipient partner : Fin n)
    (hne : partner ≠ recipient) (hone : hazard partner = 1) :
    continueMassExcl hazard recipient = 0 := by
  unfold continueMassExcl
  rw [show Finset.univ.erase recipient =
      insert partner (quittingCrossedRawOutsiders recipient partner) by
        ext coordinate
        simp [quittingCrossedRawOutsiders, hne]]
  rw [Finset.prod_insert]
  · simp [hone]
  · simp [quittingCrossedRawOutsiders]

/-- At an absent partner, the continuation mass is the outsiders' survival product. -/
theorem quittingCrossed_continueMassExcl_partner_zero
    (hazard : Fin n → ℝ) (recipient partner : Fin n)
    (hne : partner ≠ recipient) (hzero : hazard partner = 0) :
    continueMassExcl hazard recipient =
      ∏ outsider ∈ quittingCrossedRawOutsiders recipient partner,
        (1 - hazard outsider) := by
  unfold continueMassExcl
  rw [show Finset.univ.erase recipient =
      insert partner (quittingCrossedRawOutsiders recipient partner) by
        ext coordinate
        simp [quittingCrossedRawOutsiders, hne]]
  rw [Finset.prod_insert]
  · simp [hzero]
  · simp [quittingCrossedRawOutsiders]

/-- A sure partner turns the source residual into a weighted sum of literal
joining differences over all outsider coalitions. -/
theorem quittingCrossed_displacement_partner_one_eq_sum_joining
    (reward : {S : Finset (Fin n) // S.Nonempty} → Payoff (Fin n))
    (hazard : Fin n → ℝ) (recipient partner : Fin n)
    (hne : partner ≠ recipient) (hone : hazard partner = 1) :
    quittingDiscountedDisplacement reward 0 hazard recipient =
      ∑ subset ∈ (quittingCrossedRawOutsiders recipient partner).powerset,
        bernoulliWeight hazard (quittingCrossedRawOutsiders recipient partner) subset *
          (weightOfReward reward (insert recipient (insert partner subset)) recipient -
            weightOfReward reward (insert partner subset) recipient) := by
  rw [quittingDiscountedDisplacement,
    quittingCrossed_continueMassExcl_partner_one hazard recipient partner hne hone,
    quittingCrossed_sigmaValue_partner_one (weightOfReward reward) hazard
      recipient partner hne hone,
    quittingCrossed_excludedValue_partner_one reward hazard recipient partner hne hone]
  simp only [sub_zero, one_mul]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro subset _
  ring

/-- With the partner absent, the source residual retains exactly the outsider
probability sum and its all-Continue survival factor. -/
theorem quittingCrossed_displacement_partner_zero_eq_sums
    (reward : {S : Finset (Fin n) // S.Nonempty} → Payoff (Fin n))
    (hazard : Fin n → ℝ) (recipient partner : Fin n)
    (hne : partner ≠ recipient) (hzero : hazard partner = 0) :
    quittingDiscountedDisplacement reward 0 hazard recipient =
      (1 - ∏ outsider ∈ quittingCrossedRawOutsiders recipient partner,
        (1 - hazard outsider)) *
        (∑ subset ∈ (quittingCrossedRawOutsiders recipient partner).powerset,
          bernoulliWeight hazard (quittingCrossedRawOutsiders recipient partner) subset *
            weightOfReward reward (insert recipient subset) recipient) -
      ∑ subset ∈ (quittingCrossedRawOutsiders recipient partner).powerset,
        bernoulliWeight hazard (quittingCrossedRawOutsiders recipient partner) subset *
          weightOfReward reward subset recipient := by
  rw [quittingDiscountedDisplacement,
    quittingCrossed_continueMassExcl_partner_zero hazard recipient partner hne hzero,
    quittingCrossed_sigmaValue_partner_zero (weightOfReward reward) hazard
      recipient partner hne hzero,
    quittingCrossed_excludedValue_partner_zero reward hazard recipient partner hne hzero]
  ring

end GameTheory
