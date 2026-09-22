import UniformEquilibrium.Quitting.Stationary.GuardedCrossedResponseRawFaces

/-! # Literal partner-face expansions of the stationary quitting sums -/

noncomputable section

namespace GameTheory

open Math.Finset

variable {n : ℕ}

/-- The opponents other than a selected recipient and its partner. -/
def quittingCrossedRawOutsiders (recipient partner : Fin n) : Finset (Fin n) :=
  (Finset.univ.erase recipient).erase partner

private theorem opponents_eq_insert_partner
    (recipient partner : Fin n) (hne : partner ≠ recipient) :
    Finset.univ.erase recipient =
      insert partner (quittingCrossedRawOutsiders recipient partner) := by
  ext coordinate
  simp [quittingCrossedRawOutsiders, hne]

private theorem partner_not_mem_outsiders (recipient partner : Fin n) :
    partner ∉ quittingCrossedRawOutsiders recipient partner := by
  simp [quittingCrossedRawOutsiders]

/-- Exact pure-Quit sum when the partner's hazard is zero. -/
theorem quittingCrossed_sigmaValue_partner_zero
    (weight : Finset (Fin n) → Fin n → ℝ) (hazard : Fin n → ℝ)
    (recipient partner : Fin n) (hne : partner ≠ recipient)
    (hzero : hazard partner = 0) :
    sigmaValue weight hazard recipient =
      ∑ subset ∈ (quittingCrossedRawOutsiders recipient partner).powerset,
        bernoulliWeight hazard (quittingCrossedRawOutsiders recipient partner) subset *
          weight (insert recipient subset) recipient := by
  unfold sigmaValue
  rw [opponents_eq_insert_partner recipient partner hne]
  change (∑ subset ∈ (insert partner (quittingCrossedRawOutsiders recipient partner)).powerset,
      bernoulliWeight hazard (insert partner (quittingCrossedRawOutsiders recipient partner))
        subset * weight (insert recipient subset) recipient) = _
  exact quittingCrossed_sum_bernoulliWeight_partner_zero
    (quittingCrossedRawOutsiders recipient partner) partner
    (partner_not_mem_outsiders recipient partner) hazard hzero
      (fun subset => weight (insert recipient subset) recipient)

/-- Exact pure-Quit sum when the partner's hazard is one. -/
theorem quittingCrossed_sigmaValue_partner_one
    (weight : Finset (Fin n) → Fin n → ℝ) (hazard : Fin n → ℝ)
    (recipient partner : Fin n) (hne : partner ≠ recipient)
    (hone : hazard partner = 1) :
    sigmaValue weight hazard recipient =
      ∑ subset ∈ (quittingCrossedRawOutsiders recipient partner).powerset,
        bernoulliWeight hazard (quittingCrossedRawOutsiders recipient partner) subset *
          weight (insert recipient (insert partner subset)) recipient := by
  unfold sigmaValue
  rw [opponents_eq_insert_partner recipient partner hne]
  change (∑ subset ∈ (insert partner (quittingCrossedRawOutsiders recipient partner)).powerset,
      bernoulliWeight hazard (insert partner (quittingCrossedRawOutsiders recipient partner))
        subset * weight (insert recipient subset) recipient) = _
  exact quittingCrossed_sum_bernoulliWeight_partner_one
    (quittingCrossedRawOutsiders recipient partner) partner
    (partner_not_mem_outsiders recipient partner) hazard hone
      (fun subset => weight (insert recipient subset) recipient)

/-- The artificial empty reward is zero, so the Continue sum may use the full powerset. -/
private theorem excludedValue_eq_fullBernoulliSum
    (reward : {S : Finset (Fin n) // S.Nonempty} → Payoff (Fin n))
    (hazard : Fin n → ℝ) (recipient : Fin n) :
    excludedValue (weightOfReward reward) hazard recipient =
      ∑ subset ∈ (Finset.univ.erase recipient).powerset,
        bernoulliWeight hazard (Finset.univ.erase recipient) subset *
          weightOfReward reward subset recipient := by
  let opponents := Finset.univ.erase recipient
  have hempty : (∅ : Finset (Fin n)) ∈ opponents.powerset :=
    Finset.empty_mem_powerset opponents
  have hsplit := Finset.sum_erase_add opponents.powerset
    (fun subset => bernoulliWeight hazard opponents subset *
      weightOfReward reward subset recipient) hempty
  have hemptyTerm : bernoulliWeight hazard opponents ∅ *
      weightOfReward reward ∅ recipient = 0 := by
    simp [weightOfReward]
  rw [hemptyTerm, add_zero] at hsplit
  exact hsplit

/-- Exact Continue sum when the partner's hazard is zero. -/
theorem quittingCrossed_excludedValue_partner_zero
    (reward : {S : Finset (Fin n) // S.Nonempty} → Payoff (Fin n))
    (hazard : Fin n → ℝ) (recipient partner : Fin n)
    (hne : partner ≠ recipient) (hzero : hazard partner = 0) :
    excludedValue (weightOfReward reward) hazard recipient =
      ∑ subset ∈ (quittingCrossedRawOutsiders recipient partner).powerset,
        bernoulliWeight hazard (quittingCrossedRawOutsiders recipient partner) subset *
          weightOfReward reward subset recipient := by
  rw [excludedValue_eq_fullBernoulliSum, opponents_eq_insert_partner recipient partner hne]
  exact quittingCrossed_sum_bernoulliWeight_partner_zero
    (quittingCrossedRawOutsiders recipient partner) partner
    (partner_not_mem_outsiders recipient partner) hazard hzero
      (fun subset => weightOfReward reward subset recipient)

/-- Exact Continue sum when the partner's hazard is one. -/
theorem quittingCrossed_excludedValue_partner_one
    (reward : {S : Finset (Fin n) // S.Nonempty} → Payoff (Fin n))
    (hazard : Fin n → ℝ) (recipient partner : Fin n)
    (hne : partner ≠ recipient) (hone : hazard partner = 1) :
    excludedValue (weightOfReward reward) hazard recipient =
      ∑ subset ∈ (quittingCrossedRawOutsiders recipient partner).powerset,
        bernoulliWeight hazard (quittingCrossedRawOutsiders recipient partner) subset *
          weightOfReward reward (insert partner subset) recipient := by
  rw [excludedValue_eq_fullBernoulliSum, opponents_eq_insert_partner recipient partner hne]
  exact quittingCrossed_sum_bernoulliWeight_partner_one
    (quittingCrossedRawOutsiders recipient partner) partner
    (partner_not_mem_outsiders recipient partner) hazard hone
      (fun subset => weightOfReward reward subset recipient)

end GameTheory
