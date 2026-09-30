import MathUE.Finset.BernoulliBounds
import UniformEquilibrium.Quitting.Stationary.GuardedCrossedResponseWeakHalfLower

/-! # One-sided weak raw rankings and joining comparisons at the unit ceiling -/

noncomputable section

namespace GameTheory

open Math.Finset

/-- Weak joining differences for one selected recipient at a sure partner. -/
def QuittingWeakUnitJoining
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (recipient partner : Fin 4) : Prop :=
  ∀ outsider : Finset (Fin 4),
    outsider ⊆ quittingCrossedRawOutsiders recipient partner →
    weightOfReward reward (insert recipient (insert partner outsider)) recipient ≤
      weightOfReward reward (insert partner outsider) recipient

/-- Weak lower comparisons imply the full absent-partner residual inequality,
including the all-Continue outsider row. No approximation of rewards is involved. -/
theorem quittingDisplacement_partner_zero_nonneg_of_weakLowerRanking
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (hazard : Fin 4 → ℝ) (recipient partner : Fin 4) (hne : partner ≠ recipient)
    (hzero : hazard partner = 0)
    (hbox : ∀ coordinate ∈ quittingCrossedRawOutsiders recipient partner,
      0 ≤ hazard coordinate ∧ hazard coordinate ≤ 1)
    (hranking : QuittingCrossedWeakLowerRanking reward recipient partner) :
    0 ≤ quittingDiscountedDisplacement reward 0 hazard recipient := by
  let carrier := quittingCrossedRawOutsiders recipient partner
  let quit := ∑ subset ∈ carrier.powerset,
    bernoulliWeight hazard carrier subset *
      weightOfReward reward (insert recipient subset) recipient
  have hquit (other : Finset (Fin 4)) (hother : other ⊆ carrier)
      (hnonempty : other.Nonempty) : weightOfReward reward other recipient ≤ quit := by
    calc
      weightOfReward reward other recipient =
          (∑ subset ∈ carrier.powerset, bernoulliWeight hazard carrier subset) *
            weightOfReward reward other recipient := by rw [sum_bernoulliWeight, one_mul]
      _ = ∑ subset ∈ carrier.powerset,
          bernoulliWeight hazard carrier subset * weightOfReward reward other recipient := by
        rw [Finset.sum_mul]
      _ ≤ quit := by
        apply Finset.sum_le_sum
        intro subset hsubset
        exact mul_le_mul_of_nonneg_left
          (hranking subset other (Finset.mem_powerset.mp hsubset) hother hnonempty)
          (bernoulliWeight_nonneg_of_bounds hazard carrier subset
            (Finset.mem_powerset.mp hsubset) hbox)
  have hcontinue :
      (∑ subset ∈ carrier.powerset, bernoulliWeight hazard carrier subset *
        weightOfReward reward subset recipient) ≤
      (1 - ∏ coordinate ∈ carrier, (1 - hazard coordinate)) * quit := by
    have hempty : bernoulliWeight hazard carrier ∅ * weightOfReward reward ∅ recipient = 0 :=
      by simp [weightOfReward]
    have hsplit := Finset.sum_erase_add carrier.powerset
      (fun subset => bernoulliWeight hazard carrier subset *
        weightOfReward reward subset recipient) (Finset.empty_mem_powerset carrier)
    rw [hempty, add_zero] at hsplit
    rw [← hsplit]
    calc
      (∑ subset ∈ carrier.powerset.erase ∅, bernoulliWeight hazard carrier subset *
          weightOfReward reward subset recipient) ≤
          ∑ subset ∈ carrier.powerset.erase ∅, bernoulliWeight hazard carrier subset * quit := by
        apply Finset.sum_le_sum
        intro subset hsubset
        have hcarrier := Finset.mem_powerset.mp (Finset.mem_of_mem_erase hsubset)
        exact mul_le_mul_of_nonneg_left
          (hquit subset hcarrier
            (Finset.nonempty_iff_ne_empty.mpr (Finset.ne_of_mem_erase hsubset)))
          (bernoulliWeight_nonneg_of_bounds hazard carrier subset hcarrier hbox)
      _ = (1 - ∏ coordinate ∈ carrier, (1 - hazard coordinate)) * quit := by
        rw [← Finset.sum_mul, sum_bernoulliWeight_erase_empty]
  rw [quittingCrossed_displacement_partner_zero_eq_sums reward hazard recipient partner
    hne hzero]
  exact sub_nonneg.mpr hcontinue

/-- Weak raw joining comparisons average to the full sure-partner guard. -/
theorem quittingDisplacement_partner_one_nonpos_of_weakUnitJoining
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (hazard : Fin 4 → ℝ) (recipient partner : Fin 4) (hne : partner ≠ recipient)
    (hone : hazard partner = 1)
    (hbox : ∀ coordinate ∈ quittingCrossedRawOutsiders recipient partner,
      0 ≤ hazard coordinate ∧ hazard coordinate ≤ 1)
    (hjoining : QuittingWeakUnitJoining reward recipient partner) :
    quittingDiscountedDisplacement reward 0 hazard recipient ≤ 0 := by
  rw [quittingCrossed_displacement_partner_one_eq_sum_joining reward hazard recipient
    partner hne hone]
  apply Finset.sum_nonpos
  intro subset hsubset
  exact mul_nonpos_of_nonneg_of_nonpos
    (bernoulliWeight_nonneg_of_bounds hazard _ subset (Finset.mem_powerset.mp hsubset) hbox)
    (sub_nonpos.mpr (hjoining subset (Finset.mem_powerset.mp hsubset)))

end GameTheory
