import UniformEquilibrium.Quitting.Classification.PlayerDeletionLift

/-! # A shared approximate-Nash consumer of quiet-lift terminal debt bounds -/

noncomputable section

namespace GameTheory

open StochasticGame

variable {α : Type} [Fintype α] [DecidableEq α]

/-- Nonnegative weighted bounds on quiet outsiders' actual terminal debts
assemble into one approximate-Nash bound. Raw reward-row producers discharge
these internal hypotheses; child payoffs and deviation caps use the existing
exact deletion identity. -/
theorem isεAsymptoticNash_quietLift_of_outsideTerminalDebtBounds_add
    (deleted : α → Prop) [DecidablePred deleted]
    (reward : {S : Finset α // S.Nonempty} → Payoff α)
    (weight : {who : α // deleted who} → {who : α // ¬ deleted who} → ℝ)
    (hweight : ∀ outside child, 0 ≤ weight outside child)
    (factor : ℝ) (hfactor : 1 ≤ factor)
    (hweightFactor : ∀ outside, (∑ child, weight outside child) ≤ factor)
    (allowance : ℝ) (hallowance : 0 ≤ allowance)
    {error : ℝ} (herror : 0 ≤ error)
    (profile : (quittingGame (quittingDeleteReward reward deleted)).BehaviorProfile)
    (houtside : ∀ outside : {who : α // deleted who},
      quittingBehaviorDeviationPayoffCap reward
          (quittingLiftDeletedProfile reward deleted profile) outside.1 -
        quittingTerminalPayoff reward
          (quittingLiftDeletedProfile reward deleted profile) outside.1 ≤
        ∑ child, weight outside child *
          (quittingBehaviorDeviationPayoffCap
              (quittingDeleteReward reward deleted) profile child -
            quittingTerminalPayoff (quittingDeleteReward reward deleted) profile child) + allowance)
    (hnash : (quittingGame (quittingDeleteReward reward deleted)).IsεAsymptoticNash
      (quittingTerminalPayoff (quittingDeleteReward reward deleted)) error profile) :
    (quittingGame reward).IsεAsymptoticNash (quittingTerminalPayoff reward)
      (factor * error + allowance) (quittingLiftDeletedProfile reward deleted profile) := by
  let lifted := quittingLiftDeletedProfile reward deleted profile
  have hchild (child : {who : α // ¬ deleted who}) :
      quittingBehaviorDeviationPayoffCap (quittingDeleteReward reward deleted) profile child -
        quittingTerminalPayoff (quittingDeleteReward reward deleted) profile child ≤ error := by
    rw [quittingBehaviorDeviationPayoffCap_eq_bestReplyValue]
    apply sub_le_iff_le_add.mpr
    apply quittingBestReplyValue_le
    intro deviation
    have h := hnash child deviation
    linarith
  have hdebt (who : α) : quittingBehaviorDeviationPayoffCap reward lifted who -
      quittingTerminalPayoff reward lifted who ≤ factor * error + allowance := by
    by_cases hdeleted : deleted who
    · let outside : {who : α // deleted who} := ⟨who, hdeleted⟩
      calc
        _ ≤ ∑ child, weight outside child *
            (quittingBehaviorDeviationPayoffCap
                (quittingDeleteReward reward deleted) profile child -
              quittingTerminalPayoff (quittingDeleteReward reward deleted) profile child) +
            allowance :=
          houtside outside
        _ ≤ (∑ child, weight outside child * error) + allowance :=
          add_le_add (Finset.sum_le_sum fun child _ =>
            mul_le_mul_of_nonneg_left (hchild child) (hweight outside child)) le_rfl
        _ = (∑ child, weight outside child) * error + allowance := by
          rw [Finset.sum_mul]
        _ ≤ factor * error + allowance :=
          add_le_add (mul_le_mul_of_nonneg_right (hweightFactor outside) herror) le_rfl
    · let child : {who : α // ¬ deleted who} := ⟨who, hdeleted⟩
      calc
        _ = quittingBehaviorDeviationPayoffCap
            (quittingDeleteReward reward deleted) profile child -
          quittingTerminalPayoff (quittingDeleteReward reward deleted) profile child :=
            quittingBehaviorDeviationDebt_liftDeletedProfile reward deleted profile child
        _ ≤ error := hchild child
        _ ≤ factor * error := by
          simpa only [one_mul] using mul_le_mul_of_nonneg_right hfactor herror
        _ ≤ factor * error + allowance := le_add_of_nonneg_right hallowance
  intro who deviation
  have hcap := le_quittingBestReplyValue reward lifted who deviation
  rw [← quittingBehaviorDeviationPayoffCap_eq_bestReplyValue] at hcap
  change quittingTerminalPayoff reward lifted who + (factor * error + allowance) ≥ _
  linarith [hdebt who]

/-- Weighted quiet-lift debt transport without an additional allowance. -/
theorem isεAsymptoticNash_quietLift_of_outsideTerminalDebtBounds
    (deleted : α → Prop) [DecidablePred deleted]
    (reward : {S : Finset α // S.Nonempty} → Payoff α)
    (weight : {who : α // deleted who} → {who : α // ¬ deleted who} → ℝ)
    (hweight : ∀ outside child, 0 ≤ weight outside child)
    (factor : ℝ) (hfactor : 1 ≤ factor)
    (hweightFactor : ∀ outside, (∑ child, weight outside child) ≤ factor)
    {error : ℝ} (herror : 0 ≤ error)
    (profile : (quittingGame (quittingDeleteReward reward deleted)).BehaviorProfile)
    (houtside : ∀ outside : {who : α // deleted who},
      quittingBehaviorDeviationPayoffCap reward
          (quittingLiftDeletedProfile reward deleted profile) outside.1 -
        quittingTerminalPayoff reward
          (quittingLiftDeletedProfile reward deleted profile) outside.1 ≤
        ∑ child, weight outside child *
          (quittingBehaviorDeviationPayoffCap
              (quittingDeleteReward reward deleted) profile child -
            quittingTerminalPayoff (quittingDeleteReward reward deleted) profile child))
    (hnash : (quittingGame (quittingDeleteReward reward deleted)).IsεAsymptoticNash
      (quittingTerminalPayoff (quittingDeleteReward reward deleted)) error profile) :
    (quittingGame reward).IsεAsymptoticNash (quittingTerminalPayoff reward)
      (factor * error) (quittingLiftDeletedProfile reward deleted profile) := by
  simpa only [add_zero] using
    isεAsymptoticNash_quietLift_of_outsideTerminalDebtBounds_add
      deleted reward weight hweight factor hfactor hweightFactor 0 le_rfl herror profile
      (fun outside => by simpa only [add_zero] using houtside outside) hnash

end GameTheory
