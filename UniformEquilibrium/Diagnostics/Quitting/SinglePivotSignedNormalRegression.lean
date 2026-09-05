import UniformEquilibrium.Quitting.Punishment.SinglePivotPunishment
import UniformEquilibrium.Quitting.Punishment.ContinueFloor

noncomputable section

namespace GameTheory
namespace SinglePivotSignedNormalRegression

open Math.Probability Math.PMFProduct QuittingSureSetOwnerRepair

def reward : {S : Finset Bool // S.Nonempty} → Payoff Bool := fun terminal who =>
  if who then
    if terminal.val = {true} then -1 else -2
  else if false ∈ terminal.val then 1 else 0

@[simp] theorem pivot_singleton : reward (quittingSingletonTerminal false) false = 1 := by
  simp [reward, quittingSingletonTerminal]

@[simp] theorem other_singleton : reward (quittingSingletonTerminal true) true = -1 := by
  simp [reward, quittingSingletonTerminal]

theorem pivot_punishment_eq_one : quittingPunishmentValue reward false = 1 := by
  rw [quittingPunishmentValue_eq_stationaryPunishmentValue]
  apply le_antisymm
  · have h := quittingPunishmentValue_le_max_solo reward false
    rw [quittingPunishmentValue_eq_stationaryPunishmentValue] at h
    simpa [quittingSetReward, reward] using h
  · apply le_ciInf
    intro root
    apply le_trans _ (le_max_left _ _)
    change 1 ≤ quittingRootAbsorbingContribution reward
      (Function.update root false (PMF.pure true)) false
    unfold quittingRootAbsorbingContribution quittingRootExpectedPayoff
    calc
      1 = Math.Probability.expect
          (pmfPi (Function.update root false (PMF.pure true)))
          (fun _ => (1 : ℝ)) :=
        (Math.Probability.expect_const _ (1 : ℝ)).symm
      _ ≤ _ := by
        apply Math.ProbabilityMassFunction.expect_mono_on_support
        intro action hsupport
        have hfalse : action false = true := by
          cases haction : action false
          · have hzero : pmfPi (Function.update root false (PMF.pure true)) action = 0 := by
              rw [pmfPi_apply]
              apply Finset.prod_eq_zero (Finset.mem_univ false)
              simp [haction]
            rw [PMF.mem_support_iff] at hsupport
            exact (hsupport hzero).elim
          · rfl
        have hquit : (quittingQuitters action).Nonempty :=
          (quittingQuitters_nonempty_iff action).2 ⟨false, hfalse⟩
        rw [quittingRootPayoff, dif_pos hquit]
        simp [reward, quittingQuitters, hfalse]

theorem other_joinAntitone : QuittingOwnerJoinAntitone reward true := by
  intro quitters hquitters hother
  have hfalse : false ∈ quitters := by
    by_contra hfalse
    have hempty : quitters = ∅ := by
      ext who
      cases who <;> simp [hfalse, hother]
    exact hquitters.ne_empty hempty
  simp [reward, hfalse, hother, Finset.ext_iff]

theorem other_punishment_eq_neg_two : quittingPunishmentValue reward true = -2 := by
  apply le_antisymm
  · apply (quittingPunishmentValue_le_pureRowCap reward true {false}).trans
    norm_num [quittingSetReward, reward, Finset.ext_iff]
  · rw [quittingPunishmentValue_eq_stationaryPunishmentValue]
    apply le_ciInf
    intro root
    apply le_quittingStationaryUnilateralCap_of_forall_le reward true (by norm_num)
    intro terminal
    simp [reward]
    split <;> norm_num

theorem punishmentVector_eq :
    (fun who => quittingPunishmentValue reward who) =
      fun who => if who then -2 else 1 := by
  funext who
  cases who
  · exact pivot_punishment_eq_one
  · exact other_punishment_eq_neg_two

theorem all_normal : ∀ who, quittingPunishmentValue reward who ≤
    quittingSoloReward reward who who := by
  intro who
  cases who
  · rw [pivot_punishment_eq_one]
    norm_num [quittingSoloReward, reward]
  · rw [other_punishment_eq_neg_two]
    norm_num [quittingSoloReward, reward]

theorem normalized_other_punishment_eq_neg_one :
    quittingPunishmentValue
      (quittingSinglePivotNormalizedReward reward false) true = -1 := by
  rw [quittingPunishmentValue_singlePivotNormalized reward false true]
  · rw [other_punishment_eq_neg_two]
    norm_num [quittingSinglePivotOffset, quittingSoloReward, reward,
      quittingSingletonTerminal]
  · norm_num [quittingSoloReward, reward]
  · exact all_normal true

theorem original_allNever_payoff_zero (who : Bool) :
    quittingTerminalPayoff reward (quittingAlwaysContinueProfile reward) who = 0 :=
  quittingTerminalPayoff_quittingAlwaysContinue reward who

theorem normalized_allNever_payoff_zero (who : Bool) :
    quittingTerminalPayoff (quittingSinglePivotNormalizedReward reward false)
      (quittingAlwaysContinueProfile (quittingSinglePivotNormalizedReward reward false)) who =
        0 :=
  quittingTerminalPayoff_quittingAlwaysContinue _ who

theorem offset_eq : quittingSinglePivotOffset reward false = fun who => if who then -1 else 0 := by
  funext who
  cases who <;> norm_num [quittingSinglePivotOffset, reward, quittingSoloReward,
    quittingSingletonTerminal]

/-- At all-Never both actual payoffs are zero, while the naive affine image
has nonpivot coordinate `-1`. -/
theorem allNever_not_naive_affine :
    (fun who => quittingSinglePivotOffset reward false who +
      reward (quittingSingletonTerminal false) false *
        quittingTerminalPayoff (quittingSinglePivotNormalizedReward reward false)
          (quittingAlwaysContinueProfile
            (quittingSinglePivotNormalizedReward reward false)) who) ≠
      fun who => quittingTerminalPayoff reward (quittingAlwaysContinueProfile reward) who := by
  intro heq
  have h := congrFun heq true
  rw [normalized_allNever_payoff_zero, original_allNever_payoff_zero] at h
  norm_num [quittingSinglePivotOffset, reward, quittingSingletonTerminal] at h

/-- Literal signed-normal boundary package. -/
theorem signed_normal_boundary :
    (fun who => quittingPunishmentValue reward who) =
        (fun who => if who then -2 else 1) ∧
      quittingPunishmentValue
          (quittingSinglePivotNormalizedReward reward false) true = -1 ∧
      (∀ who, quittingTerminalPayoff reward
          (quittingAlwaysContinueProfile reward) who = 0) ∧
      (∀ who, quittingTerminalPayoff
          (quittingSinglePivotNormalizedReward reward false)
          (quittingAlwaysContinueProfile
            (quittingSinglePivotNormalizedReward reward false)) who = 0) ∧
      (fun who => quittingSinglePivotOffset reward false who +
        reward (quittingSingletonTerminal false) false *
          quittingTerminalPayoff (quittingSinglePivotNormalizedReward reward false)
            (quittingAlwaysContinueProfile
              (quittingSinglePivotNormalizedReward reward false)) who) ≠
        fun who => quittingTerminalPayoff reward
          (quittingAlwaysContinueProfile reward) who :=
  ⟨punishmentVector_eq, normalized_other_punishment_eq_neg_one,
    original_allNever_payoff_zero, normalized_allNever_payoff_zero,
    allNever_not_naive_affine⟩

end SinglePivotSignedNormalRegression
end GameTheory
