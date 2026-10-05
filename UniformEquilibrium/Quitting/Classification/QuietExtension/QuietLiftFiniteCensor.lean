import UniformEquilibrium.Quitting.Classification.PlayerDeletionLift
import UniformEquilibrium.Quitting.Terminal.StoppingLawExploitability
import UniformEquilibrium.Quitting.Terminal.FiniteDeadlineStoppingLawRealization
import UniformEquilibrium.Quitting.Paths.LateFiniteStoppingLawCensor
import UniformEquilibrium.Quitting.Paths.StoppingLawExploitabilityCongruence
import MathUE.ProbabilityMassFunction.ExactLateFiniteCensor
import MathUE.ProbabilityMassFunction.LateFiniteStoppingLawJointNever

/-! # Finite censoring of actual quiet lifts

Only child finite tails move to Never. Outsiders remain literally Never;
the entire parent stopping-law family and full behavioral regret are retained.
-/

noncomputable section

namespace GameTheory

open _root_.Math.Probability

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Quiet outsiders contribute no finite tail; the parent discarded mass is
exactly the sum of the actual child discarded masses. -/
theorem sum_lateFiniteMass_quietLift_eq
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (deleted : ι → Prop) [DecidablePred deleted]
    (profile : (quittingGame (quittingDeleteReward reward deleted)).BehaviorProfile)
    (cutoff : ℕ) :
    (∑ who, stoppingLawLateFiniteMass
      (quittingBehaviorStoppingLaw reward
        (quittingLiftDeletedProfile reward deleted profile who)) cutoff) =
      ∑ who, stoppingLawLateFiniteMass
        (quittingBehaviorStoppingLaw (quittingDeleteReward reward deleted) (profile who))
        cutoff := by
  rw [← Fintype.sum_subtype_add_sum_subtype deleted]
  have houtside : (∑ who : {who : ι // deleted who}, stoppingLawLateFiniteMass
      (quittingBehaviorStoppingLaw reward
        (quittingLiftDeletedProfile reward deleted profile who)) cutoff) = 0 := by
    apply Finset.sum_eq_zero
    intro who _
    rw [quittingBehaviorStoppingLaw_liftDeletedProfile_of_deleted reward deleted profile who.2]
    exact stoppingLawLateFiniteMass_eq_zero_of_support_prefix _ cutoff (by simp)
  rw [houtside, zero_add]
  apply Finset.sum_congr rfl
  intro who _
  rw [quittingBehaviorStoppingLaw_liftDeletedProfile]

/-- Quiet lift and finite censor commute at the level of the full actual
stopping-law family. Equality of arbitrary behavioral presentations is not needed. -/
theorem quittingBehaviorStoppingLaws_quietLift_censored_eq
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (deleted : ι → Prop) [DecidablePred deleted]
    (profile : (quittingGame (quittingDeleteReward reward deleted)).BehaviorProfile)
    (cutoff : ℕ) :
    quittingBehaviorStoppingLaws reward
        (quittingLiftDeletedProfile reward deleted
          (quittingStoppingLawProfile (quittingDeleteReward reward deleted)
            (censorLateFiniteStoppingLaws
              (quittingBehaviorStoppingLaws (quittingDeleteReward reward deleted) profile)
              cutoff))) =
      censorLateFiniteStoppingLaws
        (quittingBehaviorStoppingLaws reward
          (quittingLiftDeletedProfile reward deleted profile)) cutoff := by
  funext who
  by_cases hwho : deleted who
  · change quittingBehaviorStoppingLaw reward _ = censorLateFiniteStoppingLaw
      (quittingBehaviorStoppingLaw reward _) cutoff
    rw [quittingBehaviorStoppingLaw_liftDeletedProfile_of_deleted reward deleted _ hwho,
      quittingBehaviorStoppingLaw_liftDeletedProfile_of_deleted reward deleted _ hwho]
    exact (censorLateFiniteStoppingLaw_eq_self_of_support_prefix _ cutoff (by simp)).symm
  · let child : QuittingChildPlayer deleted := ⟨who, hwho⟩
    change quittingBehaviorStoppingLaw reward
      (quittingLiftDeletedProfile reward deleted _ child.1) = censorLateFiniteStoppingLaw
        (quittingBehaviorStoppingLaw reward
          (quittingLiftDeletedProfile reward deleted profile child.1)) cutoff
    rw [quittingBehaviorStoppingLaw_liftDeletedProfile,
      quittingBehaviorStoppingLaw_liftDeletedProfile]
    exact congrFun (quittingBehaviorStoppingLaws_stoppingLawProfile
      (quittingDeleteReward reward deleted) _) child

/-- The parent reward bound controls censoring of the child inside its actual
quiet lift, uniformly over every behavioral replacement. -/
theorem quittingTerminalExploitability_quietLift_censored_le [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (deleted : ι → Prop) [DecidablePred deleted]
    (profile : (quittingGame (quittingDeleteReward reward deleted)).BehaviorProfile)
    (cutoff : ℕ) {bound : ℝ}
    (hreward : ∀ terminal who, |reward terminal who| ≤ bound) :
    quittingTerminalExploitability reward
        (quittingLiftDeletedProfile reward deleted
          (quittingStoppingLawProfile (quittingDeleteReward reward deleted)
            (censorLateFiniteStoppingLaws
              (quittingBehaviorStoppingLaws (quittingDeleteReward reward deleted) profile)
              cutoff))) ≤
      quittingTerminalExploitability reward
          (quittingLiftDeletedProfile reward deleted profile) +
        4 * bound * ∑ who, stoppingLawLateFiniteMass
          (quittingBehaviorStoppingLaw (quittingDeleteReward reward deleted) (profile who))
          cutoff := by
  have h := quittingTerminalExploitability_censored_le reward
    (quittingBehaviorStoppingLaws reward
      (quittingLiftDeletedProfile reward deleted profile)) cutoff hreward
  rw [quittingTerminalExploitability_stoppingLawProfile_behaviorLaws_eq] at h
  simp only [quittingBehaviorStoppingLaws] at h
  rw [sum_lateFiniteMass_quietLift_eq] at h
  refine le_trans ?_ h
  apply le_of_eq
  apply quittingTerminalExploitability_eq_of_behaviorStoppingLaws_eq
  rw [quittingBehaviorStoppingLaws_quietLift_censored_eq,
    quittingBehaviorStoppingLaws_stoppingLawProfile]

/-- An actual finite independent child menu approximates the displayed quiet
lift, retaining its full regret bound and controlling joint Never. -/
theorem exists_finiteQuietLift_of_profile [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (deleted : ι → Prop) [DecidablePred deleted]
    [Nonempty (QuittingChildPlayer deleted)]
    (profile : (quittingGame (quittingDeleteReward reward deleted)).BehaviorProfile)
    {tolerance : ℝ} (htolerance : 0 < tolerance) {bound : ℝ} (hbound : 0 ≤ bound)
    (hreward : ∀ terminal who, |reward terminal who| ≤ bound) :
    ∃ deadline : ℕ, 0 < deadline ∧
      ∃ mixed : QuittingChildPlayer deleted → PMF (QuittingFiniteDeadlineTimingAction deadline),
        quittingTerminalExploitability reward
            (quittingLiftDeletedProfile reward deleted
              (quittingFiniteDeadlineTimingProfile (quittingDeleteReward reward deleted)
                deadline mixed)) ≤
          quittingTerminalExploitability reward
              (quittingLiftDeletedProfile reward deleted profile) + 4 * bound * tolerance ∧
        (∏ who, (quittingBehaviorStoppingLaw (quittingDeleteReward reward deleted)
          (quittingFiniteDeadlineTimingProfile (quittingDeleteReward reward deleted)
            deadline mixed who) none).toReal) ≤
          (∏ who, (quittingBehaviorStoppingLaw
            (quittingDeleteReward reward deleted) (profile who) none).toReal) +
            2 * tolerance := by
  let childReward := quittingDeleteReward reward deleted
  let laws := quittingBehaviorStoppingLaws childReward profile
  obtain ⟨cutoff, htail⟩ := exists_horizon_sum_stoppingLawLateFiniteMass_lt laws htolerance
  let censored := censorLateFiniteStoppingLaws laws cutoff
  obtain ⟨mixed, hmixed⟩ :=
    exists_finiteDeadlineTimingLaws_of_censoredLaws laws cutoff (cutoff + 1) (by omega)
  have hprofile := finiteDeadlineTimingProfile_eq_stoppingLawProfile_of_laws
    childReward (cutoff + 1) mixed censored hmixed
  refine ⟨cutoff + 1, by omega, mixed, ?_, ?_⟩
  · rw [hprofile]
    exact (quittingTerminalExploitability_quietLift_censored_le
      reward deleted profile cutoff hreward).trans
      (add_le_add le_rfl (mul_le_mul_of_nonneg_left htail.le (by positivity)))
  · rw [hprofile]
    change (∏ who, (quittingBehaviorStoppingLaws childReward
      (quittingStoppingLawProfile childReward censored) who none).toReal) ≤ _
    rw [quittingBehaviorStoppingLaws_stoppingLawProfile]
    exact (prod_censorLateFiniteStoppingLaw_none_le laws cutoff).trans
      (add_le_add le_rfl (mul_le_mul_of_nonneg_left htail.le (by norm_num)))

end GameTheory
