import UniformEquilibrium.Quitting.Terminal.PivotRepairFiniteLP
import UniformEquilibrium.Quitting.Terminal.FiniteDeadlineStoppingLawRealization
import UniformEquilibrium.Quitting.Paths.FiniteSupportStoppingLawSurvival
import UniformEquilibrium.Quitting.Paths.LateFiniteStoppingLawCensor
import MathUE.ProbabilityMassFunction.ExactLateFiniteCensor

/-! # One-coordinate finite censor with exact displayed survival -/

noncomputable section

namespace GameTheory.QuittingPivotRepairLPInput

open _root_.Math.Probability
open scoped BigOperators

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
variable (input : QuittingPivotRepairLPInput reward)

omit [Fintype ι] [DecidableEq ι] in
theorem opponents_support_prefix {cutoff : ℕ} (hcutoff : input.deadline ≤ cutoff + 1)
    (who : ι) (hwho : who ≠ input.pivot) :
    (input.opponents who).support ⊆ ↑(stoppingLawFinitePrefix cutoff) := by
  intro choice hchoice
  rcases input.opponents_finite who hwho choice hchoice with rfl | ⟨time, htime, rfl⟩
  · exact none_mem_stoppingLawFinitePrefix cutoff
  · exact (some_mem_stoppingLawFinitePrefix cutoff time).mpr (by omega)

omit [Fintype ι] in
/-- Censoring this profile changes only the pivot marginal. -/
theorem censor_laws_eq_update (law : PMF (Option ℕ)) {cutoff : ℕ}
    (hcutoff : input.deadline ≤ cutoff + 1) :
    censorLateFiniteStoppingLaws (Function.update input.opponents input.pivot law) cutoff =
      Function.update input.opponents input.pivot (censorLateFiniteStoppingLaw law cutoff) := by
  funext who
  by_cases hwho : who = input.pivot
  · subst who
    simp [censorLateFiniteStoppingLaws]
  · simp only [censorLateFiniteStoppingLaws, Function.update_of_ne hwho]
    exact censorLateFiniteStoppingLaw_eq_self_of_support_prefix _ cutoff
      (input.opponents_support_prefix hcutoff who hwho)

/-- The sum of censored finite masses is exactly the pivot's discarded mass. -/
theorem sum_lateFiniteMass_update_eq (law : PMF (Option ℕ)) {cutoff : ℕ}
    (hcutoff : input.deadline ≤ cutoff + 1) :
    (∑ who, stoppingLawLateFiniteMass
      (Function.update input.opponents input.pivot law who) cutoff) =
      stoppingLawLateFiniteMass law cutoff := by
  rw [Finset.sum_eq_single input.pivot]
  · simp
  · intro who _ hwho
    rw [Function.update_of_ne hwho]
    exact stoppingLawLateFiniteMass_eq_zero_of_support_prefix _ cutoff
      (input.opponents_support_prefix hcutoff who hwho)
  · simp

/-- The joint Never mass after censoring has its exact one-coordinate increment. -/
theorem prod_censored_none_eq (law : PMF (Option ℕ)) {cutoff : ℕ}
    (hcutoff : input.deadline ≤ cutoff + 1) :
    (∏ who, (censorLateFiniteStoppingLaws
      (Function.update input.opponents input.pivot law) cutoff who none).toReal) =
      ((law none).toReal + stoppingLawLateFiniteMass law cutoff) *
        ∏ who ∈ Finset.univ.erase input.pivot, (input.opponents who none).toReal := by
  rw [input.censor_laws_eq_update law hcutoff,
    ← Finset.mul_prod_erase _ _ (Finset.mem_univ input.pivot)]
  simp only [Function.update_self, censorLateFiniteStoppingLaw_none_toReal_eq]
  congr 1
  apply Finset.prod_congr rfl
  intro who hwho
  rw [Function.update_of_ne (Finset.ne_of_mem_erase hwho)]

/-- An actual finite menu retains the precise one-coordinate censor, full
behavioral regret control under a supplied reward bound, and exact survival. -/
theorem exists_finite_censor_menu_of_reward_bound
    (law : PMF (Option ℕ)) (cutoff : ℕ)
    (hcutoff : input.deadline ≤ cutoff + 1) (horizon : ℕ) (hhorizon : 1 ≤ horizon)
    (lowerDeadline : ℕ) (bound : ℝ)
    (hreward : ∀ terminal player, |reward terminal player| ≤ bound) :
    letI : Nonempty ι := ⟨input.pivot⟩
    ∃ deadline : ℕ, max horizon lowerDeadline ≤ deadline ∧
      ∃ mixed : ι → PMF (QuittingFiniteDeadlineTimingAction deadline),
        (∀ who, (quittingFiniteDeadlineTimingLaw (mixed who)).toPMF =
          Function.update input.opponents input.pivot
            (censorLateFiniteStoppingLaw law cutoff) who) ∧
        quittingTerminalExploitability reward
            (quittingFiniteDeadlineTimingProfile reward deadline mixed) ≤
          quittingTerminalExploitability reward
              (quittingStoppingLawProfile reward
                (Function.update input.opponents input.pivot law)) +
            4 * bound * stoppingLawLateFiniteMass law cutoff ∧
        quittingJointSurvivalWeight
            (quittingProfileLiveRoot reward
              (quittingFiniteDeadlineTimingProfile reward deadline mixed)) 0 (deadline - horizon) =
          ((law none).toReal + stoppingLawLateFiniteMass law cutoff) *
            ∏ who ∈ Finset.univ.erase input.pivot, (input.opponents who none).toReal := by
  letI : Nonempty ι := ⟨input.pivot⟩
  let laws := Function.update input.opponents input.pivot law
  let censored := censorLateFiniteStoppingLaws laws cutoff
  let deadline := max (cutoff + 1 + horizon) lowerDeadline
  have hlarge : cutoff < deadline := by dsimp [deadline]; omega
  obtain ⟨mixed, hmixed⟩ :=
    exists_finiteDeadlineTimingLaws_of_censoredLaws laws cutoff deadline hlarge
  have hprofile : quittingFiniteDeadlineTimingProfile reward deadline mixed =
      quittingStoppingLawProfile reward censored :=
    finiteDeadlineTimingProfile_eq_stoppingLawProfile_of_laws
      reward deadline mixed censored hmixed
  refine ⟨deadline, by dsimp [deadline]; omega, mixed, ?_, ?_, ?_⟩
  · intro who
    rw [hmixed who]
    exact congrFun (input.censor_laws_eq_update law hcutoff) who
  · rw [hprofile]
    have h := quittingTerminalExploitability_censored_le reward laws cutoff hreward
    rw [input.sum_lateFiniteMass_update_eq law hcutoff] at h
    exact h
  · rw [hprofile, quittingJointSurvivalWeight_eq_prod_none_of_support_prefix
      reward _ cutoff (deadline - horizon) (by dsimp [deadline]; omega)]
    · have hlaws := quittingBehaviorStoppingLaws_stoppingLawProfile reward censored
      change (∏ who, (quittingBehaviorStoppingLaws reward
        (quittingStoppingLawProfile reward censored) who none).toReal) = _
      rw [hlaws]
      exact input.prod_censored_none_eq law hcutoff
    · intro who
      change (quittingBehaviorStoppingLaws reward
        (quittingStoppingLawProfile reward censored) who).support ⊆ _
      rw [quittingBehaviorStoppingLaws_stoppingLawProfile]
      exact censorLateFiniteStoppingLaw_support_subset (laws who) cutoff

/-- The summed project reward bound is a short specialization of the
supplied-coordinate-bound finite-censor theorem. -/
theorem exists_finite_censor_menu (law : PMF (Option ℕ)) (cutoff : ℕ)
    (hcutoff : input.deadline ≤ cutoff + 1) (horizon : ℕ) (hhorizon : 1 ≤ horizon)
    (lowerDeadline : ℕ) :
    letI : Nonempty ι := ⟨input.pivot⟩
    ∃ deadline : ℕ, max horizon lowerDeadline ≤ deadline ∧
      ∃ mixed : ι → PMF (QuittingFiniteDeadlineTimingAction deadline),
        (∀ who, (quittingFiniteDeadlineTimingLaw (mixed who)).toPMF =
          Function.update input.opponents input.pivot
            (censorLateFiniteStoppingLaw law cutoff) who) ∧
        quittingTerminalExploitability reward
            (quittingFiniteDeadlineTimingProfile reward deadline mixed) ≤
          quittingTerminalExploitability reward
              (quittingStoppingLawProfile reward
                (Function.update input.opponents input.pivot law)) +
            4 * quittingRewardBound reward * stoppingLawLateFiniteMass law cutoff ∧
        quittingJointSurvivalWeight
            (quittingProfileLiveRoot reward
              (quittingFiniteDeadlineTimingProfile reward deadline mixed)) 0 (deadline - horizon) =
          ((law none).toReal + stoppingLawLateFiniteMass law cutoff) *
            ∏ who ∈ Finset.univ.erase input.pivot, (input.opponents who none).toReal := by
  exact input.exists_finite_censor_menu_of_reward_bound law cutoff hcutoff horizon hhorizon
    lowerDeadline (quittingRewardBound reward) (abs_reward_le_quittingRewardBound reward)

end GameTheory.QuittingPivotRepairLPInput
