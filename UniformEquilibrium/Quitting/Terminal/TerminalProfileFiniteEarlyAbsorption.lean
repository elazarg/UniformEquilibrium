import MathUE.ProbabilityMassFunction.LateFiniteStoppingLawJointNever
import UniformEquilibrium.Quitting.Paths.LateFiniteStoppingLawCensor
import UniformEquilibrium.Quitting.Paths.FiniteSupportStoppingLawSurvival
import UniformEquilibrium.Quitting.Paths.ProfileNeverMass
import UniformEquilibrium.Quitting.Terminal.FiniteDeadlineStoppingLawRealization
import UniformEquilibrium.Quitting.Terminal.FiniteMenuEarlyAbsorption
import UniformEquilibrium.Quitting.Terminal.StoppingLawExploitability

noncomputable section

namespace GameTheory

open _root_.Math.Probability _root_.Math.Probability.DiscreteHazard

variable {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]

/-- Finite timing menus with an unrestricted terminal-deviation cap and an
arbitrarily early absorption window. -/
def HasQuittingFiniteMenuFullEarlyAbsorption
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) : Prop :=
  ∀ error : ℝ, 0 < error → ∀ horizon : ℕ, 1 ≤ horizon →
    ∀ reach : ℝ, 0 < reach → ∀ lowerDeadline : ℕ,
      ∃ deadline : ℕ, max horizon lowerDeadline ≤ deadline ∧
        ∃ mixed : ι → PMF (QuittingFiniteDeadlineTimingAction deadline),
          quittingTerminalExploitability reward
              (quittingFiniteDeadlineTimingProfile reward deadline mixed) < error ∧
            quittingJointSurvivalWeight
                (quittingProfileLiveRoot reward
                  (quittingFiniteDeadlineTimingProfile reward deadline mixed))
                0 (deadline - horizon) < reach

/-- Actual low-exploitability profiles with zero joint Never mass can be
censored into finite menus while retaining their unrestricted cap. -/
theorem finiteMenuFullEarlyAbsorption_of_terminalProfiles_liveMassZero
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hsource : ∀ error : ℝ, 0 < error →
      ∃ profile : (quittingGame reward).BehaviorProfile,
        quittingTerminalExploitability reward profile < error ∧
        quittingLiveMassLimit reward profile = 0) :
    HasQuittingFiniteMenuFullEarlyAbsorption reward := by
  intro error herror horizon hhorizon reach hreach lowerDeadline
  obtain ⟨profile, hprofileExploit, hlive⟩ := hsource (error / 2) (half_pos herror)
  let laws := quittingBehaviorStoppingLaws reward profile
  let bound := quittingRewardBound reward
  let tolerance := min (error / (8 * (bound + 1))) (reach / 4)
  have htolerance : 0 < tolerance := by
    apply lt_min
    · apply div_pos herror
      have hbound := quittingRewardBound_nonneg reward
      positivity
    · positivity
  obtain ⟨cutoff, htail⟩ :=
    exists_horizon_sum_stoppingLawLateFiniteMass_lt laws htolerance
  let censored := censorLateFiniteStoppingLaws laws cutoff
  let censoredProfile := quittingStoppingLawProfile reward censored
  have hcanonical : quittingTerminalExploitability reward
      (quittingStoppingLawProfile reward laws) =
        quittingTerminalExploitability reward profile :=
    quittingTerminalExploitability_stoppingLawProfile_behaviorLaws_eq reward profile
  have hcensoredExploit :
      quittingTerminalExploitability reward censoredProfile < error := by
    have hstable := quittingTerminalExploitability_censored_le
      reward laws cutoff (abs_reward_le_quittingRewardBound reward)
    change quittingTerminalExploitability reward censoredProfile ≤ _ at hstable
    rw [hcanonical] at hstable
    have htailError :
        4 * bound * (∑ who, stoppingLawLateFiniteMass (laws who) cutoff) <
          error / 2 := by
      have hsmall := htail.trans_le (min_le_left _ _)
      have hbound := quittingRewardBound_nonneg reward
      have hpositive : 0 < 8 * (bound + 1) := by positivity
      have hscaled := mul_lt_mul_of_pos_left hsmall hpositive
      have hsum0 : 0 ≤ ∑ who, stoppingLawLateFiniteMass (laws who) cutoff :=
        Finset.sum_nonneg fun _ _ => pmfFiniteComplementMass_nonneg _ _
      have heq : 8 * (bound + 1) * (error / (8 * (bound + 1))) = error := by
        have hb1 : bound + 1 ≠ 0 := by positivity
        field_simp [hb1]
      rw [heq] at hscaled
      nlinarith
    linarith
  have horiginalNever : (∏ who, (laws who none).toReal) = 0 := by
    rw [← hlive, quittingLiveMassLimit_eq_prod_hazardNeverMass]
    apply Finset.prod_congr rfl
    intro who _
    exact quittingBehaviorStoppingLaw_none_toReal reward (profile who)
  have hcensoredNever : (∏ who, (censored who none).toReal) < reach := by
    have hle := prod_censorLateFiniteStoppingLaw_none_le laws cutoff
    rw [horiginalNever, zero_add] at hle
    have hsmall := htail.trans_le (min_le_right _ _)
    change (∏ who, (censored who none).toReal) ≤ _ at hle
    linarith
  let deadline := max (cutoff + 1 + horizon) lowerDeadline
  have hcutoff : cutoff < deadline := by
    dsimp [deadline]
    omega
  obtain ⟨mixed, hmixed⟩ :=
    exists_finiteDeadlineTimingLaws_of_censoredLaws laws cutoff deadline hcutoff
  have hprofile : quittingFiniteDeadlineTimingProfile reward deadline mixed =
      censoredProfile :=
    finiteDeadlineTimingProfile_eq_stoppingLawProfile_of_laws
      reward deadline mixed censored hmixed
  refine ⟨deadline, ?_, mixed, ?_, ?_⟩
  · dsimp [deadline]
    omega
  · rwa [hprofile]
  · have htime : cutoff < deadline - horizon := by
      dsimp [deadline]
      omega
    rw [hprofile, quittingJointSurvivalWeight_eq_prod_none_of_support_prefix
      reward censoredProfile cutoff (deadline - horizon) htime]
    · have hlaws := quittingBehaviorStoppingLaws_stoppingLawProfile reward censored
      change (∏ who,
        (quittingBehaviorStoppingLaws reward censoredProfile who none).toReal) < reach
      rw [hlaws]
      exact hcensoredNever
    · intro who
      have hlaws := congrFun
        (quittingBehaviorStoppingLaws_stoppingLawProfile reward censored) who
      change (quittingBehaviorStoppingLaws reward censoredProfile who).support ⊆ _
      rw [hlaws]
      exact censorLateFiniteStoppingLaw_support_subset (laws who) cutoff

/-- The full-cap construction in particular satisfies every displayed pure
finite-menu Nash comparison. -/
theorem finiteMenuEarlyAbsorption_of_terminalProfiles_liveMassZero
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hsource : ∀ error : ℝ, 0 < error →
      ∃ profile : (quittingGame reward).BehaviorProfile,
        quittingTerminalExploitability reward profile < error ∧
        quittingLiveMassLimit reward profile = 0) :
    HasQuittingFiniteMenuEarlyAbsorption reward := by
  intro error herror horizon hhorizon reach hreach lowerDeadline
  obtain ⟨deadline, hdeadline, mixed, hexploit, hsurvival⟩ :=
    finiteMenuFullEarlyAbsorption_of_terminalProfiles_liveMassZero reward hsource
      error herror horizon hhorizon reach hreach lowerDeadline
  refine ⟨deadline, hdeadline, mixed, ?_, hsurvival⟩
  rw [isQuittingFiniteDeadlineNash_iff_pure]
  have hnash := isεAsymptoticNash_of_quittingTerminalExploitability_le
    (quittingFiniteDeadlineTimingProfile reward deadline mixed) hexploit.le
  exact fun who action ↦ hnash who _

end GameTheory
