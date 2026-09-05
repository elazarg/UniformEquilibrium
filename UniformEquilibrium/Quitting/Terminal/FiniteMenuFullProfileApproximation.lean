import UniformEquilibrium.Quitting.Terminal.FiniteMenuEarlyAbsorptionNecessity
import UniformEquilibrium.Quitting.Terminal.TargetTail.UniformTargetTerminalSequence

/-! # Actual finite-menu approximation with full-deviation and payoff control -/

noncomputable section

namespace GameTheory

open Filter
open _root_.Math.Probability
open scoped Topology

variable {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]

/-- One actual finite-menu law approximates a given behavioral profile's payoff
and bounds its unrestricted exploitability. Its displayed deadline can exceed
any prescribed lower bound. No singleton-sign or normality assumption is used. -/
theorem exists_finiteDeadlineTimingProfile_approximation
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    {error : ℝ} (herror : 0 < error) (lowerDeadline : ℕ) :
    ∃ deadline : ℕ, lowerDeadline ≤ deadline ∧
      ∃ mixed : ι → PMF (QuittingFiniteDeadlineTimingAction deadline),
        quittingTerminalExploitability reward
            (quittingFiniteDeadlineTimingProfile reward deadline mixed) <
          quittingTerminalExploitability reward profile + error ∧
        ‖quittingTerminalPayoff reward
            (quittingFiniteDeadlineTimingProfile reward deadline mixed) -
          quittingTerminalPayoff reward profile‖ < error := by
  let laws := quittingBehaviorStoppingLaws reward profile
  let bound := quittingRewardBound reward
  have hbound : 0 ≤ bound := quittingRewardBound_nonneg reward
  have htolerance : 0 < error / (4 * (bound + 1)) := by positivity
  obtain ⟨cutoff, htail⟩ :=
    exists_horizon_sum_stoppingLawLateFiniteMass_lt laws htolerance
  let tailMass := ∑ player, stoppingLawLateFiniteMass (laws player) cutoff
  have htailMass : 0 ≤ tailMass := by
    exact Finset.sum_nonneg fun _ _ ↦ pmfFiniteComplementMass_nonneg _ _
  have hscaled : 4 * bound * tailMass < error := by
    have hpositive : 0 < 4 * (bound + 1) := by positivity
    have hmul := mul_lt_mul_of_pos_left htail hpositive
    have heq : 4 * (bound + 1) * (error / (4 * (bound + 1))) = error := by
      field_simp [ne_of_gt hpositive]
    rw [heq] at hmul
    change 4 * (bound + 1) * tailMass < error at hmul
    nlinarith
  let censored := censorLateFiniteStoppingLaws laws cutoff
  let censoredProfile := quittingStoppingLawProfile reward censored
  have hexploit : quittingTerminalExploitability reward censoredProfile <
      quittingTerminalExploitability reward profile + error := by
    have hstable := quittingTerminalExploitability_censored_le
      reward laws cutoff (abs_reward_le_quittingRewardBound reward)
    rw [quittingTerminalExploitability_stoppingLawProfile_behaviorLaws_eq] at hstable
    change quittingTerminalExploitability reward censoredProfile ≤
      quittingTerminalExploitability reward profile + 4 * bound * tailMass at hstable
    linarith
  have hpayoff : ‖quittingTerminalPayoff reward censoredProfile -
      quittingTerminalPayoff reward profile‖ < error := by
    have hnorm : ‖quittingTerminalPayoff reward censoredProfile -
        quittingTerminalPayoff reward profile‖ ≤ 2 * bound * tailMass := by
      apply (pi_norm_le_iff_of_nonneg (by positivity : 0 ≤ 2 * bound * tailMass)).mpr
      intro who
      have h := abs_expectedPayoff_censorLateFiniteStoppingLaws_sub_le
        reward laws cutoff who (abs_reward_le_quittingRewardBound reward)
      rw [← quittingTerminalPayoff_stoppingLawProfile_eq_expectedPayoff,
        quittingStoppingLawExpectedPayoff_behaviorStoppingLaws_eq_terminalPayoff] at h
      exact h
    have hsmall : 2 * bound * tailMass < error := by nlinarith
    exact hnorm.trans_lt hsmall
  let deadline := max (cutoff + 1) lowerDeadline
  have hcutoff : cutoff < deadline := by dsimp [deadline]; omega
  obtain ⟨mixed, hmixed⟩ :=
    exists_finiteDeadlineTimingLaws_of_censoredLaws laws cutoff deadline hcutoff
  have hprofile : quittingFiniteDeadlineTimingProfile reward deadline mixed =
      censoredProfile := finiteDeadlineTimingProfile_eq_stoppingLawProfile_of_laws
        reward deadline mixed censored hmixed
  refine ⟨deadline, Nat.le_max_right _ _, mixed, ?_, ?_⟩
  · simpa only [hprofile] using hexploit
  · simpa only [hprofile] using hpayoff

/-- A specified target is a uniform-equilibrium payoff exactly when actual
finite-menu laws approach that target with vanishing unrestricted exploitability.
The same law satisfies both bounds, at an arbitrarily large displayed deadline. -/
theorem isUniformEquilibriumPayoff_iff_finiteMenu_fullCap_target_approximation
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (target : Payoff ι) :
    (quittingGame reward).IsUniformEquilibriumPayoff none target ↔
      ∀ error : ℝ, 0 < error → ∀ lowerDeadline : ℕ,
        ∃ deadline : ℕ, lowerDeadline ≤ deadline ∧
          ∃ mixed : ι → PMF (QuittingFiniteDeadlineTimingAction deadline),
            quittingTerminalExploitability reward
              (quittingFiniteDeadlineTimingProfile reward deadline mixed) < error ∧
            ‖quittingTerminalPayoff reward
                (quittingFiniteDeadlineTimingProfile reward deadline mixed) - target‖ < error := by
  constructor
  · intro huniform error herror lowerDeadline
    obtain ⟨profiles, htarget, hexploit⟩ :=
      exists_terminalProfile_sequence_exploitability_tendsto_zero_of_uniformPayoff
        reward target huniform
    have hhalf : 0 < error / 2 := half_pos herror
    have heventExploit : ∀ᶠ n in atTop,
        quittingTerminalExploitability reward (profiles n) < error / 2 :=
      hexploit.eventually (gt_mem_nhds hhalf)
    have heventPayoff : ∀ᶠ n in atTop,
        ‖quittingTerminalPayoff reward (profiles n) - target‖ < error / 2 := by
      simpa only [Metric.mem_ball, dist_eq_norm] using
        htarget.eventually (Metric.ball_mem_nhds target hhalf)
    obtain ⟨n, hnExploit, hnPayoff⟩ := (heventExploit.and heventPayoff).exists
    obtain ⟨deadline, hdeadline, mixed, hmenuExploit, hmenuPayoff⟩ :=
      exists_finiteDeadlineTimingProfile_approximation
        reward (profiles n) hhalf lowerDeadline
    refine ⟨deadline, hdeadline, mixed, ?_, ?_⟩
    · linarith
    · calc
        _ ≤ ‖quittingTerminalPayoff reward
              (quittingFiniteDeadlineTimingProfile reward deadline mixed) -
                quittingTerminalPayoff reward (profiles n)‖ +
            ‖quittingTerminalPayoff reward (profiles n) - target‖ := by
          simpa only [dist_eq_norm] using dist_triangle
            (quittingTerminalPayoff reward
              (quittingFiniteDeadlineTimingProfile reward deadline mixed))
            (quittingTerminalPayoff reward (profiles n)) target
        _ < error / 2 + error / 2 := add_lt_add hmenuPayoff hnPayoff
        _ = error := by ring
  · intro hmenus
    apply quittingGame_isUniformEquilibriumPayoff_of_terminalTargetAcceptance reward target
    intro error herror
    obtain ⟨deadline, _, mixed, hexploit, hpayoff⟩ := hmenus error herror 0
    refine ⟨quittingFiniteDeadlineTimingProfile reward deadline mixed,
      isεAsymptoticNash_of_quittingTerminalExploitability_le _ hexploit.le, ?_⟩
    intro who
    have hcoordinate :=
      (pi_norm_le_iff_of_nonneg herror.le).mp hpayoff.le who
    exact hcoordinate

end GameTheory
