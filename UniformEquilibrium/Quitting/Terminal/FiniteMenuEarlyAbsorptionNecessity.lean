import UniformEquilibrium.Quitting.Paths.LateFiniteStoppingLawCensor
import UniformEquilibrium.Quitting.Terminal.SingletonJointNeverDebt
import UniformEquilibrium.Quitting.Terminal.FiniteMenuEarlyAbsorption
import UniformEquilibrium.Quitting.Terminal.FiniteMenuEarlyAbsorptionCompletion
import UniformEquilibrium.Quitting.Terminal.TargetTail.TerminalUniformPayoffSelection
import MathUE.ProbabilityMassFunction.FiniteStoppingTimeMenu

/-! # Positive-singleton necessity of finite-menu early absorption -/

noncomputable section

namespace GameTheory

open StochasticGame
open _root_.Math.Probability _root_.Math.Probability.DiscreteHazard

variable {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]

omit [Fintype ι] [DecidableEq ι] [Nonempty ι] in
theorem exists_finiteDeadlineTimingLaws_of_censoredLaws
    (laws : ι → PMF (Option ℕ)) (cutoff deadline : ℕ)
    (hdeadline : cutoff < deadline) :
    ∃ mixed : ι → PMF (QuittingFiniteDeadlineTimingAction deadline),
      ∀ who, (quittingFiniteDeadlineTimingLaw (mixed who)).toPMF =
        censorLateFiniteStoppingLaw (laws who) cutoff := by
  classical
  have hsupport (who : ι) (time : ℕ) (htime : deadline ≤ time) :
      censorLateFiniteStoppingLaw (laws who) cutoff (some time) = 0 := by
    have hnot : some time ∉ stoppingLawFinitePrefix cutoff := by
      simp
      omega
    have hnotSupport : some time ∉
        (censorLateFiniteStoppingLaw (laws who) cutoff).support :=
      fun hmem => hnot
        (censorLateFiniteStoppingLaw_support_subset (laws who) cutoff hmem)
    by_contra hne
    exact hnotSupport (by simpa [PMF.mem_support_iff] using hne)
  have hexists (who : ι) : ∃ law : PMF (Option (Fin deadline)),
      law.map (finiteStoppingTimeDecode deadline) =
        censorLateFiniteStoppingLaw (laws who) cutoff := by
    obtain ⟨law, hlaw, _⟩ := exists_finiteStoppingTimePMF_map_eq
      (censorLateFiniteStoppingLaw (laws who) cutoff) deadline (hsupport who)
    exact ⟨law, hlaw⟩
  choose mixed hmixed using hexists
  refine ⟨mixed, fun who => ?_⟩
  rw [quittingFiniteDeadlineTimingLaw, CompactStoppingLaw.toPMF_ofPMF]
  have hmaps : (mixed who).map quittingFiniteDeadlineTimingActionTime =
      (mixed who).map (finiteStoppingTimeDecode deadline) := by
    congr 1
    funext action
    cases action <;> rfl
  rw [hmaps, hmixed who]

/-- Canonical reconstruction preserves literal terminal exploitability. -/
theorem quittingTerminalExploitability_stoppingLawProfile_behaviorLaws_eq
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) :
    quittingTerminalExploitability reward
        (quittingStoppingLawProfile reward
          (quittingBehaviorStoppingLaws reward profile)) =
      quittingTerminalExploitability reward profile := by
  unfold quittingTerminalExploitability
  congr 1
  funext who
  rw [← quittingStoppingLawCap_behaviorStoppingLaws_eq_continuationBestResponseValue,
    quittingBehaviorStoppingLaws_stoppingLawProfile,
    quittingStoppingLawCap_behaviorStoppingLaws_eq_continuationBestResponseValue,
    quittingTerminalPayoff_stoppingLawProfile_eq_expectedPayoff,
    quittingStoppingLawExpectedPayoff_behaviorStoppingLaws_eq_terminalPayoff]

omit [DecidableEq ι] [Nonempty ι] in
/-- A finite-support stopping-law profile realized on a deadline has exactly
the canonical stopping-law behavioral profile. -/
theorem finiteDeadlineTimingProfile_eq_stoppingLawProfile_of_laws
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (deadline : ℕ)
    (mixed : ι → PMF (QuittingFiniteDeadlineTimingAction deadline))
    (laws : ι → PMF (Option ℕ))
    (hlaws : ∀ who, (quittingFiniteDeadlineTimingLaw (mixed who)).toPMF = laws who) :
    quittingFiniteDeadlineTimingProfile reward deadline mixed =
      quittingStoppingLawProfile reward laws := by
  funext who
  unfold quittingFiniteDeadlineTimingProfile quittingCompactStoppingLawProfile
    quittingStoppingLawProfile
  rw [← hlaws who]

/-- Beyond its finite support, a stopping law's inclusive survival is exactly
its retained Never atom. -/
theorem stoppingLawSurvival_eq_none_of_support_prefix
    (law : PMF (Option ℕ)) (cutoff time : ℕ) (htime : cutoff < time)
    (hsupport : law.support ⊆ ↑(stoppingLawFinitePrefix cutoff)) :
    StoppingLaw.survival law time = (law none).toReal := by
  have htotal : (law none).toReal +
      ∑ date ∈ Finset.range time, (law (some date)).toReal = 1 := by
    rw [← StoppingLaw.none_add_tsum_finiteMass law]
    congr 1
    symm
    apply tsum_eq_sum
    intro date hdate
    have hnot : some date ∉ stoppingLawFinitePrefix cutoff := by
      rw [some_mem_stoppingLawFinitePrefix]
      have hle : time ≤ date := Nat.le_of_not_gt (by simpa using hdate)
      omega
    have hzero : law (some date) = 0 := by
      by_contra hne
      exact hnot (hsupport (by simpa [PMF.mem_support_iff] using hne))
    simp [StoppingLaw.finiteMass, hzero]
  unfold StoppingLaw.survival StoppingLaw.finiteMass
  linarith

omit [DecidableEq ι] [Nonempty ι] in
/-- Once every marginal has no finite atom after `cutoff`, joint live-spine
survival at a later date is exactly the product of the Never atoms. -/
theorem quittingJointSurvivalWeight_eq_prod_none_of_support_prefix
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (cutoff time : ℕ)
    (htime : cutoff < time)
    (hsupport : ∀ who,
      (quittingBehaviorStoppingLaw reward (profile who)).support ⊆
        ↑(stoppingLawFinitePrefix cutoff)) :
    quittingJointSurvivalWeight (quittingProfileLiveRoot reward profile) 0 time =
      ∏ who, (quittingBehaviorStoppingLaw reward (profile who) none).toReal := by
  rw [quittingJointSurvivalWeight_eq_prod]
  simp_rw [quittingStationaryContinueMass_eq_prod_continueProbability]
  rw [Finset.prod_comm]
  apply Finset.prod_congr rfl
  intro who _
  rw [← quittingHazardSurvival_eq_prod]
  have hhazard :
      (fun x => quittingProfileLiveRoot reward profile (0 + x) who) =
        quittingBehaviorLiveHazard reward (profile who) := by
    funext x
    simp only [quittingProfileLiveRoot, quittingBehaviorLiveHazard]
    congr 2 <;> omega
  rw [hhazard]
  rw [← stoppingLawSurvival_quittingBehaviorStoppingLaw]
  exact stoppingLawSurvival_eq_none_of_support_prefix
    _ cutoff time htime (hsupport who)

/-- A uniform-equilibrium payoff and one positive singleton produce the full
finite-menu early-absorption predicate, in its stated quantifier order. -/
theorem finiteMenuEarlyAbsorption_of_uniformEquilibriumPayoff_of_singleton_pos
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (owner : ι)
    (hsolo : 0 < reward (quittingSingletonTerminal owner) owner)
    (target : Payoff ι)
    (huniform : (quittingGame reward).IsUniformEquilibriumPayoff none target) :
    HasQuittingFiniteMenuEarlyAbsorption reward := by
  intro error herror horizon hhorizon reach hreach lowerDeadline
  let solo := reward (quittingSingletonTerminal owner) owner
  let budget := min error (solo * reach) / 2
  have hbudget : 0 < budget := by
    exact half_pos (lt_min herror (mul_pos hsolo hreach))
  obtain ⟨profile, hnash⟩ :=
    quittingGame_terminalNash_all_errors_of_isUniformEquilibriumPayoff
      reward target huniform (budget / 2) (half_pos hbudget)
  have hsourceExploit : quittingTerminalExploitability reward profile ≤ budget / 2 :=
    quittingTerminalExploitability_le_of_isεAsymptoticNash
      reward profile (le_of_lt (half_pos hbudget)) hnash
  let laws := quittingBehaviorStoppingLaws reward profile
  let bound := quittingRewardBound reward
  have htailError : 0 < budget / (8 * (bound + 1)) := by
    apply div_pos hbudget
    have : 0 ≤ bound := quittingRewardBound_nonneg reward
    positivity
  obtain ⟨cutoff, htail⟩ :=
    exists_horizon_sum_stoppingLawLateFiniteMass_lt laws htailError
  let censored := censorLateFiniteStoppingLaws laws cutoff
  let censoredProfile := quittingStoppingLawProfile reward censored
  have hcanonical : quittingTerminalExploitability reward
      (quittingStoppingLawProfile reward laws) =
        quittingTerminalExploitability reward profile := by
    exact quittingTerminalExploitability_stoppingLawProfile_behaviorLaws_eq
      reward profile
  have hcensoredExploit :
      quittingTerminalExploitability reward censoredProfile < budget := by
    have hstable := quittingTerminalExploitability_censored_le
      reward laws cutoff (abs_reward_le_quittingRewardBound reward)
    change quittingTerminalExploitability reward censoredProfile ≤ _ at hstable
    rw [hcanonical] at hstable
    have hbound : 0 ≤ bound := quittingRewardBound_nonneg reward
    have hscaled : 4 * bound *
        (∑ player, stoppingLawLateFiniteMass (laws player) cutoff) < budget / 2 := by
      have hpositive : 0 < 4 * (bound + 1) := by positivity
      have hmul := mul_lt_mul_of_pos_left htail hpositive
      have heq : 4 * (bound + 1) * (budget / (8 * (bound + 1))) = budget / 2 := by
        field_simp [ne_of_gt hpositive]
        ring
      rw [heq] at hmul
      have hsumNonneg : 0 ≤ ∑ player,
          stoppingLawLateFiniteMass (laws player) cutoff := by
        apply Finset.sum_nonneg
        intro player _
        exact pmfFiniteComplementMass_nonneg _ _
      nlinarith
    linarith
  let deadline := max (cutoff + 1 + horizon) lowerDeadline
  have hcutoffDeadline : cutoff < deadline := by
    dsimp only [deadline]
    omega
  obtain ⟨mixed, hmixed⟩ := exists_finiteDeadlineTimingLaws_of_censoredLaws
    laws cutoff deadline hcutoffDeadline
  have hprofile : quittingFiniteDeadlineTimingProfile reward deadline mixed =
      censoredProfile := by
    apply finiteDeadlineTimingProfile_eq_stoppingLawProfile_of_laws
    exact hmixed
  have hfullNash : (quittingGame reward).IsεAsymptoticNash
      (quittingTerminalPayoff reward) error censoredProfile := by
    apply isεAsymptoticNash_of_quittingTerminalExploitability_le
    exact hcensoredExploit.le.trans (by
      dsimp only [budget]
      nlinarith [min_le_left error (solo * reach)])
  have hmenu : IsQuittingFiniteDeadlineNash reward deadline error mixed := by
    rw [isQuittingFiniteDeadlineNash_iff_pure]
    intro who action
    rw [hprofile]
    exact hfullNash who _
  have hneverSmall :
      (∏ player, (censored player none).toReal) < reach := by
    have hcharge :=
      prod_stoppingLaw_none_mul_singleton_le_terminalExploitability
        reward censoredProfile owner
    have hlaws : quittingBehaviorStoppingLaws reward censoredProfile = censored := by
      exact quittingBehaviorStoppingLaws_stoppingLawProfile reward censored
    change (∏ player,
        (quittingBehaviorStoppingLaws reward censoredProfile player none).toReal) *
          reward (quittingSingletonTerminal owner) owner ≤ _ at hcharge
    rw [hlaws] at hcharge
    have hbudgetReach : budget ≤ solo * reach / 2 := by
      exact div_le_div_of_nonneg_right (min_le_right _ _) (by norm_num)
    dsimp only [solo] at hbudgetReach
    nlinarith
  have hdeadline : max horizon lowerDeadline ≤ deadline := by
    dsimp only [deadline]
    omega
  refine ⟨deadline, hdeadline, mixed, hmenu, ?_⟩
  have htime : cutoff < deadline - horizon := by
    dsimp only [deadline]
    omega
  rw [hprofile, quittingJointSurvivalWeight_eq_prod_none_of_support_prefix
    reward censoredProfile cutoff (deadline - horizon) htime]
  · have hlaws := quittingBehaviorStoppingLaws_stoppingLawProfile reward censored
    change (∏ player,
      (quittingBehaviorStoppingLaws reward censoredProfile player none).toReal) < reach
    rw [hlaws]
    exact hneverSmall
  · intro who
    have hlaws := congrFun
      (quittingBehaviorStoppingLaws_stoppingLawProfile reward censored) who
    change (quittingBehaviorStoppingLaws reward censoredProfile who).support ⊆ _
    rw [hlaws]
    exact censorLateFiniteStoppingLaw_support_subset (laws who) cutoff

/-- With one positive singleton reward, finite-menu early absorption is
equivalent to existence of one uniform-equilibrium payoff. -/
theorem exists_uniformEquilibriumPayoff_iff_finiteMenuEarlyAbsorption_of_singleton_pos
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (owner : ι)
    (hsolo : 0 < reward (quittingSingletonTerminal owner) owner) :
    (∃ payoff : Payoff ι,
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff) ↔
      HasQuittingFiniteMenuEarlyAbsorption reward := by
  constructor
  · rintro ⟨payoff, hpayoff⟩
    exact finiteMenuEarlyAbsorption_of_uniformEquilibriumPayoff_of_singleton_pos
      reward owner hsolo payoff hpayoff
  · intro hearly
    exact exists_uniformEquilibriumPayoff_of_finiteMenuEarlyAbsorption reward hearly

end GameTheory
