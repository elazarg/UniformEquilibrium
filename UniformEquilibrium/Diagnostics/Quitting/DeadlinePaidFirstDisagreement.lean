import MathUE.ProbabilityMassFunction.BoundedSupportAverage
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticPaidFirstDisagreement
import UniformEquilibrium.Quitting.Paths.BehaviorStoppingPayoff
import UniformEquilibrium.Quitting.Terminal.ExploitabilityGap
import UniformEquilibrium.Quitting.Terminal.FiniteDeadlineCapSelection

/-! # Paid first disagreement before a sure opponent's deadline -/

noncomputable section
namespace GameTheory

open Math.Probability
open Math.ProbabilityMassFunction

variable {ι : Type} [Fintype ι] [DecidableEq ι]

private theorem HasTerminalExploitabilityGap.exists_supported_pair_with_gain
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    {gap : ℝ} (exploit : HasTerminalExploitabilityGap reward gap)
    (profile : (quittingGame reward).BehaviorProfile) :
    ∃ observer, ∃ deviation : (quittingGame reward).BehaviorStrategy observer,
      gap ≤ quittingTerminalPayoff reward
          (Function.update profile observer deviation) observer -
        quittingTerminalPayoff reward profile observer ∧
      ∃ source receiving,
        source ∈ (quittingBehaviorStoppingLaw reward (profile observer)).support ∧
        receiving ∈ (quittingBehaviorStoppingLaw reward deviation).support ∧
        gap ≤ quittingPureTimeDeviationPayoff reward profile observer receiving -
          quittingPureTimeDeviationPayoff reward profile observer source := by
  obtain ⟨observer, deviation, hgain⟩ := exploit profile
  let value : Option ℕ → ℝ :=
    quittingPureTimeDeviationPayoff reward profile observer
  have hvalue : ∀ quitTime, |value quitTime| ≤ quittingRewardBound reward := by
    intro quitTime
    exact abs_quittingTerminalPayoff_le reward _ observer
      (abs_reward_le_quittingRewardBound reward)
  have hdeviation : quittingTerminalPayoff reward
      (Function.update profile observer deviation) observer =
      Math.Probability.expect
        (quittingBehaviorStoppingLaw reward deviation) value :=
    quittingTerminalPayoff_update_eq_expect_stoppingLaw_pureTime
      reward profile observer deviation
  have hprescribed : quittingTerminalPayoff reward profile observer =
      Math.Probability.expect
        (quittingBehaviorStoppingLaw reward (profile observer)) value := by
    have h := quittingTerminalPayoff_update_eq_expect_stoppingLaw_pureTime
      reward profile observer (profile observer)
    rw [Function.update_eq_self] at h
    exact h
  obtain ⟨receiving, source, hreceiving, hsource, havg⟩ :=
    exists_support_pair_expect_sub_le_sub
      (quittingBehaviorStoppingLaw reward deviation)
      (quittingBehaviorStoppingLaw reward (profile observer)) value value
      hvalue hvalue
  have hgain' : gap ≤ quittingTerminalPayoff reward
      (Function.update profile observer deviation) observer -
        quittingTerminalPayoff reward profile observer := by
    linarith
  refine ⟨observer, deviation, hgain', source, receiving,
    hsource, hreceiving, ?_⟩
  calc
    gap ≤ quittingTerminalPayoff reward
        (Function.update profile observer deviation) observer -
      quittingTerminalPayoff reward profile observer := hgain'
    _ = Math.Probability.expect
          (quittingBehaviorStoppingLaw reward deviation) value -
        Math.Probability.expect
          (quittingBehaviorStoppingLaw reward (profile observer)) value := by
      rw [hdeviation, hprescribed]
    _ ≤ value receiving - value source := havg

theorem quittingOpponentSurvivalWeight_eq_zero_of_sureOpponent_before
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    {observer owner : ι} {deadline start : ℕ}
    (hne : owner ≠ observer)
    (hsure : quittingProfileLiveRoot reward profile deadline owner = PMF.pure true)
    (hbefore : deadline < start) :
    quittingOpponentSurvivalWeight
      (quittingProfileLiveRoot reward profile) observer 0 start = 0 := by
  unfold quittingOpponentSurvivalWeight
  apply Finset.prod_eq_zero (show deadline ∈ Finset.range start by simpa)
  unfold quittingFixedOpponentsContinueMass
  apply quittingStationaryContinueMass_of_sureQuitter (quitter := owner)
  simp only [Nat.zero_add]
  rw [Function.update_of_ne hne]
  exact hsure

/-- A positive terminal gap at a profile with one zero-debt sure-deadline
owner yields a distinct paid observer.  Its first disagreement occurs by the
deadline, and its opponent reach satisfies the sharp `gap/(2M)` lower bound. -/
theorem HasTerminalExploitabilityGap.exists_deadline_paidFirstDisagreement
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    {gap M : ℝ} (hexploit : HasTerminalExploitabilityGap reward gap)
    (hgap : 0 < gap) (hM : 0 < M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (profile : (quittingGame reward).BehaviorProfile)
    (owner : ι) (deadline : ℕ)
    (hownerDebt : quittingTerminalDeviationDebt reward profile owner = 0)
    (hsure : quittingProfileLiveRoot reward profile deadline owner =
      PMF.pure true) :
    ∃ observer, observer ≠ owner ∧
      ∃ row : QuittingPaidFirstDisagreementRow reward profile observer gap,
        row.start ≤ deadline ∧ gap / (2 * M) ≤ row.liveMass := by
  obtain ⟨observer, deviation, hactual, source, receiving,
      _hsource, _hreceiving, hedge⟩ :=
    exists_supported_pair_with_gain reward hexploit profile
  have hobserverDebt : gap ≤
      quittingTerminalDeviationDebt reward profile observer := by
    have hcap := quittingTerminalPayoff_update_le_continuationBestResponseValue
      reward profile observer deviation
    unfold quittingTerminalDeviationDebt
    linarith
  have hne : observer ≠ owner := by
    intro heq
    subst observer
    rw [hownerDebt] at hobserverDebt
    linarith
  obtain ⟨row, _hrowSource, _hrowReceiving⟩ :=
    exists_quittingPaidFirstDisagreementRow_of_pureTimePayoff_sub
      reward profile observer source receiving gap hgap hedge
  have hlive0 : 0 ≤ row.liveMass := by
    rw [row.liveMass_eq]
    exact quittingOpponentSurvivalWeight_nonneg _ _ _ _
  have hquit : |quittingFixedOpponentsQuitValue reward
      (quittingProfileLiveRoot reward profile) observer row.start| ≤ M := by
    rw [← quittingRootQuitPayoff_eq_fixedOpponentsQuitValue
      reward (quittingProfileLiveRoot reward profile) observer
        (0 : Payoff ι) row.start]
    exact abs_quittingRootExpectedPayoff_le_bound reward (0 : Payoff ι)
      (Function.update (quittingProfileLiveRoot reward profile row.start)
        observer (PMF.pure true)) observer hreward (fun _ => by simpa using hM.le)
  have hlater : |quittingRootSequenceRelativePureTimeTerminalValue reward
      (quittingProfileLiveRoot reward profile) observer row.start row.later| ≤ M := by
    unfold quittingRootSequenceRelativePureTimeTerminalValue
      quittingRootSequencePureTimeTerminalValue
      quittingRootSequenceHazardTerminalValue
    exact abs_quittingRootSequenceTerminalValue_le reward
      (quittingRootSequenceUpdate (quittingProfileLiveRoot reward profile)
        observer (quittingPureTimeHazard
          (quittingAbsolutePureTime row.start row.later)))
      observer row.start hM.le hreward
  have hreached : row.reachedGain ≤ 2 * M := by
    rw [row.reachedGain_eq]
    split <;> rw [abs_le] at hquit hlater <;> linarith
  have hpaid : gap ≤ 2 * M * row.liveMass := by
    calc
      gap ≤ row.liveMass * row.reachedGain := row.gain_le_paid
      _ ≤ row.liveMass * (2 * M) :=
        mul_le_mul_of_nonneg_left hreached hlive0
      _ = 2 * M * row.liveMass := by ring
  have hstart : row.start ≤ deadline := by
    by_contra hnot
    have hzero := quittingOpponentSurvivalWeight_eq_zero_of_sureOpponent_before
      reward profile hne.symm hsure (Nat.lt_of_not_ge hnot)
    rw [row.liveMass_eq, hzero] at hpaid
    linarith
  refine ⟨observer, hne, row, hstart, ?_⟩
  exact (div_le_iff₀ (by positivity : 0 < 2 * M)).2 (by simpa [mul_comm] using hpaid)

end GameTheory
