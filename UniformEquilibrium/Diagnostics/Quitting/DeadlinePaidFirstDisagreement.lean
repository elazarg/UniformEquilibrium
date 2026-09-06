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

/-- A positive terminal gap jointly selects a prescribed-support source and
a bounded cap-attaining recipient for a distinct paid observer.  Their first
disagreement occurs by the sure-owner deadline and has the sharp reach floor. -/
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
      ∃ source receiving : Option ℕ,
        source ∈ (quittingBehaviorStoppingLaw reward
          (profile observer)).support ∧
        (receiving = none ∨
          ∃ time ≤ deadline, receiving = some time) ∧
        quittingPureTimeDeviationPayoff reward profile observer receiving =
          quittingContinuationBestResponseValue reward profile observer ∧
        gap ≤ quittingTerminalDeviationDebt reward profile observer ∧
        gap ≤ quittingPureTimeDeviationPayoff reward profile observer receiving -
          quittingTerminalPayoff reward profile observer ∧
        gap ≤ quittingPureTimeDeviationPayoff reward profile observer receiving -
          quittingPureTimeDeviationPayoff reward profile observer source ∧
        ∃ row : QuittingPaidFirstDisagreementRow reward profile observer gap,
          row.sourceWitness = source ∧ row.receivingWitness = receiving ∧
            row.start ≤ deadline ∧ gap / (2 * M) ≤ row.liveMass := by
  obtain ⟨observer, deviation, hactual⟩ := hexploit profile
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
  obtain ⟨receiving, hreceivingBound, hreceivingCap⟩ :=
    exists_pureTime_le_deadline_or_never_terminalPayoff_eq_cap
      reward profile deadline hne.symm hsure
  let value : Option ℕ → ℝ :=
    quittingPureTimeDeviationPayoff reward profile observer
  have hvalue : ∀ quitTime, |value quitTime| ≤ quittingRewardBound reward := by
    intro quitTime
    exact abs_quittingTerminalPayoff_le reward _ observer
      (abs_reward_le_quittingRewardBound reward)
  have hprescribed : quittingTerminalPayoff reward profile observer =
      Math.Probability.expect
        (quittingBehaviorStoppingLaw reward (profile observer)) value := by
    have h := quittingTerminalPayoff_update_eq_expect_stoppingLaw_pureTime
      reward profile observer (profile observer)
    rw [Function.update_eq_self] at h
    exact h
  obtain ⟨source, hsource, hsourceValue⟩ :=
    exists_mem_support_le_expect
      (quittingBehaviorStoppingLaw reward (profile observer)) value hvalue
  have hreceivingValue : value receiving =
      quittingContinuationBestResponseValue reward profile observer := by
    exact hreceivingCap
  have hreceivingGain : gap ≤ value receiving -
      quittingTerminalPayoff reward profile observer := by
    rw [hreceivingValue]
    exact hobserverDebt
  have hedge : gap ≤ value receiving - value source := by
    have hdeviationCap :=
      quittingTerminalPayoff_update_le_continuationBestResponseValue
        reward profile observer deviation
    rw [hreceivingValue]
    linarith
  obtain ⟨row, hrowSource, hrowReceiving⟩ :=
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
  refine ⟨observer, hne, source, receiving, hsource, hreceivingBound,
    hreceivingValue, hobserverDebt, hreceivingGain, hedge, row,
    hrowSource, hrowReceiving, hstart, ?_⟩
  exact (div_le_iff₀ (by positivity : 0 < 2 * M)).2
    (by simpa [mul_comm] using hpaid)

end GameTheory
