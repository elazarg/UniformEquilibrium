/-
Actual-reach lower bounds from a positive quitting continuation debt.

A positive gap between the observer's continuation best-response value and the
prescribed terminal payoff forces a paid first-disagreement row whose start
date is genuinely reached: the observer's own live-spine survival through that
date and the opponents' live mass at that date each carry a division-free
lower bound, and their product bounds the joint survival prefix.
-/
import FableStoppingSelection
import UniformEquilibrium.Quitting.Paths.BehaviorStoppingPayoff
import UniformEquilibrium.Quitting.Paths.SurvivalPrefixBridge
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticPaidFirstDisagreement

noncomputable section

namespace GameTheory

open StochasticGame _root_.Math.Probability

/-- Selection of a bad source choice together with a survival floor that is
valid at every start date the selected source does not strictly precede. -/
private theorem quittingStoppingLaw_positiveGap_source
    (hazard : ℕ → PMF Bool) (value : Option ℕ → ℝ) (C M Δ : ℝ)
    (hval : ∀ choice, |value choice| ≤ M)
    (hC : ∀ choice, value choice ≤ C) (hCM : C ≤ M) (hΔ : 0 < Δ)
    (hgap : Δ ≤ C - expect (quittingHazardStoppingLaw hazard) value) :
    ∃ source : Option ℕ, Δ / 2 ≤ C - value source ∧
      ∀ start : ℕ, (∀ n, source = some n → start ≤ n) →
        Δ ≤ 4 * M * quittingHazardSurvival hazard start := by
  have hM : 0 ≤ M := le_trans (abs_nonneg _) (hval none)
  have h4M : (0:ℝ) ≤ 4 * M := by linarith
  have hbad := quittingStoppingLaw_badMass_lowerBound hazard value C M Δ hval hC hCM hgap
  rcases quittingStoppingLaw_exists_leastBad_survival_lowerBound hazard
      (fun q => Δ / 2 ≤ C - value q) with ⟨-, hzero⟩ | ⟨n, hPn, -, -, hsurv⟩
  · refine ⟨none, ?_, ?_⟩
    · by_contra hnone
      have habs : ∀ q, |(if Δ / 2 ≤ C - value q then (1:ℝ) else 0)| ≤ 1 := by
        intro q
        split <;> norm_num
      have hexp := quittingHazardStoppingLaw_expect hazard
        (fun q => if Δ / 2 ≤ C - value q then (1:ℝ) else 0) habs
      have hterm : ∀ t : ℕ, quittingHazardStopMass hazard t *
          (if Δ / 2 ≤ C - value (some t) then (1:ℝ) else 0) = 0 := by
        intro t
        by_cases ht : Δ / 2 ≤ C - value (some t)
        · rw [hzero t ht]; ring
        · rw [if_neg ht]; ring
      rw [if_neg hnone, tsum_congr hterm, tsum_zero] at hexp
      rw [hexp] at hbad
      simp only [mul_zero, add_zero] at hbad
      linarith
    · intro start _
      have hle := quittingStoppingLaw_badMass_le_survival_of_noFiniteBad hazard
        (fun q => Δ / 2 ≤ C - value q) hzero start
      linarith [mul_le_mul_of_nonneg_left hle h4M]
  · refine ⟨some n, hPn, ?_⟩
    intro start hstart
    have hmono := antitone_quittingHazardSurvival hazard (hstart n rfl)
    linarith [mul_le_mul_of_nonneg_left hsurv h4M,
      mul_le_mul_of_nonneg_left hmono h4M]

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- A positive continuation debt for the observer produces a paid
first-disagreement row at gain `Δ / 4` whose start date carries a
division-free floor on the observer's own live-spine survival and on the
opponents' reaching live mass. -/
theorem positiveDebt_exists_actualReach_paidFirstDisagreementRow
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (observer : ι)
    (Δ : ℝ) (hΔ : 0 < Δ)
    (hdebt : Δ ≤ quittingContinuationBestResponseValue reward profile observer -
        quittingTerminalPayoff reward profile observer) :
    ∃ row : QuittingPaidFirstDisagreementRow reward profile observer (Δ / 4),
      Δ ≤ 4 * quittingRewardBound reward *
          quittingHazardSurvival
            (quittingBehaviorLiveHazard reward (profile observer)) row.start ∧
      Δ ≤ 8 * quittingRewardBound reward * row.liveMass := by
  have hval : ∀ q, |quittingPureTimeDeviationPayoff reward profile observer q|
      ≤ quittingRewardBound reward := by
    intro q
    rw [quittingPureTimeDeviationPayoff]
    exact abs_quittingTerminalPayoff_le_quittingRewardBound reward _ observer
  have hCbound : ∀ q, quittingPureTimeDeviationPayoff reward profile observer q
      ≤ quittingContinuationBestResponseValue reward profile observer := by
    intro q
    rw [quittingPureTimeDeviationPayoff]
    exact quittingTerminalPayoff_update_le_continuationBestResponseValue
      reward profile observer _
  have hCM : quittingContinuationBestResponseValue reward profile observer
      ≤ quittingRewardBound reward :=
    le_trans (le_abs_self _)
      (abs_quittingContinuationBestResponseValue_le reward profile observer
        (abs_reward_le_quittingRewardBound reward))
  have hU : quittingTerminalPayoff reward profile observer =
      expect (quittingHazardStoppingLaw
          (quittingBehaviorLiveHazard reward (profile observer)))
        (quittingPureTimeDeviationPayoff reward profile observer) := by
    have h := quittingTerminalPayoff_update_eq_expect_stoppingLaw_pureTime
      reward profile observer (profile observer)
    rw [Function.update_eq_self] at h
    exact h
  have hgap : Δ ≤ quittingContinuationBestResponseValue reward profile observer -
      expect (quittingHazardStoppingLaw
          (quittingBehaviorLiveHazard reward (profile observer)))
        (quittingPureTimeDeviationPayoff reward profile observer) := by
    rw [← hU]
    exact hdebt
  obtain ⟨source, hsource, hfloor⟩ := quittingStoppingLaw_positiveGap_source
    (quittingBehaviorLiveHazard reward (profile observer))
    (quittingPureTimeDeviationPayoff reward profile observer)
    (quittingContinuationBestResponseValue reward profile observer)
    (quittingRewardBound reward) Δ hval hCbound hCM hΔ hgap
  have hsup := quittingContinuationBestResponseValue_eq_sSup_pureTimeDeviationPayoff
    reward profile observer
  have hne : (Set.range (quittingPureTimeDeviationPayoff reward profile observer)).Nonempty :=
    ⟨_, Set.mem_range_self none⟩
  have hlt : quittingContinuationBestResponseValue reward profile observer - Δ / 4 <
      sSup (Set.range (quittingPureTimeDeviationPayoff reward profile observer)) := by
    rw [← hsup]
    linarith
  obtain ⟨x, ⟨recv, rfl⟩, hx⟩ := exists_lt_of_lt_csSup hne hlt
  have hedge : Δ / 4 ≤ quittingPureTimeDeviationPayoff reward profile observer recv -
      quittingPureTimeDeviationPayoff reward profile observer source := by linarith
  obtain ⟨row, hrow, -⟩ := exists_quittingPaidFirstDisagreementRow_of_pureTimePayoff_sub
    reward profile observer source recv (Δ / 4) (by linarith) hedge
  refine ⟨row, ?_, ?_⟩
  · refine hfloor row.start ?_
    intro n hn
    have hsw : row.sourceWitness = some n := hrow.trans hn
    have hchr := row.chronology
    by_cases hre : row.receivingEarlier = true
    · rw [if_pos hre] at hchr
      have h2 := hchr.2
      rw [hsw] at h2
      cases hlater : row.later with
      | none =>
          rw [hlater] at h2
          simp [quittingAbsolutePureTime] at h2
      | some d =>
          rw [hlater] at h2
          simp [quittingAbsolutePureTime] at h2
          omega
    · rw [if_neg hre] at hchr
      have h1 := hchr.1
      rw [hsw] at h1
      simp only [Option.some.injEq] at h1
      omega
  · have hgain := row.gain_le_liveMass
    linarith

/-- The same construction bounds the joint survival prefix at the row's start
date from below by the product of the two one-sided floors. -/
theorem positiveDebt_exists_actualJointReach_paidFirstDisagreementRow
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (observer : ι)
    (Δ : ℝ) (hΔ : 0 < Δ)
    (hdebt : Δ ≤ quittingContinuationBestResponseValue reward profile observer -
        quittingTerminalPayoff reward profile observer) :
    ∃ row : QuittingPaidFirstDisagreementRow reward profile observer (Δ / 4),
      Δ * Δ ≤ 32 * quittingRewardBound reward * quittingRewardBound reward *
        quittingSurvivalPrefix (quittingProfileLiveRoot reward profile) row.start := by
  obtain ⟨row, hown, hlive⟩ :=
    positiveDebt_exists_actualReach_paidFirstDisagreementRow reward profile observer
      Δ hΔ hdebt
  refine ⟨row, ?_⟩
  have hprefix : quittingSurvivalPrefix (quittingProfileLiveRoot reward profile) row.start =
      row.liveMass * quittingHazardSurvival
        (quittingBehaviorLiveHazard reward (profile observer)) row.start := by
    rw [quittingSurvivalPrefix_eq_opponentSurvivalWeight_mul_own
        (quittingProfileLiveRoot reward profile) observer row.start,
      row.liveMass_eq, quittingHazardSurvival_eq_prod]
    rfl
  have hkey : Δ * Δ ≤ (8 * quittingRewardBound reward * row.liveMass) *
      (4 * quittingRewardBound reward * quittingHazardSurvival
        (quittingBehaviorLiveHazard reward (profile observer)) row.start) :=
    mul_le_mul hlive hown hΔ.le (by linarith)
  rw [hprefix]
  nlinarith [hkey]

end GameTheory
