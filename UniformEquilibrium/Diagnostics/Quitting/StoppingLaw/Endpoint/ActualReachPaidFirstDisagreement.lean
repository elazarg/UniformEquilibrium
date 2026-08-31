import UniformEquilibrium.Quitting.Paths.StoppingLawBadMassSelection
import UniformEquilibrium.Quitting.Paths.BehaviorStoppingPayoff
import UniformEquilibrium.Quitting.Paths.SurvivalPrefixBridge
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticPaidFirstDisagreement

/-!
# Actual-reach paid first-disagreement rows

A positive continuation debt selects a source witness inside the observer's
actual stopping-law support.  The selected paid first-disagreement row retains
the observer, opponent, and joint survival-prefix floors.  This is a static
terminal-semantic localization, not a chronological source construction.
-/

noncomputable section

namespace GameTheory

open StochasticGame Math.Probability

/-- Selection of a bad source choice together with a survival floor valid at
every start date the selected source does not strictly precede, and with the
support of the selected source retained: a finite source carries strictly
positive stopping mass, and the never-stopping source carries strictly
positive never mass. -/
private theorem quittingStoppingLaw_positiveGap_sourceSupport
    (hazard : ℕ → PMF Bool) (value : Option ℕ → ℝ) (C M Δ : ℝ)
    (hval : ∀ choice, |value choice| ≤ M)
    (hC : ∀ choice, value choice ≤ C) (hCM : C ≤ M) (hΔ : 0 < Δ)
    (hgap : Δ ≤ C - expect (quittingHazardStoppingLaw hazard) value) :
    ∃ source : Option ℕ, Δ / 2 ≤ C - value source ∧
      (∀ start : ℕ, (∀ n, source = some n → start ≤ n) →
        Δ ≤ 4 * M * quittingHazardSurvival hazard start) ∧
      ((∃ n, source = some n ∧ 0 < quittingHazardStopMass hazard n) ∨
        (source = none ∧ 0 < quittingHazardNeverMass hazard)) := by
  have hM : 0 ≤ M := le_trans (abs_nonneg _) (hval none)
  have h4M : (0:ℝ) ≤ 4 * M := by linarith
  have hbad := quittingStoppingLaw_badMass_lowerBound hazard value C M Δ hval hC hCM hgap
  rcases quittingStoppingLaw_exists_leastBad_survival_lowerBound hazard
      (fun q => Δ / 2 ≤ C - value q) with ⟨hle, hzero⟩ | ⟨n, hPn, hposn, -, hsurv⟩
  · have hle' : expect (quittingHazardStoppingLaw hazard)
        (fun choice => if Δ / 2 ≤ C - value choice then (1:ℝ) else 0)
          ≤ quittingHazardNeverMass hazard := hle
    refine ⟨none, ?_, ?_, Or.inr ⟨rfl, ?_⟩⟩
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
    · have hchain : Δ ≤ 4 * M * quittingHazardNeverMass hazard := by
        linarith [mul_le_mul_of_nonneg_left hle' h4M]
      nlinarith [hchain, h4M, hΔ]
  · refine ⟨some n, hPn, ?_, Or.inl ⟨n, rfl, hposn⟩⟩
    intro start hstart
    have hmono := antitone_quittingHazardSurvival hazard (hstart n rfl)
    linarith [mul_le_mul_of_nonneg_left hsurv h4M,
      mul_le_mul_of_nonneg_left hmono h4M]

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- A positive continuation debt for the observer produces a paid
first-disagreement row at gain `Δ / 4` whose start date carries a
division-free floor on the observer's own live-spine survival and on the
opponents' reaching live mass, and whose recorded source witness is supported
by the observer's own stopping law. -/
theorem positiveDebt_exists_actualReach_paidRow_withSupport
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (observer : ι)
    (M Δ : ℝ)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hΔ : 0 < Δ)
    (hdebt : Δ ≤ quittingContinuationBestResponseValue reward profile observer -
        quittingTerminalPayoff reward profile observer) :
    ∃ row : QuittingPaidFirstDisagreementRow reward profile observer (Δ / 4),
      (Δ ≤ 4 * M *
          quittingHazardSurvival
            (quittingBehaviorLiveHazard reward (profile observer)) row.start) ∧
      (Δ ≤ 8 * M * row.liveMass) ∧
      ((∃ n, row.sourceWitness = some n ∧
          0 < quittingHazardStopMass
            (quittingBehaviorLiveHazard reward (profile observer)) n) ∨
        (row.sourceWitness = none ∧
          0 < quittingHazardNeverMass
            (quittingBehaviorLiveHazard reward (profile observer)))) := by
  have hM : 0 ≤ M :=
    (abs_nonneg (reward (quittingSingletonTerminal observer) observer)).trans
      (hreward (quittingSingletonTerminal observer) observer)
  have hval : ∀ q, |quittingPureTimeDeviationPayoff reward profile observer q|
      ≤ M := by
    intro q
    rw [quittingPureTimeDeviationPayoff]
    exact abs_quittingTerminalPayoff_le reward _ observer hreward
  have hCbound : ∀ q, quittingPureTimeDeviationPayoff reward profile observer q
      ≤ quittingContinuationBestResponseValue reward profile observer := by
    intro q
    rw [quittingPureTimeDeviationPayoff]
    exact quittingTerminalPayoff_update_le_continuationBestResponseValue
      reward profile observer _
  have hCM : quittingContinuationBestResponseValue reward profile observer
      ≤ M :=
    le_trans (le_abs_self _)
      (abs_quittingContinuationBestResponseValue_le reward profile observer
        hreward)
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
  obtain ⟨source, hsource, hfloor, hsupport⟩ := quittingStoppingLaw_positiveGap_sourceSupport
    (quittingBehaviorLiveHazard reward (profile observer))
    (quittingPureTimeDeviationPayoff reward profile observer)
    (quittingContinuationBestResponseValue reward profile observer)
    M Δ hval hCbound hCM hΔ hgap
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
  have hstartSrc : ∀ n, source = some n → row.start ≤ n := by
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
  refine ⟨row, hfloor row.start hstartSrc, ?_, ?_⟩
  · have hlive : 0 ≤ row.liveMass := by
      rw [row.liveMass_eq]
      exact quittingOpponentSurvivalWeight_nonneg _ _ _ _
    have hquit : |quittingFixedOpponentsQuitValue reward
        (quittingProfileLiveRoot reward profile) observer row.start| ≤ M := by
      rw [← quittingRootQuitPayoff_eq_fixedOpponentsQuitValue
        reward (quittingProfileLiveRoot reward profile) observer
          (0 : Payoff ι) row.start]
      exact abs_quittingRootExpectedPayoff_le_bound reward (0 : Payoff ι)
        (Function.update (quittingProfileLiveRoot reward profile row.start)
          observer (PMF.pure true)) observer hreward
        (fun _ => by simpa using hM)
    have hlater : |quittingRootSequenceRelativePureTimeTerminalValue reward
        (quittingProfileLiveRoot reward profile) observer row.start row.later| ≤ M := by
      unfold quittingRootSequenceRelativePureTimeTerminalValue
        quittingRootSequencePureTimeTerminalValue
        quittingRootSequenceHazardTerminalValue
      exact abs_quittingRootSequenceTerminalValue_le reward
        (quittingRootSequenceUpdate (quittingProfileLiveRoot reward profile)
          observer
          (quittingPureTimeHazard
            (quittingAbsolutePureTime row.start row.later)))
        observer row.start hM hreward
    have hreached : row.reachedGain ≤ 2 * M := by
      rw [row.reachedGain_eq]
      split <;> rw [abs_le] at hquit hlater <;> linarith
    have hpaid := row.gain_le_paid
    nlinarith [mul_le_mul_of_nonneg_left hreached hlive]
  · rcases hsupport with ⟨n, hn, hpos⟩ | ⟨hnone, hpos⟩
    · exact Or.inl ⟨n, hrow.trans hn, hpos⟩
    · exact Or.inr ⟨hrow.trans hnone, hpos⟩

/-- The same construction bounds the joint survival prefix at the row's start
date from below by the product of the two one-sided floors, while still
exporting the support of the recorded source witness. -/
theorem positiveDebt_exists_actualJointReach_paidRow_withSupport
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (observer : ι)
    (M Δ : ℝ)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hΔ : 0 < Δ)
    (hdebt : Δ ≤ quittingContinuationBestResponseValue reward profile observer -
        quittingTerminalPayoff reward profile observer) :
    ∃ row : QuittingPaidFirstDisagreementRow reward profile observer (Δ / 4),
      (Δ * Δ ≤ 32 * M * M *
        quittingSurvivalPrefix (quittingProfileLiveRoot reward profile) row.start) ∧
      ((∃ n, row.sourceWitness = some n ∧
          0 < quittingHazardStopMass
            (quittingBehaviorLiveHazard reward (profile observer)) n) ∨
        (row.sourceWitness = none ∧
          0 < quittingHazardNeverMass
            (quittingBehaviorLiveHazard reward (profile observer)))) := by
  obtain ⟨row, hown, hlive, hsupport⟩ :=
    positiveDebt_exists_actualReach_paidRow_withSupport reward profile observer
      M Δ hreward hΔ hdebt
  refine ⟨row, ?_, hsupport⟩
  have hprefix : quittingSurvivalPrefix (quittingProfileLiveRoot reward profile) row.start =
      row.liveMass * quittingHazardSurvival
        (quittingBehaviorLiveHazard reward (profile observer)) row.start := by
    rw [quittingSurvivalPrefix_eq_opponentSurvivalWeight_mul_own
        (quittingProfileLiveRoot reward profile) observer row.start,
      row.liveMass_eq, quittingHazardSurvival_eq_prod]
    rfl
  have hkey : Δ * Δ ≤ (8 * M * row.liveMass) *
      (4 * M * quittingHazardSurvival
        (quittingBehaviorLiveHazard reward (profile observer)) row.start) :=
    mul_le_mul hlive hown hΔ.le (by linarith)
  rw [hprefix]
  nlinarith [hkey]

/-- The support clause in the actual stopping-law vocabulary, together with
all three explicit-coordinate reach inequalities. -/
theorem positiveDebt_exists_actualJointReach_paidRow_mem_support
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (observer : ι)
    (M Δ : ℝ)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hΔ : 0 < Δ)
    (hdebt : Δ ≤ quittingContinuationBestResponseValue reward profile observer -
        quittingTerminalPayoff reward profile observer) :
    ∃ row : QuittingPaidFirstDisagreementRow reward profile observer (Δ / 4),
      row.sourceWitness ∈
          (quittingBehaviorStoppingLaw reward (profile observer)).support ∧
      Δ ≤ 4 * M * quittingHazardSurvival
        (quittingBehaviorLiveHazard reward (profile observer)) row.start ∧
      Δ ≤ 8 * M * row.liveMass ∧
      Δ * Δ ≤ 32 * M * M *
        quittingSurvivalPrefix (quittingProfileLiveRoot reward profile) row.start := by
  obtain ⟨row, hown, hlive, hsource⟩ :=
    positiveDebt_exists_actualReach_paidRow_withSupport reward profile observer
      M Δ hreward hΔ hdebt
  refine ⟨row, ?_, hown, hlive, ?_⟩
  · rw [PMF.mem_support_iff]
    rcases hsource with ⟨n, hrow, hpos⟩ | ⟨hrow, hpos⟩
    · rw [hrow]
      exact (ENNReal.toReal_ne_zero.mp (by
        simpa only [quittingBehaviorStoppingLaw_some_toReal] using
          ne_of_gt hpos)).1
    · rw [hrow]
      exact (ENNReal.toReal_ne_zero.mp (by
        simpa only [quittingBehaviorStoppingLaw_none_toReal] using
          ne_of_gt hpos)).1
  · have hprefix : quittingSurvivalPrefix
        (quittingProfileLiveRoot reward profile) row.start =
        row.liveMass * quittingHazardSurvival
          (quittingBehaviorLiveHazard reward (profile observer)) row.start := by
      rw [quittingSurvivalPrefix_eq_opponentSurvivalWeight_mul_own
          (quittingProfileLiveRoot reward profile) observer row.start,
        row.liveMass_eq, quittingHazardSurvival_eq_prod]
      rfl
    have hkey : Δ * Δ ≤ (8 * M * row.liveMass) *
        (4 * M * quittingHazardSurvival
          (quittingBehaviorLiveHazard reward (profile observer)) row.start) :=
      mul_le_mul hlive hown hΔ.le (by linarith)
    rw [hprefix]
    nlinarith [hkey]

end GameTheory
