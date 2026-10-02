import MathUE.PMFProduct.ArbitraryEvents
import MathUE.Probability.StoppingLawConditioning
import UniformEquilibrium.Quitting.Examples.AdaptiveChildCenter
import UniformEquilibrium.Quitting.Paths.StoppingLawOperationalDistance
import UniformEquilibrium.Quitting.Terminal.TerminalExploitability

/-! # Actual anchor membership and unbounded first quantiles at the center -/

noncomputable section

namespace GameTheory.AdaptiveChildCenter

open _root_.Math.Probability _root_.Math.ProbabilityMassFunction
open _root_.Math.Probability.DiscreteHazard.StoppingLaw Math.PMFProduct

/-- Center payoff of one actual deterministic clock tuple. -/
def clockPayoff (times : Fin 4 → Option ℕ) (who : Fin 4) : ℝ :=
  quittingTerminalOutcomeReward reward (quittingFirstStoppingOutcome times) who

theorem expectedPayoff_eq_expect_clocks (laws : Fin 4 → PMF (Option ℕ))
    (who : Fin 4) :
    quittingStoppingLawExpectedPayoff reward laws who =
      expect (pmfPi laws) (fun times => clockPayoff times who) := by
  rw [quittingStoppingLawExpectedPayoff, quittingIndependentTerminalOutcomeLaw, expect_map]
  rfl

theorem clockPayoff_abs_le_two (times : Fin 4 → Option ℕ) (who : Fin 4) :
    |clockPayoff times who| ≤ 2 := by
  unfold clockPayoff
  cases quittingFirstStoppingOutcome times with
  | none => norm_num [quittingTerminalOutcomeReward]
  | some terminal => exact reward_abs_le_two terminal who

/-- The anchor belongs to the first finite coalition, with ties included. -/
def anchorMembership (times : Fin 4 → Option ℕ) : Prop :=
  quittingStoppingTimeValue (times 3) = quittingEarliestStoppingValue times ∧
    quittingEarliestStoppingValue times ≠ ⊤

open Classical in
theorem clockPayoff_anchor (times : Fin 4 → Option ℕ) :
    clockPayoff times 3 = if anchorMembership times then 1 else 0 := by
  classical
  unfold clockPayoff quittingFirstStoppingOutcome
  by_cases htop : quittingEarliestStoppingValue times = ⊤
  · simp [htop, quittingTerminalOutcomeReward, anchorMembership]
  · simp [htop, quittingTerminalOutcomeReward, reward,
      quittingEarliestStoppingCoalition, anchorMembership]

theorem earliest_eq_zero_of_zero (times : Fin 4 → Option ℕ) (who : Fin 4)
    (hzero : times who = some 0) : quittingEarliestStoppingValue times = 0 := by
  apply le_antisymm
  · have hle := Finset.inf_le
      (f := fun player => quittingStoppingTimeValue (times player)) (Finset.mem_univ who)
    rw [hzero] at hle
    exact hle
  · exact bot_le

theorem anchorMembership_of_zero (times : Fin 4 → Option ℕ)
    (hzero : times 3 = some 0) : anchorMembership times := by
  rw [anchorMembership, earliest_eq_zero_of_zero times 3 hzero, hzero]
  simp [quittingStoppingTimeValue]

theorem clockPayoff_zero_of_quitNow (times : Fin 4 → Option ℕ)
    (hzero : times 0 = some 0) : clockPayoff times 0 = 1 := by
  have hmin := earliest_eq_zero_of_zero times 0 hzero
  simp [clockPayoff, quittingFirstStoppingOutcome, hmin,
    quittingTerminalOutcomeReward, reward, quittingEarliestStoppingCoalition,
    hzero, quittingStoppingTimeValue]

/-- Behavioral payoff is the membership probability under its actual
independent complete laws, including every late atom and Never. -/
theorem anchor_terminalPayoff_eq_membershipMass
    (parent : (quittingGame reward).BehaviorProfile) :
    quittingTerminalPayoff reward parent 3 =
      (pmfMass (pmfPi (quittingBehaviorStoppingLaws reward parent))
        anchorMembership).toReal := by
  rw [← quittingStoppingLawExpectedPayoff_behaviorStoppingLaws_eq_terminalPayoff,
    expectedPayoff_eq_expect_clocks]
  simp_rw [clockPayoff_anchor]
  exact expect_indicator_eq_pmfMass_toReal _ _

theorem anchor_terminalPayoff_le_one (parent : (quittingGame reward).BehaviorProfile) :
    quittingTerminalPayoff reward parent 3 ≤ 1 := by
  rw [anchor_terminalPayoff_eq_membershipMass]
  have hmass : pmfMass (pmfPi (quittingBehaviorStoppingLaws reward parent))
      anchorMembership ≤ 1 := by
    simpa only [pmfMass_true] using pmfMass_mono
      (pmfPi (quittingBehaviorStoppingLaws reward parent))
      (E := anchorMembership) (F := fun _ => True) (fun _ _ => trivial)
  simpa only [ENNReal.toReal_one] using
    ENNReal.toReal_mono ENNReal.one_ne_top hmass

theorem terminalPayoff_update_reconstructed_law
    (parent : (quittingGame reward).BehaviorProfile) (who observer : Fin 4)
    (replacement : PMF (Option ℕ)) :
    quittingTerminalPayoff reward (Function.update parent who
        (quittingStoppingLawBehaviorStrategy reward who replacement)) observer =
      quittingStoppingLawExpectedPayoff reward
        (Function.update (quittingBehaviorStoppingLaws reward parent) who replacement)
        observer := by
  rw [← quittingStoppingLawExpectedPayoff_behaviorStoppingLaws_eq_terminalPayoff,
    quittingBehaviorStoppingLaws_update,
    quittingBehaviorStoppingLaw_stoppingLawBehaviorStrategy]

theorem anchor_quitNow_payoff (parent : (quittingGame reward).BehaviorProfile) :
    quittingTerminalPayoff reward (Function.update parent 3
      (quittingStoppingLawBehaviorStrategy reward 3 (PMF.pure (some 0)))) 3 = 1 := by
  rw [terminalPayoff_update_reconstructed_law, expectedPayoff_eq_expect_clocks]
  calc
    expect (pmfPi (Function.update (quittingBehaviorStoppingLaws reward parent)
        3 (PMF.pure (some 0)))) (fun times => clockPayoff times 3) =
        expect (pmfPi (Function.update (quittingBehaviorStoppingLaws reward parent)
          3 (PMF.pure (some 0)))) (fun _ => (1 : ℝ)) := by
      apply expect_congr_on_support
      intro times htimes
      have hzero := eq_of_mem_support_pmfPi_update_pure
        (quittingBehaviorStoppingLaws reward parent) 3 (some 0) htimes
      simp [clockPayoff_anchor, anchorMembership_of_zero times hzero]
    _ = 1 := expect_const _ _

theorem zero_quitNow_payoff (parent : (quittingGame reward).BehaviorProfile) :
    quittingTerminalPayoff reward (Function.update parent 0
      (quittingStoppingLawBehaviorStrategy reward 0 (PMF.pure (some 0)))) 0 = 1 := by
  rw [terminalPayoff_update_reconstructed_law, expectedPayoff_eq_expect_clocks]
  calc
    expect (pmfPi (Function.update (quittingBehaviorStoppingLaws reward parent)
        0 (PMF.pure (some 0)))) (fun times => clockPayoff times 0) =
        expect (pmfPi (Function.update (quittingBehaviorStoppingLaws reward parent)
          0 (PMF.pure (some 0)))) (fun _ => (1 : ℝ)) := by
      apply expect_congr_on_support
      intro times htimes
      exact clockPayoff_zero_of_quitNow times
        (eq_of_mem_support_pmfPi_update_pure
          (quittingBehaviorStoppingLaws reward parent) 0 (some 0) htimes)
    _ = 1 := expect_const _ _

/-- The anchor's complete behavioral cap is exactly one for every parent. -/
theorem anchor_cap_eq_one (parent : (quittingGame reward).BehaviorProfile) :
    quittingContinuationBestResponseValue reward parent 3 = 1 := by
  apply le_antisymm
  · unfold quittingContinuationBestResponseValue
    apply csSup_le
    · exact ⟨_, parent 3, rfl⟩
    · rintro value ⟨deviation, rfl⟩
      exact anchor_terminalPayoff_le_one _
  · have hreply := quittingTerminalPayoff_update_le_continuationBestResponseValue
      reward parent 3 (quittingStoppingLawBehaviorStrategy reward 3 (PMF.pure (some 0)))
    rw [anchor_quitNow_payoff] at hreply
    exact hreply

theorem anchor_membership_error_le
    (parent : (quittingGame reward).BehaviorProfile) {error : ℝ}
    (herror : quittingTerminalExploitability reward parent ≤ error) :
    (pmfMass (pmfPi (quittingBehaviorStoppingLaws reward parent))
      (fun times => ¬anchorMembership times)).toReal ≤ error := by
  have hdebt := (quittingTerminalDeviationDebt_le_exploitability reward parent 3).trans herror
  rw [quittingTerminalDeviationDebt, anchor_cap_eq_one,
    anchor_terminalPayoff_eq_membershipMass] at hdebt
  rw [pmfMass_complement_toReal_eq_one_sub]
  exact hdebt

theorem not_anchorMembership_of_never (times : Fin 4 → Option ℕ)
    (hnever : times 3 = none) : ¬anchorMembership times := by
  rintro ⟨hfirst, hfinite⟩
  rw [hnever] at hfirst
  exact hfinite hfirst.symm

theorem anchor_never_le_error
    (parent : (quittingGame reward).BehaviorProfile) {error : ℝ}
    (herror : quittingTerminalExploitability reward parent ≤ error) :
    ((quittingBehaviorStoppingLaws reward parent 3) none).toReal ≤ error := by
  have hmono := pmfMass_mono (pmfPi (quittingBehaviorStoppingLaws reward parent))
    (E := fun times => times 3 = none) (F := fun times => ¬anchorMembership times)
    (fun times hnever => not_anchorMembership_of_never times hnever)
  have hreal := ENNReal.toReal_mono
    (pmfMass_ne_top _ (fun times => ¬anchorMembership times)) hmono
  rw [pmfMass_pmfPi_coord_arbitrary (quittingBehaviorStoppingLaws reward parent)
    3 (fun time => time = none), pmfMass_singleton] at hreal
  exact hreal.trans (anchor_membership_error_le parent herror)

theorem not_anchorMembership_of_before_survival
    (times : Fin 4 → Option ℕ) (active : Fin 3) (cutoff : ℕ)
    (hbefore : ¬survivesUntil cutoff (times active.castSucc))
    (hanchor : survivesUntil cutoff (times 3)) : ¬anchorMembership times := by
  have hstrict : quittingStoppingTimeValue (times active.castSucc) <
      quittingStoppingTimeValue (times 3) := by
    cases hactive : times active.castSucc with
    | none => simp [hactive, survivesUntil] at hbefore
    | some time =>
        have htime : time < cutoff := by simpa [hactive, survivesUntil] using hbefore
        cases hanchorTime : times 3 with
        | none => simp [quittingStoppingTimeValue]
        | some anchorTime =>
            have hcutoff : cutoff ≤ anchorTime := by
              simpa [hanchorTime, survivesUntil] using hanchor
            simpa [quittingStoppingTimeValue] using htime.trans_le hcutoff
  intro hmembership
  have hle := Finset.inf_le
    (f := fun who => quittingStoppingTimeValue (times who))
    (Finset.mem_univ active.castSucc)
  rw [hmembership.1] at hstrict
  exact (not_lt_of_ge hle) hstrict

/-- Independence gives the actual crossing-event bound for every active clock. -/
theorem before_survival_mul_le_error
    (parent : (quittingGame reward).BehaviorProfile) (active : Fin 3) (cutoff : ℕ)
    {error : ℝ} (herror : quittingTerminalExploitability reward parent ≤ error) :
    (1 - survival (quittingBehaviorStoppingLaws reward parent active.castSucc) cutoff) *
        survival (quittingBehaviorStoppingLaws reward parent 3) cutoff ≤ error := by
  let laws := quittingBehaviorStoppingLaws reward parent
  have hdifferent : active.castSucc ≠ (3 : Fin 4) := by
    intro heq
    have hvalue := congrArg Fin.val heq
    change active.val = 3 at hvalue
    omega
  have hmono := pmfMass_mono (pmfPi laws)
    (E := fun times => ¬survivesUntil cutoff (times active.castSucc) ∧
      survivesUntil cutoff (times 3)) (F := fun times => ¬anchorMembership times)
    (fun times htimes => not_anchorMembership_of_before_survival
      times active cutoff htimes.1 htimes.2)
  have hreal := ENNReal.toReal_mono
    (pmfMass_ne_top _ (fun times => ¬anchorMembership times)) hmono
  rw [pmfMass_pmfPi_pair_arbitrary laws active.castSucc 3 hdifferent
      (fun time => ¬survivesUntil cutoff time) (survivesUntil cutoff),
    ENNReal.toReal_mul, pmfMass_complement_toReal_eq_one_sub,
    pmfMass_survivesUntil_toReal, pmfMass_survivesUntil_toReal] at hreal
  exact hreal.trans (anchor_membership_error_le parent herror)

/-- The selected date is the existing first crossing of the actual anchor law.
All laws are complete and unbounded, and cutoff zero is permitted. -/
theorem exists_actual_quantile_source
    (parent : (quittingGame reward).BehaviorProfile) {error accuracy : ℝ}
    (herror : quittingTerminalExploitability reward parent ≤ error)
    (haccuracy : 0 < accuracy) (haccuracyOne : accuracy < 1)
    (hscale : error ≤ accuracy ^ 2) :
    ∃ cutoff,
      stoppingLawFirstCrossing? (quittingBehaviorStoppingLaws reward parent 3)
        (1 - accuracy) = some cutoff ∧
      accuracy < survival (quittingBehaviorStoppingLaws reward parent 3) cutoff ∧
      survival (quittingBehaviorStoppingLaws reward parent 3) (cutoff + 1) ≤ accuracy ∧
      ∀ active : Fin 3,
        (1 - survival (quittingBehaviorStoppingLaws reward parent active.castSucc) cutoff)
          ≤ error / accuracy ∧
        (1 - survival (quittingBehaviorStoppingLaws reward parent active.castSucc) cutoff)
          ≤ accuracy ∧
        1 - accuracy ≤
          survival (quittingBehaviorStoppingLaws reward parent active.castSucc) cutoff ∧
        0 < survival (quittingBehaviorStoppingLaws reward parent active.castSucc) cutoff := by
  have hnone : ((quittingBehaviorStoppingLaws reward parent 3) none).toReal < accuracy :=
    (anchor_never_le_error parent herror).trans_lt (by
      nlinarith [mul_pos haccuracy (sub_pos.mpr haccuracyOne)])
  obtain ⟨cutoff, hfirst, _, hsurvival, htail⟩ :=
    exists_stoppingLawFirstCrossing_bounds _ hnone haccuracyOne
  refine ⟨cutoff, hfirst, hsurvival, htail, ?_⟩
  intro active
  have hcross := before_survival_mul_le_error parent active cutoff herror
  have hsum := sum_finiteMass_range_eq_one_sub_survival
    (quittingBehaviorStoppingLaws reward parent active.castSucc) cutoff
  have hdiv := beforeMass_le_error_div_of_crossing_le
    (quittingBehaviorStoppingLaws reward parent active.castSucc)
    (quittingBehaviorStoppingLaws reward parent 3) cutoff
    haccuracy hsurvival (by simpa only [hsum] using hcross)
  have hsmall := beforeMass_le_threshold_of_crossing_le
    (quittingBehaviorStoppingLaws reward parent active.castSucc)
    (quittingBehaviorStoppingLaws reward parent 3) cutoff
    haccuracy hscale hsurvival (by simpa only [hsum] using hcross)
  rw [hsum] at hdiv hsmall
  exact ⟨hdiv, hsmall, by linarith, by linarith⟩

end GameTheory.AdaptiveChildCenter
