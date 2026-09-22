import MathUE.PMFProduct.Basic
import UniformEquilibrium.Quitting.Paths.StoppingLawOperationalDistance
import UniformEquilibrium.Quitting.RewardBound

/-!
# Evaluated payoffs of complete stopping laws

Complete independent stopping laws retain both the first quitting coalition and
its clock.  This module defines their payoff under an arbitrary clock
evaluation, transports that semantics to actual behavior profiles, and shows
that arbitrary behavioral replacements and arbitrary complete-law replacements
have the same payoff envelope.

For a general evaluation, behavioral payoff is defined here through complete
live-spine stopping laws.  Its identification with finite-horizon stage payoff
is a separate bridge.  The bounded expectation and envelope results below use
the stated nonnegative antitone hypotheses; the underlying `tsum` and `sSup`
definitions remain total without adding those hypotheses to their signatures.
-/

noncomputable section

namespace GameTheory

open _root_.Math _root_.Math.Probability Math.PMFProduct

variable {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]

/-- Terminal payoff of one deterministic clock tuple. -/
def quittingPureClockTerminalPayoff
    (reward : {A : Finset ι // A.Nonempty} → ι → ℝ)
    (times : ι → Option ℕ) (who : ι) : ℝ :=
  match quittingFirstStoppingOutcome times with
  | none => 0
  | some A => reward A who

/-- Evaluated payoff of one deterministic clock tuple.  Never has value zero,
independently of the supplied evaluation's value at `⊤`. -/
def quittingPureClockEvaluatedPayoff
    (reward : {A : Finset ι // A.Nonempty} → ι → ℝ)
    (evaluation : WithTop ℕ → ℝ)
    (times : ι → Option ℕ) (who : ι) : ℝ :=
  match quittingFirstStoppingOutcome times with
  | none => 0
  | some A => evaluation (quittingEarliestStoppingValue times) * reward A who

/-- Expected evaluated payoff of independent complete stopping laws. -/
def quittingStoppingLawEvaluatedPayoff
    (reward : {A : Finset ι // A.Nonempty} → ι → ℝ)
    (evaluation : WithTop ℕ → ℝ)
    (laws : ι → PMF (Option ℕ)) (who : ι) : ℝ :=
  expect (pmfPi laws) fun times =>
    quittingPureClockEvaluatedPayoff reward evaluation times who

/-- Evaluated payoff of an actual behavior profile, through its exact tuple of
complete live-spine stopping laws. -/
def quittingBehaviorEvaluatedPayoff
    (reward : {A : Finset ι // A.Nonempty} → ι → ℝ)
    (evaluation : WithTop ℕ → ℝ)
    (profile : (quittingGame reward).BehaviorProfile) (who : ι) : ℝ :=
  quittingStoppingLawEvaluatedPayoff reward evaluation
    (quittingBehaviorStoppingLaws reward profile) who

/-- Replacement-law payoff envelope for one evaluated coordinate. -/
def quittingStoppingLawEvaluatedReplacementPayoffCap
    (reward : {A : Finset ι // A.Nonempty} → ι → ℝ)
    (evaluation : WithTop ℕ → ℝ)
    (laws : ι → PMF (Option ℕ)) (who : ι) : ℝ :=
  sSup (Set.range fun replacement : PMF (Option ℕ) =>
    quittingStoppingLawEvaluatedPayoff reward evaluation
      (Function.update laws who replacement) who)

/-- Full behavioral replacement payoff envelope for one evaluated coordinate. -/
def quittingBehaviorEvaluatedDeviationPayoffCap
    (reward : {A : Finset ι // A.Nonempty} → ι → ℝ)
    (evaluation : WithTop ℕ → ℝ)
    (profile : (quittingGame reward).BehaviorProfile) (who : ι) : ℝ :=
  sSup (Set.range fun deviation : (quittingGame reward).BehaviorStrategy who =>
    quittingBehaviorEvaluatedPayoff reward evaluation
      (Function.update profile who deviation) who)

omit [DecidableEq ι] in
/-- A nonnegative antitone evaluation bounds every deterministic evaluated
payoff by its value at time zero times the reward-table bound. -/
theorem abs_quittingPureClockEvaluatedPayoff_le
    (reward : {A : Finset ι // A.Nonempty} → ι → ℝ)
    (evaluation : WithTop ℕ → ℝ)
    (evaluation_nonneg : ∀ clock, 0 ≤ evaluation clock)
    (evaluation_antitone : Antitone evaluation)
    (times : ι → Option ℕ) (who : ι) :
    |quittingPureClockEvaluatedPayoff reward evaluation times who| ≤
      evaluation 0 * quittingRewardBound reward := by
  unfold quittingPureClockEvaluatedPayoff
  cases quittingFirstStoppingOutcome times with
  | none =>
      simp only [abs_zero]
      exact mul_nonneg (evaluation_nonneg 0) (quittingRewardBound_nonneg reward)
  | some outcome =>
      rw [abs_mul, abs_of_nonneg (evaluation_nonneg _)]
      exact mul_le_mul
        (evaluation_antitone bot_le)
        (abs_reward_le_quittingRewardBound reward outcome who)
        (abs_nonneg _) (evaluation_nonneg _)

omit [DecidableEq ι] in
/-- The same uniform bound after integrating independent stopping laws. -/
theorem abs_quittingStoppingLawEvaluatedPayoff_le
    (reward : {A : Finset ι // A.Nonempty} → ι → ℝ)
    (evaluation : WithTop ℕ → ℝ)
    (evaluation_nonneg : ∀ clock, 0 ≤ evaluation clock)
    (evaluation_antitone : Antitone evaluation)
    (laws : ι → PMF (Option ℕ)) (who : ι) :
    |quittingStoppingLawEvaluatedPayoff reward evaluation laws who| ≤
      evaluation 0 * quittingRewardBound reward := by
  unfold quittingStoppingLawEvaluatedPayoff
  apply abs_expect_le_of_abs_le
  intro times
  exact abs_quittingPureClockEvaluatedPayoff_le reward evaluation
    evaluation_nonneg evaluation_antitone times who

/-- Actual behavioral replacement payoffs form a bounded-above set. -/
theorem bddAbove_range_quittingBehaviorEvaluatedPayoff_update
    (reward : {A : Finset ι // A.Nonempty} → ι → ℝ)
    (evaluation : WithTop ℕ → ℝ)
    (evaluation_nonneg : ∀ clock, 0 ≤ evaluation clock)
    (evaluation_antitone : Antitone evaluation)
    (profile : (quittingGame reward).BehaviorProfile) (who : ι) :
    BddAbove (Set.range fun deviation : (quittingGame reward).BehaviorStrategy who =>
      quittingBehaviorEvaluatedPayoff reward evaluation
        (Function.update profile who deviation) who) := by
  refine ⟨evaluation 0 * quittingRewardBound reward, ?_⟩
  rintro _ ⟨deviation, rfl⟩
  exact (le_abs_self _).trans
    (abs_quittingStoppingLawEvaluatedPayoff_le reward evaluation
      evaluation_nonneg evaluation_antitone _ who)

/-- Behavioral replacement overwrites exactly the corresponding complete
stopping-law coordinate. -/
theorem quittingBehaviorEvaluatedPayoff_update
    (reward : {A : Finset ι // A.Nonempty} → ι → ℝ)
    (evaluation : WithTop ℕ → ℝ)
    (profile : (quittingGame reward).BehaviorProfile) (who observer : ι)
    (deviation : (quittingGame reward).BehaviorStrategy who) :
    quittingBehaviorEvaluatedPayoff reward evaluation
        (Function.update profile who deviation) observer =
      quittingStoppingLawEvaluatedPayoff reward evaluation
        (Function.update (quittingBehaviorStoppingLaws reward profile) who
          (quittingBehaviorStoppingLaw reward deviation)) observer := by
  rw [quittingBehaviorEvaluatedPayoff,
    quittingBehaviorStoppingLaws_update]

omit [DecidableEq ι] in
/-- Canonical conditional-hazard reconstruction preserves every evaluated
stopping-law payoff. -/
theorem quittingBehaviorEvaluatedPayoff_stoppingLawProfile
    (reward : {A : Finset ι // A.Nonempty} → ι → ℝ)
    (evaluation : WithTop ℕ → ℝ)
    (laws : ι → PMF (Option ℕ)) (who : ι) :
    quittingBehaviorEvaluatedPayoff reward evaluation
        (quittingStoppingLawProfile reward laws) who =
      quittingStoppingLawEvaluatedPayoff reward evaluation laws who := by
  rw [quittingBehaviorEvaluatedPayoff,
    quittingBehaviorStoppingLaws_stoppingLawProfile]

/-- Complete law replacement and unrestricted behavioral replacement have
exactly the same evaluated payoff envelope. -/
theorem quittingStoppingLawEvaluatedCap_behaviorStoppingLaws_eq_behaviorCap
    (reward : {A : Finset ι // A.Nonempty} → ι → ℝ)
    (evaluation : WithTop ℕ → ℝ)
    (profile : (quittingGame reward).BehaviorProfile) (who : ι) :
    quittingStoppingLawEvaluatedReplacementPayoffCap reward evaluation
        (quittingBehaviorStoppingLaws reward profile) who =
      quittingBehaviorEvaluatedDeviationPayoffCap reward evaluation profile who := by
  unfold quittingStoppingLawEvaluatedReplacementPayoffCap
    quittingBehaviorEvaluatedDeviationPayoffCap
  apply congrArg sSup
  ext value
  simp only [Set.mem_range]
  constructor
  · rintro ⟨replacement, rfl⟩
    let deviation :=
      quittingStoppingLawBehaviorStrategy reward who replacement
    refine ⟨deviation, ?_⟩
    rw [quittingBehaviorEvaluatedPayoff_update]
    simp [deviation]
  · rintro ⟨deviation, rfl⟩
    refine ⟨quittingBehaviorStoppingLaw reward deviation, ?_⟩
    rw [quittingBehaviorEvaluatedPayoff_update]

/-- Terminal evaluation is one at finite clocks and zero at Never. -/
def quittingTerminalEvaluation (clock : WithTop ℕ) : ℝ :=
  if clock = ⊤ then 0 else 1

@[simp] theorem quittingTerminalEvaluation_top :
    quittingTerminalEvaluation ⊤ = 0 := by
  simp [quittingTerminalEvaluation]

@[simp] theorem quittingTerminalEvaluation_coe (time : ℕ) :
    quittingTerminalEvaluation (time : WithTop ℕ) = 1 := by
  simp [quittingTerminalEvaluation]

@[simp] theorem quittingTerminalEvaluation_zero :
    quittingTerminalEvaluation 0 = 1 := by
  simp [quittingTerminalEvaluation]

theorem quittingTerminalEvaluation_nonneg (clock : WithTop ℕ) :
    0 ≤ quittingTerminalEvaluation clock := by
  unfold quittingTerminalEvaluation
  split_ifs <;> norm_num

theorem quittingTerminalEvaluation_antitone :
    Antitone quittingTerminalEvaluation := by
  intro first second hle
  by_cases hfirst : first = ⊤
  · have hsecond : second = ⊤ := top_unique (hfirst ▸ hle)
    simp [quittingTerminalEvaluation, hfirst, hsecond]
  · unfold quittingTerminalEvaluation
    split_ifs <;> norm_num

omit [DecidableEq ι] in
/-- Deterministic evaluated payoff at the terminal evaluation is the literal
deterministic terminal payoff. -/
theorem quittingPureClockEvaluatedPayoff_terminalEvaluation
    (reward : {A : Finset ι // A.Nonempty} → ι → ℝ)
    (times : ι → Option ℕ) (who : ι) :
    quittingPureClockEvaluatedPayoff reward quittingTerminalEvaluation
        times who =
      quittingPureClockTerminalPayoff reward times who := by
  unfold quittingPureClockEvaluatedPayoff quittingPureClockTerminalPayoff
  cases hOutcome : quittingFirstStoppingOutcome times with
  | none => rfl
  | some A =>
      have hfinite : quittingEarliestStoppingValue times ≠ ⊤ := by
        intro htop
        rw [quittingFirstStoppingOutcome, ite_eq_left htop] at hOutcome
        contradiction
      simp [quittingTerminalEvaluation, hfinite]

omit [DecidableEq ι] in
/-- The evaluated stopping-law semantics specializes literally to the existing
terminal stopping-law payoff. -/
theorem quittingStoppingLawEvaluatedPayoff_terminalEvaluation
    (reward : {A : Finset ι // A.Nonempty} → ι → ℝ)
    (laws : ι → PMF (Option ℕ)) (who : ι) :
    quittingStoppingLawEvaluatedPayoff reward quittingTerminalEvaluation
        laws who =
      quittingStoppingLawExpectedPayoff reward laws who := by
  rw [quittingStoppingLawEvaluatedPayoff,
    quittingStoppingLawExpectedPayoff,
    quittingIndependentTerminalOutcomeLaw, expect_map]
  apply congrArg (expect (pmfPi laws))
  funext times
  cases hOutcome : quittingFirstStoppingOutcome times with
  | none =>
      simp [quittingPureClockEvaluatedPayoff, hOutcome,
        quittingTerminalOutcomeReward]
  | some outcome =>
      have hfinite : quittingEarliestStoppingValue times ≠ ⊤ := by
        intro htop
        rw [quittingFirstStoppingOutcome, ite_eq_left htop] at hOutcome
        contradiction
      simp [quittingPureClockEvaluatedPayoff, hOutcome,
        quittingTerminalEvaluation, hfinite, quittingTerminalOutcomeReward]

/-- The new behavioral evaluation specializes to the established terminal
payoff, rather than defining a parallel terminal semantics. -/
theorem quittingBehaviorEvaluatedPayoff_terminalEvaluation
    (reward : {A : Finset ι // A.Nonempty} → ι → ℝ)
    (profile : (quittingGame reward).BehaviorProfile) (who : ι) :
    quittingBehaviorEvaluatedPayoff reward quittingTerminalEvaluation
        profile who =
      quittingTerminalPayoff reward profile who := by
  rw [quittingBehaviorEvaluatedPayoff,
    quittingStoppingLawEvaluatedPayoff_terminalEvaluation,
    quittingStoppingLawExpectedPayoff_behaviorStoppingLaws_eq_terminalPayoff]

/-- The evaluated full behavioral cap specializes to the existing terminal
behavioral deviation cap. -/
theorem quittingBehaviorEvaluatedDeviationPayoffCap_terminalEvaluation
    (reward : {A : Finset ι // A.Nonempty} → ι → ℝ)
    (profile : (quittingGame reward).BehaviorProfile) (who : ι) :
    quittingBehaviorEvaluatedDeviationPayoffCap reward
        quittingTerminalEvaluation profile who =
      quittingBehaviorDeviationPayoffCap reward profile who := by
  unfold quittingBehaviorEvaluatedDeviationPayoffCap
    quittingBehaviorDeviationPayoffCap
  simp_rw [quittingBehaviorEvaluatedPayoff_terminalEvaluation]

end GameTheory
