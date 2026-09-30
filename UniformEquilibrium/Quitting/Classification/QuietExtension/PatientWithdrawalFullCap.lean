import UniformEquilibrium.Quitting.Classification.QuietExtension.PatientWithdrawalExpectedLimit

/-!
# Patient payoff limits below the unrestricted behavioral cap

The common independent sample is mapped to the literal patient response.
Its marginal is exactly one private child-law replacement. Each finite-delay
payoff is bounded by the full behavioral cap before the payoff limit is taken.
-/

noncomputable section

namespace GameTheory

open Filter Topology _root_.Math.Probability Math.PMFProduct

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Actual patient child-law replacement, with the outsider prescribed Never. -/
def patientWithdrawalChildParentStoppingLaws
    (reward : {A : Finset (Option ι) // A.Nonempty} → Option ι → ℝ)
    (childLaws : ι → PMF (Option ℕ)) (outsideLaw : PMF (Option ℕ))
    (i : ι) (delay : ℕ) : Option ι → PMF (Option ℕ) :=
  Function.update (quietParentStoppingLaws childLaws) (some i)
    (patientWithdrawalPrivateReplacementLaw reward i delay (childLaws i) outsideLaw)

/-- The deterministic patient coupling has the independent parent marginal
of its actual private replacement law. -/
theorem patientWithdrawalPrivateReplacement_parentMarginal
    (reward : {A : Finset (Option ι) // A.Nonempty} → Option ι → ℝ)
    (childLaws : ι → PMF (Option ℕ)) (outsideLaw : PMF (Option ℕ))
    (i : ι) (delay : ℕ) :
    (cappedClockIndependentSample childLaws outsideLaw).map
        (fun sample => patientWithdrawalParentClocks reward sample.1 sample.2 delay i) =
      pmfPi (patientWithdrawalChildParentStoppingLaws reward childLaws outsideLaw i delay) := by
  let changeChild (sample : (ι → Option ℕ) × Option ℕ) :=
    Function.update sample.1 i
      (patientWithdrawalClock reward i delay (sample.1 i) sample.2)
  have hchild : (cappedClockIndependentSample childLaws outsideLaw).map changeChild =
      pmfPi (Function.update childLaws i
        (patientWithdrawalPrivateReplacementLaw reward i delay (childLaws i) outsideLaw)) := by
    unfold cappedClockIndependentSample
    rw [PMF.map_bind]
    simpa only [changeChild, PMF.map_comp, Function.comp_def] using
      patientWithdrawalPrivateReplacement_childProduct reward childLaws outsideLaw i delay
  have hclocks (sample : (ι → Option ℕ) × Option ℕ) :
      patientWithdrawalParentClocks reward sample.1 sample.2 delay i =
        quietParentClocks (changeChild sample) := by
    funext player
    cases player with
    | none => rfl
    | some j => by_cases hj : j = i <;>
        simp [patientWithdrawalParentClocks, deadlinePrivateChildClocks,
          quietParentClocks, changeChild, hj]
  calc
    _ = ((cappedClockIndependentSample childLaws outsideLaw).map changeChild).map
        quietParentClocks := by
      rw [PMF.map_comp]
      apply congrArg (fun f => (cappedClockIndependentSample childLaws outsideLaw).map f)
      funext sample
      exact hclocks sample
    _ = _ := by
      rw [hchild, map_pmfPi_child_quiet]
      congr 1
      funext player
      cases player with
      | none => rfl
      | some j => by_cases hj : j = i <;>
          simp [patientWithdrawalChildParentStoppingLaws, quietParentStoppingLaws, hj]

/-- The expected coupled patient payoff is the terminal payoff of its actual
independent one-child replacement, not of a correlated response profile. -/
theorem patientWithdrawal_expectedTerminalPayoff_eq_stoppingLawPayoff
    (reward : {A : Finset (Option ι) // A.Nonempty} → Option ι → ℝ)
    (childLaws : ι → PMF (Option ℕ)) (outsideLaw : PMF (Option ℕ))
    (i : ι) (delay : ℕ) :
    expect (cappedClockIndependentSample childLaws outsideLaw) (fun sample =>
        quittingPureClockTerminalPayoff reward
          (patientWithdrawalParentClocks reward sample.1 sample.2 delay i) (some i)) =
      quittingStoppingLawExpectedPayoff reward
        (patientWithdrawalChildParentStoppingLaws reward childLaws outsideLaw i delay)
        (some i) := by
  rw [← quittingStoppingLawEvaluatedPayoff_terminalEvaluation,
    quittingStoppingLawEvaluatedPayoff,
    ← patientWithdrawalPrivateReplacement_parentMarginal, expect_map]
  simp only [quittingPureClockEvaluatedPayoff_terminalEvaluation]

/-- Every finite-delay patient payoff is below the unrestricted behavioral
cap at the reconstructed quiet profile. -/
theorem patientWithdrawal_expectedTerminalPayoff_le_behaviorDeviationCap
    (reward : {A : Finset (Option ι) // A.Nonempty} → Option ι → ℝ)
    (childLaws : ι → PMF (Option ℕ)) (outsideLaw : PMF (Option ℕ))
    (i : ι) (delay : ℕ) :
    expect (cappedClockIndependentSample childLaws outsideLaw) (fun sample =>
        quittingPureClockTerminalPayoff reward
          (patientWithdrawalParentClocks reward sample.1 sample.2 delay i) (some i)) ≤
      quittingBehaviorDeviationPayoffCap reward
        (quittingStoppingLawProfile reward (quietParentStoppingLaws childLaws)) (some i) := by
  rw [patientWithdrawal_expectedTerminalPayoff_eq_stoppingLawPayoff,
    ← quittingStoppingLawEvaluatedPayoff_terminalEvaluation,
    ← quittingBehaviorEvaluatedDeviationPayoffCap_terminalEvaluation]
  let profile := quittingStoppingLawProfile reward (quietParentStoppingLaws childLaws)
  let deviation := quittingStoppingLawBehaviorStrategy reward (some i)
    (patientWithdrawalPrivateReplacementLaw reward i delay (childLaws i) outsideLaw)
  have hlegal : quittingBehaviorEvaluatedPayoff reward quittingTerminalEvaluation
      (Function.update profile (some i) deviation) (some i) =
      quittingStoppingLawEvaluatedPayoff reward quittingTerminalEvaluation
        (patientWithdrawalChildParentStoppingLaws reward childLaws outsideLaw i delay)
        (some i) := by
    rw [quittingBehaviorEvaluatedPayoff_update]
    simp [profile, deviation, patientWithdrawalChildParentStoppingLaws,
      quittingBehaviorStoppingLaws_stoppingLawProfile]
  rw [← hlegal]
  exact le_csSup
    (bddAbove_range_quittingBehaviorEvaluatedPayoff_update reward quittingTerminalEvaluation
      quittingTerminalEvaluation_nonneg quittingTerminalEvaluation_antitone profile (some i))
    ⟨deviation, rfl⟩

/-- The literal patient payoff-limit expectation is below the full behavioral
cap, by taking a limit only after every actual response has been bounded. -/
theorem patientWithdrawal_expectedTerminalPayoffLimit_le_behaviorDeviationCap
    (reward : {A : Finset (Option ι) // A.Nonempty} → Option ι → ℝ)
    (childLaws : ι → PMF (Option ℕ)) (outsideLaw : PMF (Option ℕ)) (i : ι) :
    expect (cappedClockIndependentSample childLaws outsideLaw) (fun sample =>
        patientWithdrawalTerminalPayoffLimit reward sample.1 sample.2 i) ≤
      quittingBehaviorDeviationPayoffCap reward
        (quittingStoppingLawProfile reward (quietParentStoppingLaws childLaws)) (some i) :=
  le_of_tendsto'
    (patientWithdrawal_expectedTerminalPayoff_tendsto reward
      (cappedClockIndependentSample childLaws outsideLaw) i)
    (patientWithdrawal_expectedTerminalPayoff_le_behaviorDeviationCap
      reward childLaws outsideLaw i)

end GameTheory
