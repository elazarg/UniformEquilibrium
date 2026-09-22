import UniformEquilibrium.Quitting.Classification.QuietExtension.CappedClockExpectationDomination
import UniformEquilibrium.Quitting.Classification.QuietExtension.CappedClockPointwiseNecessity

/-!
# Expectation necessity of the capped-clock reward rows

Universal terminal expectation domination is equivalent to deterministic
domination because Dirac clock laws recover every deterministic sample.  The
existing deterministic characterization then recovers exactly the finite
Never, future, and joining reward rows.
-/

noncomputable section

namespace GameTheory

open _root_.Math _root_.Math.Probability Math.PMFProduct

variable {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]

/-- Universal terminal expectation domination is equivalent to universal
deterministic domination for the same fixed nonnegative weights. -/
theorem cappedClockExpectedActualGain_le_iff_actualGain_le
    (reward : {A : Finset (Option ι) // A.Nonempty} → Option ι → ℝ)
    (weight : ι → ℝ) (weight_nonneg : ∀ who, 0 ≤ weight who) :
    (∀ law : PMF ((ι → Option ℕ) × Option ℕ),
      expect law (fun sample =>
          cappedClockActualOutsideGain reward sample.1 sample.2) ≤
        expect law (fun sample =>
          ∑ who, weight who *
            cappedClockActualChildGain reward sample.1 sample.2 who)) ↔
      ∀ times deadline,
        cappedClockActualOutsideGain reward times deadline ≤
          ∑ who, weight who *
            cappedClockActualChildGain reward times deadline who := by
  constructor
  · intro hdom times deadline
    simpa only [expect_pure] using hdom (PMF.pure (times, deadline))
  · intro hdom law
    let certificate := cappedClockParentRewardCertificateOfActualGainLe
      reward weight weight_nonneg hdom
    have h := expect_cappedClockActualEvaluatedOutsideGain_le_weighted_childGain
      reward certificate cappedClockTerminalEvaluation
        cappedClockTerminalEvaluation_nonneg
        cappedClockTerminalEvaluation_antitone law
    change expect law (fun sample =>
        cappedClockActualEvaluatedOutsideGain reward
          cappedClockTerminalEvaluation sample.1 sample.2) ≤
      expect law (fun sample =>
        ∑ who, weight who *
          cappedClockActualEvaluatedChildGain reward
            cappedClockTerminalEvaluation sample.1 sample.2 who) at h
    simpa only [cappedClockActualEvaluatedOutsideGain,
      cappedClockActualEvaluatedChildGain,
      cappedClockActualOutsideGain, cappedClockActualChildGain,
      quittingPureClockEvaluatedPayoff_terminalEvaluation] using h

/-- Exact N/F/J reward rows are equivalent to universal terminal expectation
domination over arbitrary coupled child/deadline clock laws. -/
theorem cappedClockExpectedActualGain_le_iff_rewardRows
    (reward : {A : Finset (Option ι) // A.Nonempty} → Option ι → ℝ)
    (weight : ι → ℝ) (weight_nonneg : ∀ who, 0 ≤ weight who) :
    (∀ law : PMF ((ι → Option ℕ) × Option ℕ),
      expect law (fun sample =>
          cappedClockActualOutsideGain reward sample.1 sample.2) ≤
        expect law (fun sample =>
          ∑ who, weight who *
            cappedClockActualChildGain reward sample.1 sample.2 who)) ↔
      (reward ⟨{none}, Finset.singleton_nonempty none⟩ none ≤
        ∑ who, weight who *
          reward ⟨{some who}, Finset.singleton_nonempty (some who)⟩
            (some who)) ∧
      (∀ coalition (hne : coalition.Nonempty),
        reward ⟨{none}, Finset.singleton_nonempty none⟩ none -
            reward ⟨cappedClockChildCoalition coalition,
              cappedClockChildCoalition_nonempty hne⟩ none ≤
          ∑ who, weight who *
            (reward ⟨{some who}, Finset.singleton_nonempty (some who)⟩
                (some who) -
              reward ⟨cappedClockChildCoalition coalition,
                cappedClockChildCoalition_nonempty hne⟩ (some who))) ∧
      ∀ coalition (hne : coalition.Nonempty),
        reward ⟨cappedClockJoinedCoalition coalition,
              cappedClockJoinedCoalition_nonempty coalition⟩ none -
            reward ⟨cappedClockChildCoalition coalition,
              cappedClockChildCoalition_nonempty hne⟩ none ≤
          ∑ who, weight who *
            (reward ⟨cappedClockChildCoalition (insert who coalition),
                cappedClockChildCoalition_nonempty
                  (Finset.insert_nonempty who coalition)⟩ (some who) -
              reward ⟨cappedClockChildCoalition coalition,
                cappedClockChildCoalition_nonempty hne⟩ (some who)) := by
  exact (cappedClockExpectedActualGain_le_iff_actualGain_le
    reward weight weight_nonneg).trans
      (cappedClockActualGain_le_iff_rewardRows
        reward weight weight_nonneg)

end GameTheory
