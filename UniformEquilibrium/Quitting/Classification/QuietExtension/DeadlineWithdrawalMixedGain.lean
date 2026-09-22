import UniformEquilibrium.Quitting.Classification.QuietExtension.DeadlineWithdrawalExpectation
import UniformEquilibrium.Quitting.Classification.QuietExtension.DeadlineWithdrawalMixedMarginal

/-!
# Exact integrated gain of the private deadline mixture

The disjoint-event conditional identity is integrated only after the private
coin's full product marginal and the quiet baseline have been identified.
-/

noncomputable section

namespace GameTheory

open _root_.Math _root_.Math.Probability Math.PMFProduct

variable {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]

private theorem expect_sub_of_abs_bounds {Ω : Type*} (law : PMF Ω)
    (f g : Ω → ℝ) {C D : ℝ}
    (hf : ∀ sample, |f sample| ≤ C)
    (hg : ∀ sample, |g sample| ≤ D) :
    expect law (fun sample => f sample - g sample) =
      expect law f - expect law g := by
  change expect law (fun sample => f sample + -g sample) = _
  rw [expect_add_of_summable]
  · rw [expect_neg]
    ring
  · exact expect_summable_of_bounded law f hf
  · simpa [mul_neg] using (expect_summable_of_bounded law g hg).neg

/-- One legal private mixed response realizes the expectation of the
weighted advance and withdrawal gains, with coefficient `max(a,b)`. -/
theorem deadlineMixedPrivateReplacement_integratedGain
    (reward : {A : Finset (Option ι) // A.Nonempty} → Option ι → ℝ)
    (evaluation : WithTop ℕ → ℝ)
    (evaluation_nonneg : ∀ clock, 0 ≤ evaluation clock)
    (evaluation_antitone : Antitone evaluation)
    (childLaws : ι → PMF (Option ℕ)) (outsideLaw : PMF (Option ℕ))
    (i : ι) (advanceWeight withdrawalWeight : ℝ)
    (hadvance : 0 ≤ advanceWeight) (hwithdrawal : 0 ≤ withdrawalWeight) :
    max advanceWeight withdrawalWeight *
      (quittingStoppingLawEvaluatedPayoff reward evaluation
          (deadlineMixedChildParentStoppingLaws childLaws outsideLaw i
            advanceWeight withdrawalWeight hadvance hwithdrawal) (some i) -
        quittingStoppingLawEvaluatedPayoff reward evaluation
          (quietParentStoppingLaws childLaws) (some i)) =
      expect (cappedClockIndependentSample childLaws outsideLaw)
        (fun sample => advanceWeight *
            cappedClockActualEvaluatedChildGain reward evaluation
              sample.1 sample.2 i +
          withdrawalWeight *
            deadlineWithdrawalActualEvaluatedChildGain reward evaluation
              sample.1 sample.2 i) := by
  let law := cappedClockIndependentSample childLaws outsideLaw
  let coin (sample : (ι → Option ℕ) × Option ℕ) :=
    deadlineMixedPrivateClockLaw (sample.1 i) sample.2
      advanceWeight withdrawalWeight hadvance hwithdrawal
  let mixed (sample : (ι → Option ℕ) × Option ℕ) :=
    expect (coin sample) (fun newClock =>
      quittingPureClockEvaluatedPayoff reward evaluation
        (deadlinePrivateChildClocks sample.1 i newClock) (some i))
  let base (sample : (ι → Option ℕ) × Option ℕ) :=
    quittingPureClockEvaluatedPayoff reward evaluation
      (quietParentClocks sample.1) (some i)
  let bound := evaluation 0 * quittingRewardBound reward
  have hmixedBound (sample : (ι → Option ℕ) × Option ℕ) :
      |mixed sample| ≤ bound := by
    exact abs_expect_le_of_abs_le (coin sample) _ fun newClock =>
      abs_quittingPureClockEvaluatedPayoff_le reward evaluation
        evaluation_nonneg evaluation_antitone
        (deadlinePrivateChildClocks sample.1 i newClock) (some i)
  have hbaseBound (sample : (ι → Option ℕ) × Option ℕ) :
      |base sample| ≤ bound :=
    abs_quittingPureClockEvaluatedPayoff_le reward evaluation
      evaluation_nonneg evaluation_antitone
      (quietParentClocks sample.1) (some i)
  have hpoint : expect law (fun sample =>
      max advanceWeight withdrawalWeight * (mixed sample - base sample)) =
    expect law (fun sample => advanceWeight *
        cappedClockActualEvaluatedChildGain reward evaluation
          sample.1 sample.2 i +
      withdrawalWeight *
        deadlineWithdrawalActualEvaluatedChildGain reward evaluation
          sample.1 sample.2 i) := by
    apply congrArg (expect law)
    funext sample
    exact deadlineMixedPrivateClockLaw_evaluatedGain_identity
      reward evaluation sample.1 sample.2 i advanceWeight withdrawalWeight
      hadvance hwithdrawal
  have hlinear : expect law (fun sample =>
      max advanceWeight withdrawalWeight * (mixed sample - base sample)) =
    max advanceWeight withdrawalWeight *
      (expect law mixed - expect law base) := by
    rw [expect_const_mul, expect_sub_of_abs_bounds law mixed base
      hmixedBound hbaseBound]
  calc
    _ = max advanceWeight withdrawalWeight *
        (expect law mixed - expect law base) := by
      rw [expect_deadlineMixedPrivateClockLaw_payoff_eq_stoppingLaw
        reward evaluation evaluation_nonneg evaluation_antitone childLaws
        outsideLaw i advanceWeight withdrawalWeight hadvance hwithdrawal]
      rw [expect_cappedClockIndependentSample_quiet_eq_stoppingLaw
        reward evaluation childLaws outsideLaw (some i)]
    _ = expect law (fun sample =>
          max advanceWeight withdrawalWeight *
            (mixed sample - base sample)) := hlinear.symm
    _ = _ := hpoint

end GameTheory
