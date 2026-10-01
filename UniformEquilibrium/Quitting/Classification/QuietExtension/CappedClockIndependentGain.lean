import UniformEquilibrium.Quitting.Classification.QuietExtension.DeadlineWithdrawalOutsideMarginal
import UniformEquilibrium.Quitting.Classification.QuietExtension.CappedClockEvaluatedActualPayoffAdapter

/-! # Actual evaluated gains of the independent child/outsider coupling

The source coupling has the prescribed product-law outsider marginal, quiet
baseline, and legal capped-child marginal. These gain adapters reuse the existing
marginal and full behavioral-cap identities, including complete Never replies.
-/

noncomputable section

namespace GameTheory

open _root_.Math.Probability

variable {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]

/-- The coupled outsider gain is the difference of actual independent-law payoffs. -/
theorem expect_cappedClockIndependentSample_outsideGain_eq_stoppingLawGain
    (reward : {A : Finset (Option ι) // A.Nonempty} → Option ι → ℝ)
    (evaluation : WithTop ℕ → ℝ)
    (evaluation_nonneg : ∀ clock, 0 ≤ evaluation clock)
    (evaluation_antitone : Antitone evaluation)
    (childLaws : ι → PMF (Option ℕ)) (outsideLaw : PMF (Option ℕ)) :
    expect (cappedClockIndependentSample childLaws outsideLaw) (fun sample =>
        cappedClockActualEvaluatedOutsideGain reward evaluation sample.1 sample.2) =
      quittingStoppingLawEvaluatedPayoff reward evaluation
          (cappedClockParentSourceLaws childLaws outsideLaw) none -
        quittingStoppingLawEvaluatedPayoff reward evaluation
          (quietParentStoppingLaws childLaws) none := by
  unfold cappedClockActualEvaluatedOutsideGain
  rw [expect_sub_of_abs_bounds
    (cappedClockIndependentSample childLaws outsideLaw) _ _
    (fun sample => abs_quittingPureClockEvaluatedPayoff_le reward evaluation
      evaluation_nonneg evaluation_antitone (outsideDeadlineClocks sample.1 sample.2) none)
    (fun sample => abs_quittingPureClockEvaluatedPayoff_le reward evaluation
      evaluation_nonneg evaluation_antitone (quietParentClocks sample.1) none),
    expect_cappedClockIndependentSample_outside_eq_stoppingLaw,
    expect_cappedClockIndependentSample_quiet_eq_stoppingLaw]

/-- Each advance experiment changes one independent law and is bounded by the
same unchanged quiet profile's unrestricted evaluated child debt. -/
theorem expect_cappedClockIndependentSample_childGain_le_behaviorDebt
    (reward : {A : Finset (Option ι) // A.Nonempty} → Option ι → ℝ)
    (evaluation : WithTop ℕ → ℝ)
    (evaluation_nonneg : ∀ clock, 0 ≤ evaluation clock)
    (evaluation_antitone : Antitone evaluation)
    (childLaws : ι → PMF (Option ℕ)) (outsideLaw : PMF (Option ℕ)) (i : ι) :
    expect (cappedClockIndependentSample childLaws outsideLaw) (fun sample =>
        cappedClockActualEvaluatedChildGain reward evaluation sample.1 sample.2 i) ≤
      quittingBehaviorEvaluatedDeviationPayoffCap reward evaluation
          (quittingStoppingLawProfile reward (quietParentStoppingLaws childLaws)) (some i) -
        quittingStoppingLawEvaluatedPayoff reward evaluation
          (quietParentStoppingLaws childLaws) (some i) := by
  have hchanged := expect_parentSource_cappedChild_eq_stoppingLawEvaluatedPayoff
    reward evaluation childLaws outsideLaw i
  rw [← map_cappedClockIndependentSample_outside childLaws outsideLaw, expect_map] at hchanged
  simp only [outsideDeadlineClocks] at hchanged
  unfold cappedClockActualEvaluatedChildGain
  rw [expect_sub_of_abs_bounds
    (cappedClockIndependentSample childLaws outsideLaw) _ _
    (fun sample => abs_quittingPureClockEvaluatedPayoff_le reward evaluation
      evaluation_nonneg evaluation_antitone
      (cappedChildParentClocks sample.1 sample.2 i) (some i))
    (fun sample => abs_quittingPureClockEvaluatedPayoff_le reward evaluation
      evaluation_nonneg evaluation_antitone (quietParentClocks sample.1) (some i)),
    expect_cappedClockIndependentSample_quiet_eq_stoppingLaw, hchanged]
  exact sub_le_sub_right
    (cappedChild_stoppingLawEvaluatedPayoff_le_behaviorDeviationCap reward evaluation
      evaluation_nonneg evaluation_antitone childLaws outsideLaw i) _

end GameTheory
