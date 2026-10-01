import UniformEquilibrium.Quitting.Classification.QuietExtension.DeadlineWithdrawalPointwise
import UniformEquilibrium.Quitting.Classification.QuietExtension.DeadlineWithdrawalMixedMarginal
import UniformEquilibrium.Quitting.Classification.QuietExtension.DeterministicResponseWitnesses

/-! # Actual future cancellation and its evaluated raw rows

Cancellation keeps an earlier own clock and replaces every clock at or after a
finite outsider replica deadline by Never. A Never deadline is the identity.
The legal law and its product marginal below are literal private replacements.
The raw finite rows use the zero-based floor, never the patient Never alternative.

This module supplies the actual operation and response-cap bridge. It does not
yet prove that these rows bound every outsider's debt: that requires the
deterministic evaluated cancellation comparison and its bounded integration.
-/

noncomputable section

namespace GameTheory

open _root_.Math.Probability Math.PMFProduct
open scoped BigOperators

variable {ι : Type}

/-- Future cancellation is the identity at Never, including an own Never clock. -/
def cancellationStoppingClock (source deadline : Option ℕ) : Option ℕ :=
  match deadline with
  | none => source
  | some time =>
      if quittingStoppingTimeValue source < (time : WithTop ℕ) then source else none

theorem cancellationStoppingClock_none (source : Option ℕ) :
    cancellationStoppingClock source none = source := rfl

theorem cancellationStoppingClock_some_of_before
    (source : Option ℕ) (time : ℕ)
    (hbefore : quittingStoppingTimeValue source < (time : WithTop ℕ)) :
    cancellationStoppingClock source (some time) = source := by
  simp [cancellationStoppingClock, hbefore]

theorem cancellationStoppingClock_some_of_not_before
    (source : Option ℕ) (time : ℕ)
    (hbefore : ¬ quittingStoppingTimeValue source < (time : WithTop ℕ)) :
    cancellationStoppingClock source (some time) = none := by
  simp [cancellationStoppingClock, hbefore]

/-- The replacement sees only its original own clock and an independent replica deadline. -/
def cancellationPrivateReplacementLaw (sourceLaw outsideLaw : PMF (Option ℕ)) :
    PMF (Option ℕ) :=
  sourceLaw.bind fun source => outsideLaw.map (cancellationStoppingClock source)

variable [Fintype ι] [DecidableEq ι]

/-- One child is cancelled privately, with every other coordinate unchanged. -/
def cancellationParentClocks (times : ι → Option ℕ)
    (deadline : Option ℕ) (i : ι) : Option ι → Option ℕ :=
  deadlinePrivateChildClocks times i (cancellationStoppingClock (times i) deadline)

omit [Fintype ι] in
/-- At a Never replica deadline, the whole cancellation experiment is the identity. -/
theorem cancellationParentClocks_none (times : ι → Option ℕ) (i : ι) :
    cancellationParentClocks times none i = quietParentClocks times := by
  funext player
  cases player with
  | none => rfl
  | some j =>
      by_cases hj : j = i
      · subst j
        simp [cancellationParentClocks, deadlinePrivateChildClocks, quietParentClocks,
          cancellationStoppingClock_none]
      · simp [cancellationParentClocks, deadlinePrivateChildClocks, quietParentClocks, hj]

/-- When the deadline is no later than child absorption, cancellation is the
literal Never update. The shared witness identity handles its parent embedding. -/
theorem cancellationParentClocks_eq_quiet_update_none
    (times : ι → Option ℕ) (time : ℕ) (i : ι)
    (hdeadline : (time : WithTop ℕ) ≤ quittingEarliestStoppingValue times) :
    cancellationParentClocks times (some time) i =
      quietParentClocks (Function.update times i none) := by
  have hbefore : ¬ quittingStoppingTimeValue (times i) < (time : WithTop ℕ) := by
    apply not_lt.mpr
    exact hdeadline.trans (Finset.inf_le (Finset.mem_univ i))
  rw [cancellationParentClocks, cancellationStoppingClock_some_of_not_before _ _ hbefore]
  exact quietExtensionPrivateClocks_cancel times i

/-- The actual evaluated gain from cancelling one child's future clock. -/
def cancellationActualEvaluatedChildGain
    (reward : {A : Finset (Option ι) // A.Nonempty} → Option ι → ℝ)
    (evaluation : WithTop ℕ → ℝ)
    (times : ι → Option ℕ) (deadline : Option ℕ) (i : ι) : ℝ :=
  quittingPureClockEvaluatedPayoff reward evaluation
      (cancellationParentClocks times deadline i) (some i) -
    quittingPureClockEvaluatedPayoff reward evaluation (quietParentClocks times) (some i)

theorem cancellationActualEvaluatedChildGain_none
    (reward : {A : Finset (Option ι) // A.Nonempty} → Option ι → ℝ)
    (evaluation : WithTop ℕ → ℝ) (times : ι → Option ℕ) (i : ι) :
    cancellationActualEvaluatedChildGain reward evaluation times none i = 0 := by
  simp [cancellationActualEvaluatedChildGain, cancellationParentClocks_none]

/-- The cancellation coupling produces an independent product with exactly one new law. -/
theorem cancellationPrivateReplacement_childProduct
    (childLaws : ι → PMF (Option ℕ)) (outsideLaw : PMF (Option ℕ)) (i : ι) :
    (pmfPi childLaws).bind (fun times => outsideLaw.map fun deadline =>
      Function.update times i (cancellationStoppingClock (times i) deadline)) =
      pmfPi (Function.update childLaws i
        (cancellationPrivateReplacementLaw (childLaws i) outsideLaw)) := by
  have h := pmfPi_bind_privateClockKernel childLaws i
    (fun source => outsideLaw.map (cancellationStoppingClock source))
  simpa only [cancellationPrivateReplacementLaw, PMF.map_comp, Function.comp_def] using h

/-- Quiet parent laws with the single literal cancellation law installed. -/
def cancellationChildParentStoppingLaws
    (childLaws : ι → PMF (Option ℕ)) (outsideLaw : PMF (Option ℕ)) (i : ι) :
    Option ι → PMF (Option ℕ) :=
  Function.update (quietParentStoppingLaws childLaws) (some i)
    (cancellationPrivateReplacementLaw (childLaws i) outsideLaw)

/-- The shared coupling's parent marginal is the actual independent replacement,
not a correlated family of child responses. -/
theorem cancellationPrivateReplacement_parentMarginal
    (childLaws : ι → PMF (Option ℕ)) (outsideLaw : PMF (Option ℕ)) (i : ι) :
    (cappedClockIndependentSample childLaws outsideLaw).map
        (fun sample => cancellationParentClocks sample.1 sample.2 i) =
      pmfPi (cancellationChildParentStoppingLaws childLaws outsideLaw i) := by
  let changeChild (sample : (ι → Option ℕ) × Option ℕ) :=
    Function.update sample.1 i (cancellationStoppingClock (sample.1 i) sample.2)
  have hchild : (cappedClockIndependentSample childLaws outsideLaw).map changeChild =
      pmfPi (Function.update childLaws i
        (cancellationPrivateReplacementLaw (childLaws i) outsideLaw)) := by
    unfold cappedClockIndependentSample
    rw [PMF.map_bind]
    simpa only [changeChild, PMF.map_comp, Function.comp_def] using
      cancellationPrivateReplacement_childProduct childLaws outsideLaw i
  have hclocks (sample : (ι → Option ℕ) × Option ℕ) :
      cancellationParentClocks sample.1 sample.2 i = quietParentClocks (changeChild sample) := by
    funext player
    cases player with
    | none => rfl
    | some j => by_cases hj : j = i <;>
        simp [cancellationParentClocks, deadlinePrivateChildClocks,
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
          simp [cancellationChildParentStoppingLaws, quietParentStoppingLaws, hj]

/-- Evaluating the coupled cancellation gives the actual independent-law payoff. -/
theorem cancellation_expectedEvaluatedPayoff_eq_stoppingLawPayoff
    (reward : {A : Finset (Option ι) // A.Nonempty} → Option ι → ℝ)
    (evaluation : WithTop ℕ → ℝ)
    (childLaws : ι → PMF (Option ℕ)) (outsideLaw : PMF (Option ℕ)) (i : ι) :
    expect (cappedClockIndependentSample childLaws outsideLaw) (fun sample =>
        quittingPureClockEvaluatedPayoff reward evaluation
          (cancellationParentClocks sample.1 sample.2 i) (some i)) =
      quittingStoppingLawEvaluatedPayoff reward evaluation
        (cancellationChildParentStoppingLaws childLaws outsideLaw i) (some i) := by
  rw [quittingStoppingLawEvaluatedPayoff,
    ← cancellationPrivateReplacement_parentMarginal, expect_map]

/-- Every actual cancellation payoff is below the unrestricted behavioral cap.
The law is reconstructed as a complete behavioral replacement, including Never. -/
theorem cancellation_expectedEvaluatedPayoff_le_behaviorDeviationCap
    (reward : {A : Finset (Option ι) // A.Nonempty} → Option ι → ℝ)
    (evaluation : WithTop ℕ → ℝ)
    (evaluation_nonneg : ∀ clock, 0 ≤ evaluation clock)
    (evaluation_antitone : Antitone evaluation)
    (childLaws : ι → PMF (Option ℕ)) (outsideLaw : PMF (Option ℕ)) (i : ι) :
    expect (cappedClockIndependentSample childLaws outsideLaw) (fun sample =>
        quittingPureClockEvaluatedPayoff reward evaluation
          (cancellationParentClocks sample.1 sample.2 i) (some i)) ≤
      quittingBehaviorEvaluatedDeviationPayoffCap reward evaluation
        (quittingStoppingLawProfile reward (quietParentStoppingLaws childLaws)) (some i) := by
  rw [cancellation_expectedEvaluatedPayoff_eq_stoppingLawPayoff]
  let profile := quittingStoppingLawProfile reward (quietParentStoppingLaws childLaws)
  let deviation := quittingStoppingLawBehaviorStrategy reward (some i)
    (cancellationPrivateReplacementLaw (childLaws i) outsideLaw)
  have hlegal : quittingBehaviorEvaluatedPayoff reward evaluation
      (Function.update profile (some i) deviation) (some i) =
      quittingStoppingLawEvaluatedPayoff reward evaluation
        (cancellationChildParentStoppingLaws childLaws outsideLaw i) (some i) := by
    rw [quittingBehaviorEvaluatedPayoff_update]
    simp [profile, deviation, cancellationChildParentStoppingLaws,
      quittingBehaviorStoppingLaws_stoppingLawProfile]
  rw [← hlegal]
  exact le_csSup
    (bddAbove_range_quittingBehaviorEvaluatedPayoff_update reward evaluation
      evaluation_nonneg evaluation_antitone profile (some i)) ⟨deviation, rfl⟩

/-- The expected gain of the actual cancellation response is below full
evaluated behavioral debt at the unchanged quiet profile. -/
theorem cancellation_expectedEvaluatedGain_le_behaviorDeviationDebt
    (reward : {A : Finset (Option ι) // A.Nonempty} → Option ι → ℝ)
    (evaluation : WithTop ℕ → ℝ)
    (evaluation_nonneg : ∀ clock, 0 ≤ evaluation clock)
    (evaluation_antitone : Antitone evaluation)
    (childLaws : ι → PMF (Option ℕ)) (outsideLaw : PMF (Option ℕ)) (i : ι) :
    expect (cappedClockIndependentSample childLaws outsideLaw) (fun sample =>
        cancellationActualEvaluatedChildGain reward evaluation sample.1 sample.2 i) ≤
      quittingBehaviorEvaluatedDeviationPayoffCap reward evaluation
          (quittingStoppingLawProfile reward (quietParentStoppingLaws childLaws)) (some i) -
        quittingStoppingLawEvaluatedPayoff reward evaluation
          (quietParentStoppingLaws childLaws) (some i) := by
  let : Nonempty ι := ⟨i⟩
  let source := cappedClockIndependentSample childLaws outsideLaw
  let changed (sample : (ι → Option ℕ) × Option ℕ) :=
    quittingPureClockEvaluatedPayoff reward evaluation
      (cancellationParentClocks sample.1 sample.2 i) (some i)
  let baseline (sample : (ι → Option ℕ) × Option ℕ) :=
    quittingPureClockEvaluatedPayoff reward evaluation (quietParentClocks sample.1) (some i)
  have hlinear := expect_sub_of_abs_bounds source changed baseline
    (fun sample => abs_quittingPureClockEvaluatedPayoff_le reward evaluation
      evaluation_nonneg evaluation_antitone
      (cancellationParentClocks sample.1 sample.2 i) (some i))
    (fun sample => abs_quittingPureClockEvaluatedPayoff_le reward evaluation
      evaluation_nonneg evaluation_antitone (quietParentClocks sample.1) (some i))
  change expect source (fun sample => changed sample - baseline sample) ≤ _
  rw [hlinear]
  change expect (cappedClockIndependentSample childLaws outsideLaw) (fun sample =>
      quittingPureClockEvaluatedPayoff reward evaluation
        (cancellationParentClocks sample.1 sample.2 i) (some i)) -
    expect (cappedClockIndependentSample childLaws outsideLaw) (fun sample =>
      quittingPureClockEvaluatedPayoff reward evaluation (quietParentClocks sample.1) (some i))
      ≤ _
  rw [expect_cappedClockIndependentSample_quiet_eq_stoppingLaw]
  exact sub_le_sub_right
    (cancellation_expectedEvaluatedPayoff_le_behaviorDeviationCap reward evaluation
      evaluation_nonneg evaluation_antitone childLaws outsideLaw i) _

/-- Literal evaluated-cancellation N/F/J rows. These raw reward inequalities
use the passive zero floor and contain no strategy, cap, or equilibrium field. -/
structure CancellationWithdrawalRewardCertificate
    (reward : {A : Finset (Option ι) // A.Nonempty} → Option ι → ℝ) where
  advanceWeight : ι → ℝ
  withdrawalWeight : ι → ℝ
  advanceWeight_nonneg : ∀ i, 0 ≤ advanceWeight i
  withdrawalWeight_nonneg : ∀ i, 0 ≤ withdrawalWeight i
  never_row :
    reward ⟨{none}, Finset.singleton_nonempty none⟩ none ≤
      ∑ i, advanceWeight i *
        reward ⟨{some i}, Finset.singleton_nonempty (some i)⟩ (some i)
  future_row : ∀ A (hA : A.Nonempty),
    reward ⟨{none}, Finset.singleton_nonempty none⟩ none -
        reward ⟨cappedClockChildCoalition A, cappedClockChildCoalition_nonempty hA⟩ none ≤
      ∑ i, (advanceWeight i *
          (reward ⟨{some i}, Finset.singleton_nonempty (some i)⟩ (some i) -
            reward ⟨cappedClockChildCoalition A, cappedClockChildCoalition_nonempty hA⟩
              (some i)) +
        withdrawalWeight i * deadlineWithdrawalGainFloor reward i A hA)
  join_row : ∀ A (hA : A.Nonempty),
    reward ⟨cappedClockJoinedCoalition A, cappedClockJoinedCoalition_nonempty A⟩ none -
        reward ⟨cappedClockChildCoalition A, cappedClockChildCoalition_nonempty hA⟩ none ≤
      ∑ i, (advanceWeight i *
          (reward ⟨cappedClockChildCoalition (insert i A),
              cappedClockChildCoalition_nonempty (Finset.insert_nonempty i A)⟩ (some i) -
            reward ⟨cappedClockChildCoalition A, cappedClockChildCoalition_nonempty hA⟩
              (some i)) +
        withdrawalWeight i * deadlineWithdrawalGainFloor reward i A hA)

/-- Cancellation and advancement are separate experiments, so coefficients add. -/
def CancellationWithdrawalRewardCertificate.debtWeight
    {reward : {A : Finset (Option ι) // A.Nonempty} → Option ι → ℝ}
    (certificate : CancellationWithdrawalRewardCertificate reward) (i : ι) : ℝ :=
  certificate.advanceWeight i + certificate.withdrawalWeight i

theorem CancellationWithdrawalRewardCertificate.debtWeight_nonneg
    {reward : {A : Finset (Option ι) // A.Nonempty} → Option ι → ℝ}
    (certificate : CancellationWithdrawalRewardCertificate reward) (i : ι) :
    0 ≤ certificate.debtWeight i :=
  add_nonneg (certificate.advanceWeight_nonneg i) (certificate.withdrawalWeight_nonneg i)

/-- The printed future residual splits into the early-minus-late Never charge
and a late F-row charge. Existing deadline row algebra supplies that split. -/
theorem CancellationWithdrawalRewardCertificate.futureRows_evaluated
    {reward : {A : Finset (Option ι) // A.Nonempty} → Option ι → ℝ}
    (certificate : CancellationWithdrawalRewardCertificate reward)
    (A : Finset ι) (hA : A.Nonempty) (earlyWeight lateWeight : ℝ)
    (hlate : 0 ≤ lateWeight) (hantitone : lateWeight ≤ earlyWeight) :
    earlyWeight * reward ⟨{none}, Finset.singleton_nonempty none⟩ none -
        lateWeight *
          reward ⟨cappedClockChildCoalition A, cappedClockChildCoalition_nonempty hA⟩ none ≤
      ∑ i, (certificate.advanceWeight i *
          (earlyWeight * reward ⟨{some i}, Finset.singleton_nonempty (some i)⟩ (some i) -
            lateWeight *
              reward ⟨cappedClockChildCoalition A, cappedClockChildCoalition_nonempty hA⟩
                (some i)) +
        certificate.withdrawalWeight i * lateWeight * deadlineWithdrawalGainFloor reward i A hA)
        := by
  have hfuture := certificate.future_row A hA
  rw [Finset.sum_add_distrib] at hfuture
  have h := deadlineWithdrawal_futureRows_evaluated certificate.advanceWeight
    (fun i => reward ⟨{some i}, Finset.singleton_nonempty (some i)⟩ (some i))
    (fun i => reward ⟨cappedClockChildCoalition A, cappedClockChildCoalition_nonempty hA⟩
      (some i))
    (reward ⟨{none}, Finset.singleton_nonempty none⟩ none)
    (reward ⟨cappedClockChildCoalition A, cappedClockChildCoalition_nonempty hA⟩ none +
      ∑ i, certificate.withdrawalWeight i * deadlineWithdrawalGainFloor reward i A hA)
    earlyWeight lateWeight hlate hantitone certificate.never_row (by linarith)
  have heq : (∑ i, certificate.advanceWeight i *
      (earlyWeight * reward ⟨{some i}, Finset.singleton_nonempty (some i)⟩ (some i) -
        lateWeight *
          reward ⟨cappedClockChildCoalition A, cappedClockChildCoalition_nonempty hA⟩
            (some i))) +
      lateWeight * (∑ i, certificate.withdrawalWeight i *
        deadlineWithdrawalGainFloor reward i A hA) =
      ∑ i, (certificate.advanceWeight i *
          (earlyWeight * reward ⟨{some i}, Finset.singleton_nonempty (some i)⟩ (some i) -
            lateWeight *
              reward ⟨cappedClockChildCoalition A, cappedClockChildCoalition_nonempty hA⟩
                (some i)) +
        certificate.withdrawalWeight i * lateWeight * deadlineWithdrawalGainFloor reward i A hA)
        := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [← heq]
  linarith

end GameTheory
