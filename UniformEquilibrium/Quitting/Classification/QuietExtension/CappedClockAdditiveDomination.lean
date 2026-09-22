import UniformEquilibrium.Quitting.Classification.QuietExtension.CappedClockExpectationDomination

/-!
# Capped-clock domination with uniformly approximate reward rows

If every Never, future, and joining row has the same nonnegative additive
allowance, the evaluated pointwise and expected comparisons pay that allowance
only once.  The correction is scaled by the evaluation's value at time zero.
The sharper Never-only slack interface remains separate.
-/

noncomputable section

namespace GameTheory

open _root_.Math _root_.Math.Probability Math.PMFProduct

variable {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]

/-- Capped-clock reward rows whose three families may each exceed their exact
bound by the same nonnegative allowance. -/
structure CappedClockParentRewardAdditiveCertificate
    (reward : {A : Finset (Option ι) // A.Nonempty} → Option ι → ℝ) where
  weight : ι → ℝ
  weight_nonneg : ∀ i, 0 ≤ weight i
  rowError : ℝ
  rowError_nonneg : 0 ≤ rowError
  never_row :
    reward ⟨{none}, Finset.singleton_nonempty none⟩ none ≤
      (∑ i, weight i *
        reward ⟨{some i}, Finset.singleton_nonempty (some i)⟩ (some i)) +
        rowError
  future_row : ∀ A (hA : A.Nonempty),
    reward ⟨{none}, Finset.singleton_nonempty none⟩ none -
        reward ⟨cappedClockChildCoalition A,
          cappedClockChildCoalition_nonempty hA⟩ none ≤
      (∑ i, weight i *
        (reward ⟨{some i}, Finset.singleton_nonempty (some i)⟩ (some i) -
          reward ⟨cappedClockChildCoalition A,
            cappedClockChildCoalition_nonempty hA⟩ (some i))) +
        rowError
  join_row : ∀ A (hA : A.Nonempty),
    reward ⟨cappedClockJoinedCoalition A,
          cappedClockJoinedCoalition_nonempty A⟩ none -
        reward ⟨cappedClockChildCoalition A,
          cappedClockChildCoalition_nonempty hA⟩ none ≤
      (∑ i, weight i *
        (reward ⟨cappedClockChildCoalition (insert i A),
            cappedClockChildCoalition_nonempty (Finset.insert_nonempty i A)⟩
              (some i) -
          reward ⟨cappedClockChildCoalition A,
            cappedClockChildCoalition_nonempty hA⟩ (some i))) +
        rowError

/-- A uniform row allowance as the common three-row error interface. -/
def CappedClockParentRewardAdditiveCertificate.toRowErrorCertificate
    {reward : {A : Finset (Option ι) // A.Nonempty} → Option ι → ℝ}
    (certificate : CappedClockParentRewardAdditiveCertificate reward) :
    CappedClockParentRewardRowErrorCertificate reward where
  weight := certificate.weight
  weight_nonneg := certificate.weight_nonneg
  neverError := certificate.rowError
  neverError_nonneg := certificate.rowError_nonneg
  futureError := certificate.rowError
  futureError_nonneg := certificate.rowError_nonneg
  joinError := certificate.rowError
  joinError_nonneg := certificate.rowError_nonneg
  never_row := certificate.never_row
  future_row := certificate.future_row
  join_row := certificate.join_row

omit [DecidableEq ι] [Nonempty ι] in
private theorem cappedClockEvaluatedRowErrorCharge_common_le
    (evaluation : WithTop ℕ → ℝ)
    (evaluation_nonneg : ∀ clock, 0 ≤ evaluation clock)
    (evaluation_antitone : Antitone evaluation)
    (times : ι → Option ℕ) (deadline : Option ℕ)
    (rowError : ℝ) (rowError_nonneg : 0 ≤ rowError) :
    cappedClockEvaluatedRowErrorCharge evaluation times deadline
        rowError rowError rowError ≤
      rowError * evaluation 0 := by
  cases deadline with
  | none =>
      simp only [cappedClockEvaluatedRowErrorCharge]
      exact mul_nonneg rowError_nonneg (evaluation_nonneg 0)
  | some deadline =>
      let first := quittingEarliestStoppingValue times
      have hzero (clock : WithTop ℕ) :
          evaluation clock * rowError ≤ rowError * evaluation 0 := by
        rw [mul_comm (evaluation clock) rowError]
        exact mul_le_mul_of_nonneg_left
          (evaluation_antitone bot_le) rowError_nonneg
      by_cases htop : first = ⊤
      · simpa [cappedClockEvaluatedRowErrorCharge, first, htop] using
          hzero (deadline : WithTop ℕ)
      · by_cases hbefore : (deadline : WithTop ℕ) < first
        · calc
            cappedClockEvaluatedRowErrorCharge evaluation times
                (some deadline) rowError rowError rowError =
              evaluation deadline * rowError := by
                simp only [cappedClockEvaluatedRowErrorCharge, first, htop,
                  hbefore, ↓reduceIte]
                ring
            _ ≤ rowError * evaluation 0 :=
              hzero (deadline : WithTop ℕ)
        · by_cases htie : first = (deadline : WithTop ℕ)
          · simpa [cappedClockEvaluatedRowErrorCharge, first, htop, hbefore,
              htie] using hzero first
          · simp [cappedClockEvaluatedRowErrorCharge, first, htop, hbefore,
              htie, mul_nonneg rowError_nonneg (evaluation_nonneg 0)]

/-- A common additive violation of all N/F/J rows contributes at most its
single time-zero-scaled allowance to deterministic evaluated domination. -/
theorem cappedClockActualEvaluatedOutsideGain_le_weighted_actualChildGain_add_error
    (reward : {A : Finset (Option ι) // A.Nonempty} → Option ι → ℝ)
    (certificate : CappedClockParentRewardAdditiveCertificate reward)
    (evaluation : WithTop ℕ → ℝ)
    (evaluation_nonneg : ∀ clock, 0 ≤ evaluation clock)
    (evaluation_antitone : Antitone evaluation)
    (times : ι → Option ℕ) (deadline : Option ℕ) :
    cappedClockActualEvaluatedOutsideGain reward evaluation times deadline ≤
      (∑ i, certificate.weight i *
        cappedClockActualEvaluatedChildGain reward evaluation times deadline i) +
      certificate.rowError * evaluation 0 := by
  have h :=
    cappedClockActualEvaluatedOutsideGain_le_weighted_actualChildGain_add_rowErrors
      reward certificate.toRowErrorCertificate evaluation evaluation_nonneg
        evaluation_antitone times deadline
  simp only [CappedClockParentRewardAdditiveCertificate.toRowErrorCertificate] at h
  exact h.trans (add_le_add le_rfl
    (cappedClockEvaluatedRowErrorCharge_common_le evaluation
      evaluation_nonneg evaluation_antitone times deadline certificate.rowError
        certificate.rowError_nonneg))

/-- Integrating the approximate N/F/J comparison preserves its one additive
allowance and exposes each child counterfactual as a separate expectation. -/
theorem
    expect_cappedClockActualEvaluatedOutsideGain_le_sum_childExpectations_add_error
    (reward : {A : Finset (Option ι) // A.Nonempty} → Option ι → ℝ)
    (certificate : CappedClockParentRewardAdditiveCertificate reward)
    (evaluation : WithTop ℕ → ℝ)
    (evaluation_nonneg : ∀ clock, 0 ≤ evaluation clock)
    (evaluation_antitone : Antitone evaluation)
    (law : PMF ((ι → Option ℕ) × Option ℕ)) :
    expect law (fun sample =>
        cappedClockActualEvaluatedOutsideGain reward evaluation
          sample.1 sample.2) ≤
      (∑ i, certificate.weight i *
        expect law (fun sample =>
          cappedClockActualEvaluatedChildGain reward evaluation
            sample.1 sample.2 i)) +
      certificate.rowError * evaluation 0 := by
  exact
    expect_cappedClockActualEvaluatedOutsideGain_le_sum_childExpectations_add_const
      reward certificate.weight certificate.weight_nonneg evaluation
        evaluation_nonneg evaluation_antitone law
        (certificate.rowError * evaluation 0) fun sample =>
          cappedClockActualEvaluatedOutsideGain_le_weighted_actualChildGain_add_error
            reward certificate evaluation evaluation_nonneg evaluation_antitone
              sample.1 sample.2

end GameTheory
