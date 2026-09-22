import UniformEquilibrium.Quitting.Classification.QuietExtension.DeadlineWithdrawalSecurityMixedPointwise

/-!
# Security-enhanced raw deadline rows

The Never and future rows are unchanged. The join row uses the nonpositive
security floor selected from the literal reward table, with no supplied plan.
-/

noncomputable section

namespace GameTheory

open scoped BigOperators

variable {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]

/-- Literal N/F/J rows with the improved all-evaluation singleton floor. -/
structure DeadlineSecurityRewardCertificate
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
        reward ⟨cappedClockChildCoalition A,
          cappedClockChildCoalition_nonempty hA⟩ none ≤
      ∑ i, advanceWeight i *
        (reward ⟨{some i}, Finset.singleton_nonempty (some i)⟩ (some i) -
          reward ⟨cappedClockChildCoalition A,
            cappedClockChildCoalition_nonempty hA⟩ (some i))
  join_row : ∀ A (hA : A.Nonempty),
    reward ⟨cappedClockJoinedCoalition A,
          cappedClockJoinedCoalition_nonempty A⟩ none -
        reward ⟨cappedClockChildCoalition A,
          cappedClockChildCoalition_nonempty hA⟩ none ≤
      ∑ i, (advanceWeight i *
          (reward ⟨cappedClockChildCoalition (insert i A),
              cappedClockChildCoalition_nonempty (Finset.insert_nonempty i A)⟩ (some i) -
            reward ⟨cappedClockChildCoalition A,
              cappedClockChildCoalition_nonempty hA⟩ (some i)) +
        withdrawalWeight i * deadlineSecurityGainFloor reward i A hA)

/-- The pointwise coefficient in the deadline comparison is the larger of
the two weights, because advance and atom withdrawal occur on disjoint
private-clock events. -/
def DeadlineSecurityRewardCertificate.debtWeight
    {reward : {A : Finset (Option ι) // A.Nonempty} → Option ι → ℝ}
    (certificate : DeadlineSecurityRewardCertificate reward) (i : ι) : ℝ :=
  max (certificate.advanceWeight i) (certificate.withdrawalWeight i)

omit [Nonempty ι] in
theorem DeadlineSecurityRewardCertificate.debtWeight_nonneg
    {reward : {A : Finset (Option ι) // A.Nonempty} → Option ι → ℝ}
    (certificate : DeadlineSecurityRewardCertificate reward) (i : ι) :
    0 ≤ certificate.debtWeight i :=
  le_trans (certificate.advanceWeight_nonneg i) (le_max_left _ _)


end GameTheory
