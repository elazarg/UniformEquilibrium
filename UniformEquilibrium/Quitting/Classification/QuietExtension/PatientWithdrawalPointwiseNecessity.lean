import UniformEquilibrium.Quitting.Classification.QuietExtension.PatientWithdrawalDomination
import UniformEquilibrium.Quitting.Classification.QuietExtension.PatientWithdrawalTerminalWitnesses

/-!
# Exact fixed-weight terminal patient-withdrawal criterion

The converse tests the universal deterministic comparison of advancement and
actual patient payoff limits. It reconstructs the literal P-N/F/J rows with
the same two weight arrays. This is necessity for the specified pointwise
limiting comparison, not for arbitrary behavioral-debt domination or quiet
extension. The existing full behavioral consumers use the sum coefficient.
-/

noncomputable section

namespace GameTheory

open scoped BigOperators

variable {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]

/-- Joint child Never recovers P-N, including the actual late-own-quit
alternative in the patient payoff limit. -/
theorem patientWithdrawal_neverRow_of_terminalPointwise
    (reward : {A : Finset (Option ι) // A.Nonempty} → Option ι → ℝ)
    (advanceWeight withdrawalWeight : ι → ℝ)
    (hdom : ∀ times deadline,
      cappedClockActualOutsideGain reward times deadline ≤
        ∑ i, (advanceWeight i * cappedClockActualChildGain reward times deadline i +
          withdrawalWeight i * patientWithdrawalTerminalGain reward times deadline i)) :
    reward ⟨{none}, Finset.singleton_nonempty none⟩ none ≤
      (∑ i, advanceWeight i *
        reward ⟨{some i}, Finset.singleton_nonempty (some i)⟩ (some i)) +
      ∑ i, withdrawalWeight i * patientWithdrawalOwnNeverAlternative reward i := by
  have h := hdom (fun _ => none) (some 0)
  have hgains := quietExtension_allNeverGains reward 0
  have hfirst : quittingEarliestStoppingValue (fun _ : ι => none) = ⊤ := by
    simp [quittingEarliestStoppingValue, quittingStoppingTimeValue]
  have hquiet := quittingFirstStoppingOutcome_quietParentClocks_of_first_eq_top
    (fun _ : ι => none) hfirst
  have hpatient (i : ι) :
      patientWithdrawalTerminalGain reward (fun _ => none) (some 0) i =
        patientWithdrawalOwnNeverAlternative reward i := by
    simp [patientWithdrawalTerminalGain, patientWithdrawalTerminalPayoffLimit,
      quittingStoppingTimeValue, quittingPureClockTerminalPayoff, hquiet]
  rw [hgains.1] at h
  simp_rw [hgains.2, hpatient] at h
  simpa only [Finset.sum_add_distrib] using h

/-- A first coalition at date one, with a floor-attaining hidden coalition
when it is a singleton, recovers the exact P-F row. -/
theorem patientWithdrawal_futureRow_of_terminalPointwise
    (reward : {A : Finset (Option ι) // A.Nonempty} → Option ι → ℝ)
    (advanceWeight withdrawalWeight : ι → ℝ)
    (hdom : ∀ times deadline,
      cappedClockActualOutsideGain reward times deadline ≤
        ∑ i, (advanceWeight i * cappedClockActualChildGain reward times deadline i +
          withdrawalWeight i * patientWithdrawalTerminalGain reward times deadline i))
    (A : Finset ι) (hA : A.Nonempty) :
    reward ⟨{none}, Finset.singleton_nonempty none⟩ none -
        reward ⟨cappedClockChildCoalition A, cappedClockChildCoalition_nonempty hA⟩ none ≤
      ∑ i, (advanceWeight i *
          (reward ⟨{some i}, Finset.singleton_nonempty (some i)⟩ (some i) -
            reward ⟨cappedClockChildCoalition A, cappedClockChildCoalition_nonempty hA⟩
              (some i)) +
        withdrawalWeight i * patientWithdrawalGainFloor reward i A hA) := by
  obtain ⟨times, hfirst, hcoalition, hpatient⟩ :=
    patientWithdrawal_exists_exactCoalitionWitness reward A hA 1
  have h := hdom times (some 0)
  rw [quietExtension_outsideGain_of_before reward times 0 1 A hA hfirst hcoalition
    (by omega)] at h
  simp_rw [quietExtension_childGain_of_before reward times 0 1 A hA hfirst hcoalition
    (by omega), hpatient 0 (by omega)] at h
  exact h

/-- A first coalition at date zero, with the same attained patient-floor
witness, recovers the exact P-J row. -/
theorem patientWithdrawal_joinRow_of_terminalPointwise
    (reward : {A : Finset (Option ι) // A.Nonempty} → Option ι → ℝ)
    (advanceWeight withdrawalWeight : ι → ℝ)
    (hdom : ∀ times deadline,
      cappedClockActualOutsideGain reward times deadline ≤
        ∑ i, (advanceWeight i * cappedClockActualChildGain reward times deadline i +
          withdrawalWeight i * patientWithdrawalTerminalGain reward times deadline i))
    (A : Finset ι) (hA : A.Nonempty) :
    reward ⟨cappedClockJoinedCoalition A, cappedClockJoinedCoalition_nonempty A⟩ none -
        reward ⟨cappedClockChildCoalition A, cappedClockChildCoalition_nonempty hA⟩ none ≤
      ∑ i, (advanceWeight i *
          (reward ⟨cappedClockChildCoalition (insert i A),
              cappedClockChildCoalition_nonempty (Finset.insert_nonempty i A)⟩ (some i) -
            reward ⟨cappedClockChildCoalition A, cappedClockChildCoalition_nonempty hA⟩
              (some i)) +
        withdrawalWeight i * patientWithdrawalGainFloor reward i A hA) := by
  obtain ⟨times, hfirst, hcoalition, hpatient⟩ :=
    patientWithdrawal_exists_exactCoalitionWitness reward A hA 0
  have h := hdom times (some 0)
  rw [quietExtension_outsideGain_of_tie reward times 0 A hA hfirst hcoalition] at h
  simp_rw [quietExtension_childGain_of_tie reward times 0 A hA hfirst hcoalition,
    hpatient 0 le_rfl] at h
  exact h

/-- Reconstruct the raw patient certificate from its universal terminal
limiting comparison, preserving both supplied nonnegative weight arrays. -/
def patientWithdrawalRewardCertificateOfTerminalPointwise
    (reward : {A : Finset (Option ι) // A.Nonempty} → Option ι → ℝ)
    (advanceWeight withdrawalWeight : ι → ℝ)
    (hadvance : ∀ i, 0 ≤ advanceWeight i)
    (hwithdrawal : ∀ i, 0 ≤ withdrawalWeight i)
    (hdom : ∀ times deadline,
      cappedClockActualOutsideGain reward times deadline ≤
        ∑ i, (advanceWeight i * cappedClockActualChildGain reward times deadline i +
          withdrawalWeight i * patientWithdrawalTerminalGain reward times deadline i)) :
    PatientWithdrawalRewardCertificate reward where
  advanceWeight := advanceWeight
  withdrawalWeight := withdrawalWeight
  advanceWeight_nonneg := hadvance
  withdrawalWeight_nonneg := hwithdrawal
  never_row := patientWithdrawal_neverRow_of_terminalPointwise
    reward advanceWeight withdrawalWeight hdom
  future_row := patientWithdrawal_futureRow_of_terminalPointwise
    reward advanceWeight withdrawalWeight hdom
  join_row := patientWithdrawal_joinRow_of_terminalPointwise
    reward advanceWeight withdrawalWeight hdom

/-- The literal P-N/F/J certificate is equivalent to the universal
deterministic terminal limiting comparison at fixed nonnegative weights.
The universal quantifier includes finite and Never outsider deadlines. -/
theorem patientWithdrawal_terminalPointwise_iff_certificate
    (reward : {A : Finset (Option ι) // A.Nonempty} → Option ι → ℝ)
    (advanceWeight withdrawalWeight : ι → ℝ)
    (hadvance : ∀ i, 0 ≤ advanceWeight i)
    (hwithdrawal : ∀ i, 0 ≤ withdrawalWeight i) :
    (∀ times deadline,
      cappedClockActualOutsideGain reward times deadline ≤
        ∑ i, (advanceWeight i * cappedClockActualChildGain reward times deadline i +
          withdrawalWeight i * patientWithdrawalTerminalGain reward times deadline i)) ↔
      ∃ certificate : PatientWithdrawalRewardCertificate reward,
        certificate.advanceWeight = advanceWeight ∧
          certificate.withdrawalWeight = withdrawalWeight := by
  constructor
  · intro hdom
    exact ⟨patientWithdrawalRewardCertificateOfTerminalPointwise reward
      advanceWeight withdrawalWeight hadvance hwithdrawal hdom, rfl, rfl⟩
  · rintro ⟨certificate, ha, hw⟩ times deadline
    have h := patientWithdrawalActualOutsideGain_le_weighted_childGains
      reward certificate times deadline
    simpa only [ha, hw] using h

end GameTheory
