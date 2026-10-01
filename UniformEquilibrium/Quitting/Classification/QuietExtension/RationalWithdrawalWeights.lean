import MathUE.LinearProgramming.RationalFeasibility
import UniformEquilibrium.Quitting.Classification.QuietExtension.PatientWithdrawalRaw
import UniformEquilibrium.Quitting.Classification.QuietExtension.RationalWithdrawalSecurityLP
import UniformEquilibrium.Quitting.Classification.QuietExtension.DeadlineWithdrawalSecurityMixedRaw
import UniformEquilibrium.Quitting.Classification.QuietExtension.DeadlineWithdrawalSecurityTerminalDebt
import UniformEquilibrium.Quitting.Classification.QuietExtension.CappedClockPositiveSingletonQuietExtension

/-!
# Exact rational response weights

The literal Never/future/join reward-row systems have rational nonnegative weights whenever
they have real feasible weights and the reward table is rational. Zero weights and equality
endpoints are retained. These are raw-row feasibility adapters, not strategy selection or
a quantitative search guarantee.
-/

noncomputable section

namespace GameTheory

open scoped BigOperators

private abbrev WithdrawalResponseRow (ι : Type) :=
  Option (Bool × {coalition : Finset ι // coalition.Nonempty})

variable {ι : Type} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] in
private def withdrawalAdvanceCoefficient
    (reward : {A : Finset (Option ι) // A.Nonempty} → Option ι → ℝ) :
    WithdrawalResponseRow ι → ι → ℝ
  | none, i => reward ⟨{some i}, Finset.singleton_nonempty (some i)⟩ (some i)
  | some (false, coalition), i =>
      reward ⟨{some i}, Finset.singleton_nonempty (some i)⟩ (some i) -
        reward ⟨cappedClockChildCoalition coalition.1,
          cappedClockChildCoalition_nonempty coalition.2⟩ (some i)
  | some (true, coalition), i =>
      reward ⟨cappedClockChildCoalition (insert i coalition.1),
          cappedClockChildCoalition_nonempty (Finset.insert_nonempty i coalition.1)⟩
          (some i) -
        reward ⟨cappedClockChildCoalition coalition.1,
          cappedClockChildCoalition_nonempty coalition.2⟩ (some i)

omit [Fintype ι] in
private def withdrawalOutsideCoefficient
    (reward : {A : Finset (Option ι) // A.Nonempty} → Option ι → ℝ) :
    WithdrawalResponseRow ι → ℝ
  | none => reward ⟨{none}, Finset.singleton_nonempty none⟩ none
  | some (false, coalition) =>
      reward ⟨{none}, Finset.singleton_nonempty none⟩ none -
        reward ⟨cappedClockChildCoalition coalition.1,
          cappedClockChildCoalition_nonempty coalition.2⟩ none
  | some (true, coalition) =>
      reward ⟨cappedClockJoinedCoalition coalition.1,
          cappedClockJoinedCoalition_nonempty coalition.1⟩ none -
        reward ⟨cappedClockChildCoalition coalition.1,
          cappedClockChildCoalition_nonempty coalition.2⟩ none

private theorem exists_rational_responseWeights
    (reward : {A : Finset (Option ι) // A.Nonempty} → Option ι → ℝ)
    (hrational : ∀ coalition who, Math.IsRationalReal (reward coalition who))
    (withdrawal : WithdrawalResponseRow ι → ι → ℝ)
    (hwithdrawal : ∀ row i, Math.IsRationalReal (withdrawal row i))
    (hfeasible : ∃ advance retract : ι → ℝ,
      (∀ i, 0 ≤ advance i) ∧ (∀ i, 0 ≤ retract i) ∧
        ∀ row, withdrawalOutsideCoefficient reward row ≤
          ∑ i, (advance i * withdrawalAdvanceCoefficient reward row i +
            retract i * withdrawal row i)) :
    ∃ advance retract : ι → ℚ,
      (∀ i, 0 ≤ advance i) ∧ (∀ i, 0 ≤ retract i) ∧
        ∀ row, withdrawalOutsideCoefficient reward row ≤
          ∑ i, ((advance i : ℝ) * withdrawalAdvanceCoefficient reward row i +
            (retract i : ℝ) * withdrawal row i) := by
  classical
  let matrix := fun row coordinate =>
    Sum.elim (withdrawalAdvanceCoefficient reward row) (withdrawal row) coordinate
  have hadvance : ∀ row i,
      Math.IsRationalReal (withdrawalAdvanceCoefficient reward row i) := by
    intro row i
    cases row with
    | none => exact hrational _ _
    | some pair =>
        rcases pair with ⟨side, coalition⟩
        cases side <;> exact (hrational _ _).sub (hrational _ _)
  have houtside : ∀ row, Math.IsRationalReal (withdrawalOutsideCoefficient reward row) := by
    intro row
    cases row with
    | none => exact hrational _ _
    | some pair =>
        rcases pair with ⟨side, coalition⟩
        cases side <;> exact (hrational _ _).sub (hrational _ _)
  have hmatrix : ∀ row coordinate, Math.IsRationalReal (matrix row coordinate) := by
    intro row coordinate
    cases coordinate with
    | inl i => exact hadvance row i
    | inr i => exact hwithdrawal row i
  have hreal : ∃ point : ι ⊕ ι → ℝ, (∀ coordinate, 0 ≤ point coordinate) ∧
      ∀ row, withdrawalOutsideCoefficient reward row ≤
        ∑ coordinate, matrix row coordinate * point coordinate := by
    obtain ⟨advance, retract, hadvance, hretract, hrows⟩ := hfeasible
    refine ⟨Sum.elim advance retract, ?_, ?_⟩
    · intro coordinate
      cases coordinate with
      | inl i => exact hadvance i
      | inr i => exact hretract i
    · intro row
      simpa [matrix, Fintype.sum_sum_type, Finset.sum_add_distrib, mul_comm] using hrows row
  obtain ⟨point, hpoint, hrows⟩ :=
    Math.LinearProgramming.exists_nonnegative_rational_solution matrix
      (withdrawalOutsideCoefficient reward) hmatrix houtside hreal
  refine ⟨fun i => point (.inl i), fun i => point (.inr i),
    fun i => hpoint (.inl i), fun i => hpoint (.inr i), ?_⟩
  intro row
  simpa [matrix, Fintype.sum_sum_type, Finset.sum_add_distrib, mul_comm] using hrows row

theorem isRationalReal_deadlineWithdrawalZeroFloor
    (reward : {A : Finset (Option ι) // A.Nonempty} → Option ι → ℝ)
    (hrational : ∀ coalition who, Math.IsRationalReal (reward coalition who))
    (i : ι) : Math.IsRationalReal (deadlineWithdrawalZeroFloor reward i) := by
  classical
  unfold deadlineWithdrawalZeroFloor
  apply Math.IsRationalReal.finset_min
  intro value hvalue
  rcases Finset.mem_insert.mp hvalue with rfl | hpassive
  · exact Math.IsRationalReal.zero
  · obtain ⟨coalition, _, rfl⟩ := Finset.mem_image.mp hpassive
    exact hrational _ _

omit [Fintype ι] [DecidableEq ι] in
theorem isRationalReal_patientWithdrawalOwnNeverAlternative
    (reward : {A : Finset (Option ι) // A.Nonempty} → Option ι → ℝ)
    (hrational : ∀ coalition who, Math.IsRationalReal (reward coalition who))
    (i : ι) : Math.IsRationalReal (patientWithdrawalOwnNeverAlternative reward i) :=
  (hrational _ _).max Math.IsRationalReal.zero

theorem isRationalReal_patientWithdrawalFloor
    (reward : {A : Finset (Option ι) // A.Nonempty} → Option ι → ℝ)
    (hrational : ∀ coalition who, Math.IsRationalReal (reward coalition who))
    (i : ι) : Math.IsRationalReal (patientWithdrawalFloor reward i) := by
  classical
  unfold patientWithdrawalFloor
  apply Math.IsRationalReal.finset_min
  intro value hvalue
  rcases Finset.mem_insert.mp hvalue with rfl | hpassive
  · exact isRationalReal_patientWithdrawalOwnNeverAlternative reward hrational i
  · obtain ⟨coalition, _, rfl⟩ := Finset.mem_image.mp hpassive
    exact hrational _ _

private theorem rational_deadlineGain
    (reward : {A : Finset (Option ι) // A.Nonempty} → Option ι → ℝ)
    (hrational : ∀ coalition who, Math.IsRationalReal (reward coalition who))
    (i : ι) (A : Finset ι) (hA : A.Nonempty) :
    Math.IsRationalReal (deadlineWithdrawalGainFloor reward i A hA) := by
  classical
  unfold deadlineWithdrawalGainFloor
  split_ifs
  · exact (hrational _ _).sub (hrational _ _)
  · exact (isRationalReal_deadlineWithdrawalZeroFloor reward hrational i).sub
      (hrational _ _)
  · exact Math.IsRationalReal.zero

private theorem rational_restartGain
    (reward : {A : Finset (Option ι) // A.Nonempty} → Option ι → ℝ)
    (hrational : ∀ coalition who, Math.IsRationalReal (reward coalition who))
    (floor : ℝ) (hfloor : Math.IsRationalReal floor)
    (i : ι) (A : Finset ι) (hA : A.Nonempty) :
    Math.IsRationalReal (deadlineSecurityGainFloorWithRestart reward floor i A hA) := by
  classical
  unfold deadlineSecurityGainFloorWithRestart
  apply (rational_deadlineGain reward hrational i A hA).add
  split_ifs
  · exact hfloor.sub (isRationalReal_deadlineWithdrawalZeroFloor reward hrational i)
  · exact Math.IsRationalReal.zero

/-- Exact rational weights for the actual patient response rows. -/
theorem exists_rational_patientWithdrawalRewardCertificate
    (reward : {A : Finset (Option ι) // A.Nonempty} → Option ι → ℝ)
    (hrational : ∀ coalition who, Math.IsRationalReal (reward coalition who))
    (hfeasible : Nonempty (PatientWithdrawalRewardCertificate reward)) :
    ∃ certificate : PatientWithdrawalRewardCertificate reward,
      (∀ i, Math.IsRationalReal (certificate.advanceWeight i)) ∧
        ∀ i, Math.IsRationalReal (certificate.withdrawalWeight i) := by
  classical
  let withdrawal : WithdrawalResponseRow ι → ι → ℝ
    | none, i => patientWithdrawalOwnNeverAlternative reward i
    | some (_, coalition), i => patientWithdrawalGainFloor reward i coalition.1 coalition.2
  have hwithdrawal : ∀ row i, Math.IsRationalReal (withdrawal row i) := by
    intro row i
    cases row with
    | none => exact isRationalReal_patientWithdrawalOwnNeverAlternative reward hrational i
    | some pair =>
        exact rational_restartGain reward hrational _
          (isRationalReal_patientWithdrawalFloor reward hrational i) i pair.2.1 pair.2.2
  obtain ⟨realCertificate⟩ := hfeasible
  have hreal : ∃ advance retract : ι → ℝ, (∀ i, 0 ≤ advance i) ∧
      (∀ i, 0 ≤ retract i) ∧ ∀ row, withdrawalOutsideCoefficient reward row ≤
        ∑ i, (advance i * withdrawalAdvanceCoefficient reward row i +
          retract i * withdrawal row i) := by
    refine ⟨realCertificate.advanceWeight, realCertificate.withdrawalWeight,
      realCertificate.advanceWeight_nonneg, realCertificate.withdrawalWeight_nonneg, ?_⟩
    intro row
    cases row with
    | none =>
        simpa [withdrawalOutsideCoefficient, withdrawalAdvanceCoefficient, withdrawal,
          Finset.sum_add_distrib] using realCertificate.never_row
    | some pair =>
        rcases pair with ⟨side, coalition⟩
        cases side
        · exact realCertificate.future_row coalition.1 coalition.2
        · exact realCertificate.join_row coalition.1 coalition.2
  obtain ⟨advance, retract, hadvance, hretract, hrows⟩ :=
    exists_rational_responseWeights reward hrational withdrawal hwithdrawal hreal
  let certificate : PatientWithdrawalRewardCertificate reward :=
    { advanceWeight := fun i => (advance i : ℝ)
      withdrawalWeight := fun i => (retract i : ℝ)
      advanceWeight_nonneg := fun i => by exact_mod_cast hadvance i
      withdrawalWeight_nonneg := fun i => by exact_mod_cast hretract i
      never_row := by
        simpa [withdrawalOutsideCoefficient, withdrawalAdvanceCoefficient, withdrawal,
          Finset.sum_add_distrib] using hrows none
      future_row := fun A hA => hrows (some (false, ⟨A, hA⟩))
      join_row := fun A hA => hrows (some (true, ⟨A, hA⟩)) }
  exact ⟨certificate, fun i => ⟨advance i, rfl⟩, fun i => ⟨retract i, rfl⟩⟩

private theorem exists_rational_deadlineRows
    (reward : {A : Finset (Option ι) // A.Nonempty} → Option ι → ℝ)
    (hrational : ∀ coalition who, Math.IsRationalReal (reward coalition who))
    (gain : ι → ∀ (A : Finset ι), A.Nonempty → ℝ)
    (hgain : ∀ i A hA, Math.IsRationalReal (gain i A hA))
    (hfeasible : ∃ advance retract : ι → ℝ, (∀ i, 0 ≤ advance i) ∧
      (∀ i, 0 ≤ retract i) ∧
      reward ⟨{none}, Finset.singleton_nonempty none⟩ none ≤
        ∑ i, advance i * reward ⟨{some i}, Finset.singleton_nonempty (some i)⟩ (some i) ∧
      (∀ A hA, withdrawalOutsideCoefficient reward (some (false, ⟨A, hA⟩)) ≤
        ∑ i, advance i * withdrawalAdvanceCoefficient reward (some (false, ⟨A, hA⟩)) i) ∧
      ∀ A hA, withdrawalOutsideCoefficient reward (some (true, ⟨A, hA⟩)) ≤
        ∑ i, (advance i * withdrawalAdvanceCoefficient reward (some (true, ⟨A, hA⟩)) i +
          retract i * gain i A hA)) :
    ∃ advance retract : ι → ℚ, (∀ i, 0 ≤ advance i) ∧
      (∀ i, 0 ≤ retract i) ∧
      reward ⟨{none}, Finset.singleton_nonempty none⟩ none ≤
        ∑ i, (advance i : ℝ) *
          reward ⟨{some i}, Finset.singleton_nonempty (some i)⟩ (some i) ∧
      (∀ A hA, withdrawalOutsideCoefficient reward (some (false, ⟨A, hA⟩)) ≤
        ∑ i, (advance i : ℝ) *
          withdrawalAdvanceCoefficient reward (some (false, ⟨A, hA⟩)) i) ∧
      ∀ A hA, withdrawalOutsideCoefficient reward (some (true, ⟨A, hA⟩)) ≤
        ∑ i, ((advance i : ℝ) *
            withdrawalAdvanceCoefficient reward (some (true, ⟨A, hA⟩)) i +
          (retract i : ℝ) * gain i A hA) := by
  classical
  let withdrawal : WithdrawalResponseRow ι → ι → ℝ
    | some (true, coalition), i => gain i coalition.1 coalition.2
    | _, _ => 0
  have hwithdrawal : ∀ row i, Math.IsRationalReal (withdrawal row i) := by
    intro row
    cases row with
    | none => exact fun _ => Math.IsRationalReal.zero
    | some pair =>
        rcases pair with ⟨side, coalition⟩
        cases side
        · exact fun _ => Math.IsRationalReal.zero
        · intro i
          exact hgain i coalition.1 coalition.2
  have hreal : ∃ advance retract : ι → ℝ, (∀ i, 0 ≤ advance i) ∧
      (∀ i, 0 ≤ retract i) ∧ ∀ row, withdrawalOutsideCoefficient reward row ≤
        ∑ i, (advance i * withdrawalAdvanceCoefficient reward row i +
          retract i * withdrawal row i) := by
    obtain ⟨advance, retract, ha, hr, hnever, hfuture, hjoin⟩ := hfeasible
    refine ⟨advance, retract, ha, hr, ?_⟩
    intro row
    cases row with
    | none => simpa [withdrawal, withdrawalOutsideCoefficient,
        withdrawalAdvanceCoefficient] using hnever
    | some pair =>
        rcases pair with ⟨side, coalition⟩
        cases side
        · simpa [withdrawal] using hfuture coalition.1 coalition.2
        · exact hjoin coalition.1 coalition.2
  obtain ⟨advance, retract, ha, hr, hrows⟩ :=
    exists_rational_responseWeights reward hrational withdrawal hwithdrawal hreal
  refine ⟨advance, retract, ha, hr, ?_, ?_, ?_⟩
  · simpa [withdrawal, withdrawalOutsideCoefficient,
      withdrawalAdvanceCoefficient] using hrows none
  · intro A hA
    simpa [withdrawal] using hrows (some (false, ⟨A, hA⟩))
  · intro A hA
    exact hrows (some (true, ⟨A, hA⟩))

/-- Exact rational weights for the actual deadline-withdrawal response rows. -/
theorem exists_rational_deadlineWithdrawalRewardCertificate
    (reward : {A : Finset (Option ι) // A.Nonempty} → Option ι → ℝ)
    (hrational : ∀ coalition who, Math.IsRationalReal (reward coalition who))
    (hfeasible : Nonempty (DeadlineWithdrawalRewardCertificate reward)) :
    ∃ certificate : DeadlineWithdrawalRewardCertificate reward,
      (∀ i, Math.IsRationalReal (certificate.advanceWeight i)) ∧
        ∀ i, Math.IsRationalReal (certificate.withdrawalWeight i) := by
  obtain ⟨realCertificate⟩ := hfeasible
  obtain ⟨advance, retract, ha, hr, hnever, hfuture, hjoin⟩ :=
    exists_rational_deadlineRows reward hrational (deadlineWithdrawalGainFloor reward)
      (rational_deadlineGain reward hrational)
      ⟨realCertificate.advanceWeight, realCertificate.withdrawalWeight,
        realCertificate.advanceWeight_nonneg, realCertificate.withdrawalWeight_nonneg,
        realCertificate.never_row, realCertificate.future_row, realCertificate.join_row⟩
  let certificate : DeadlineWithdrawalRewardCertificate reward :=
    { advanceWeight := fun i => (advance i : ℝ)
      withdrawalWeight := fun i => (retract i : ℝ)
      advanceWeight_nonneg := fun i => by exact_mod_cast ha i
      withdrawalWeight_nonneg := fun i => by exact_mod_cast hr i
      never_row := hnever
      future_row := hfuture
      join_row := hjoin }
  exact ⟨certificate, fun i => ⟨advance i, rfl⟩, fun i => ⟨retract i, rfl⟩⟩

/-- The improved security floor is rational because the actual LP optimum is rational. -/
theorem isRationalReal_deadlineWithdrawalSecurityFloor
    (reward : {A : Finset (Option ι) // A.Nonempty} → Option ι → ℝ)
    (hrational : ∀ coalition who, Math.IsRationalReal (reward coalition who))
    (i : ι) : Math.IsRationalReal (deadlineWithdrawalSecurityFloor reward i) :=
  (isRationalReal_deadlineWithdrawalZeroFloor reward hrational i).max
    (isRationalReal_deadlineWithdrawalSecurityValue reward hrational i)

/-- Exact rational weights for the actual security-enhanced deadline response rows. -/
theorem exists_rational_deadlineSecurityRewardCertificate
    (reward : {A : Finset (Option ι) // A.Nonempty} → Option ι → ℝ)
    (hrational : ∀ coalition who, Math.IsRationalReal (reward coalition who))
    (hfeasible : Nonempty (DeadlineSecurityRewardCertificate reward)) :
    ∃ certificate : DeadlineSecurityRewardCertificate reward,
      (∀ i, Math.IsRationalReal (certificate.advanceWeight i)) ∧
        ∀ i, Math.IsRationalReal (certificate.withdrawalWeight i) := by
  have hgain : ∀ i A hA,
      Math.IsRationalReal (deadlineSecurityGainFloor reward i A hA) := by
    intro i A hA
    exact rational_restartGain reward hrational _
      ((isRationalReal_deadlineWithdrawalSecurityFloor reward hrational i).min
        Math.IsRationalReal.zero) i A hA
  obtain ⟨realCertificate⟩ := hfeasible
  obtain ⟨advance, retract, ha, hr, hnever, hfuture, hjoin⟩ :=
    exists_rational_deadlineRows reward hrational (deadlineSecurityGainFloor reward) hgain
      ⟨realCertificate.advanceWeight, realCertificate.withdrawalWeight,
        realCertificate.advanceWeight_nonneg, realCertificate.withdrawalWeight_nonneg,
        realCertificate.never_row, realCertificate.future_row, realCertificate.join_row⟩
  let certificate : DeadlineSecurityRewardCertificate reward :=
    { advanceWeight := fun i => (advance i : ℝ)
      withdrawalWeight := fun i => (retract i : ℝ)
      advanceWeight_nonneg := fun i => by exact_mod_cast ha i
      withdrawalWeight_nonneg := fun i => by exact_mod_cast hr i
      never_row := hnever
      future_row := hfuture
      join_row := hjoin }
  exact ⟨certificate, fun i => ⟨advance i, rfl⟩, fun i => ⟨retract i, rfl⟩⟩

/-- Ordinary advancing-only rows have exact rational weights. -/
theorem exists_rational_cappedClockParentRewardCertificate
    (reward : {A : Finset (Option ι) // A.Nonempty} → Option ι → ℝ)
    (hrational : ∀ coalition who, Math.IsRationalReal (reward coalition who))
    (hfeasible : Nonempty (CappedClockParentRewardCertificate reward)) :
    ∃ certificate : CappedClockParentRewardCertificate reward,
      ∀ i, Math.IsRationalReal (certificate.weight i) := by
  classical
  obtain ⟨realCertificate⟩ := hfeasible
  have hreal : ∃ advance retract : ι → ℝ, (∀ i, 0 ≤ advance i) ∧
      (∀ i, 0 ≤ retract i) ∧ ∀ row, withdrawalOutsideCoefficient reward row ≤
        ∑ i, (advance i * withdrawalAdvanceCoefficient reward row i + retract i * 0) := by
    refine ⟨realCertificate.weight, fun _ => 0, realCertificate.weight_nonneg,
      fun _ => le_rfl, ?_⟩
    intro row
    cases row with
    | none => simpa [withdrawalOutsideCoefficient, withdrawalAdvanceCoefficient] using
        realCertificate.never_row
    | some pair =>
        rcases pair with ⟨side, coalition⟩
        cases side
        · simpa only [withdrawalOutsideCoefficient, withdrawalAdvanceCoefficient,
            mul_zero, add_zero, sub_le_iff_le_add] using
            realCertificate.future_row coalition.1 coalition.2
        · simpa only [withdrawalOutsideCoefficient, withdrawalAdvanceCoefficient,
            mul_zero, add_zero, sub_le_iff_le_add] using
            realCertificate.join_row coalition.1 coalition.2
  obtain ⟨advance, retract, ha, hr, hrows⟩ :=
    exists_rational_responseWeights reward hrational (fun _ _ => 0)
      (fun _ _ => Math.IsRationalReal.zero) hreal
  let certificate : CappedClockParentRewardCertificate reward :=
    { weight := fun i => (advance i : ℝ)
      weight_nonneg := fun i => by exact_mod_cast ha i
      never_row := by
        simpa [withdrawalOutsideCoefficient, withdrawalAdvanceCoefficient] using hrows none
      future_row := fun A hA => by
        simpa only [withdrawalOutsideCoefficient, withdrawalAdvanceCoefficient,
          mul_zero, add_zero, sub_le_iff_le_add] using hrows (some (false, ⟨A, hA⟩))
      join_row := fun A hA => by
        simpa only [withdrawalOutsideCoefficient, withdrawalAdvanceCoefficient,
          mul_zero, add_zero, sub_le_iff_le_add] using hrows (some (true, ⟨A, hA⟩)) }
  exact ⟨certificate, fun i => ⟨advance i, rfl⟩⟩

/-- The relaxed future/join-only criterion also has rational weights.
No joint-Never row is silently imposed. -/
theorem exists_rational_cappedClockParentFutureJoinCertificate
    (reward : {A : Finset (Option ι) // A.Nonempty} → Option ι → ℝ)
    (hrational : ∀ coalition who, Math.IsRationalReal (reward coalition who))
    (hfeasible : Nonempty (CappedClockParentFutureJoinCertificate reward)) :
    ∃ certificate : CappedClockParentFutureJoinCertificate reward,
      ∀ i, Math.IsRationalReal (certificate.weight i) := by
  classical
  let rows := Bool × {coalition : Finset ι // coalition.Nonempty}
  let matrix := fun (row : rows) i => withdrawalAdvanceCoefficient reward (some row) i
  let rhs := fun (row : rows) => withdrawalOutsideCoefficient reward (some row)
  have hmatrix : ∀ row i, Math.IsRationalReal (matrix row i) := by
    rintro ⟨side, coalition⟩ i
    cases side <;> exact (hrational _ _).sub (hrational _ _)
  have hrhs : ∀ row, Math.IsRationalReal (rhs row) := by
    rintro ⟨side, coalition⟩
    cases side <;> exact (hrational _ _).sub (hrational _ _)
  obtain ⟨realCertificate⟩ := hfeasible
  have hreal : ∃ weight : ι → ℝ, (∀ i, 0 ≤ weight i) ∧
      ∀ row, rhs row ≤ ∑ i, matrix row i * weight i := by
    refine ⟨realCertificate.weight, realCertificate.weight_nonneg, ?_⟩
    rintro ⟨side, coalition⟩
    cases side
    · simpa [matrix, rhs, withdrawalAdvanceCoefficient, withdrawalOutsideCoefficient,
        mul_comm] using realCertificate.future_row coalition.1 coalition.2
    · simpa [matrix, rhs, withdrawalAdvanceCoefficient, withdrawalOutsideCoefficient,
        mul_comm] using realCertificate.join_row coalition.1 coalition.2
  obtain ⟨weight, hnonneg, hrows⟩ :=
    Math.LinearProgramming.exists_nonnegative_rational_solution matrix rhs
      hmatrix hrhs hreal
  let certificate : CappedClockParentFutureJoinCertificate reward :=
    { weight := fun i => (weight i : ℝ)
      weight_nonneg := fun i => by exact_mod_cast hnonneg i
      future_row := fun A hA => by
        simpa [matrix, rhs, withdrawalAdvanceCoefficient, withdrawalOutsideCoefficient,
          mul_comm] using hrows (false, ⟨A, hA⟩)
      join_row := fun A hA => by
        simpa [matrix, rhs, withdrawalAdvanceCoefficient, withdrawalOutsideCoefficient,
          mul_comm] using hrows (true, ⟨A, hA⟩) }
  exact ⟨certificate, fun i => ⟨weight i, rfl⟩⟩

/-- The terminal-only security criterion uses the unclamped rational LP floor. -/
theorem exists_rational_deadlineSecurityTerminalRewardCertificate
    (reward : {A : Finset (Option ι) // A.Nonempty} → Option ι → ℝ)
    (hrational : ∀ coalition who, Math.IsRationalReal (reward coalition who))
    (hfeasible : Nonempty (DeadlineSecurityTerminalRewardCertificate reward)) :
    ∃ certificate : DeadlineSecurityTerminalRewardCertificate reward,
      (∀ i, Math.IsRationalReal (certificate.advanceWeight i)) ∧
        ∀ i, Math.IsRationalReal (certificate.withdrawalWeight i) := by
  have hgain : ∀ i A hA, Math.IsRationalReal
      (deadlineSecurityGainFloorWithRestart reward
        (deadlineWithdrawalSecurityFloor reward i) i A hA) := by
    intro i A hA
    exact rational_restartGain reward hrational _
      (isRationalReal_deadlineWithdrawalSecurityFloor reward hrational i) i A hA
  obtain ⟨realCertificate⟩ := hfeasible
  obtain ⟨advance, retract, ha, hr, hnever, hfuture, hjoin⟩ :=
    exists_rational_deadlineRows reward hrational
      (fun i => deadlineSecurityGainFloorWithRestart reward
        (deadlineWithdrawalSecurityFloor reward i) i) hgain
      ⟨realCertificate.advanceWeight, realCertificate.withdrawalWeight,
        realCertificate.advanceWeight_nonneg, realCertificate.withdrawalWeight_nonneg,
        realCertificate.never_row, realCertificate.future_row,
        fun A hA => by
          simpa only [withdrawalOutsideCoefficient, withdrawalAdvanceCoefficient,
            add_zero, sub_le_iff_le_add] using realCertificate.join_row A hA⟩
  let certificate : DeadlineSecurityTerminalRewardCertificate reward :=
    { advanceWeight := fun i => (advance i : ℝ)
      withdrawalWeight := fun i => (retract i : ℝ)
      advanceWeight_nonneg := fun i => by exact_mod_cast ha i
      withdrawalWeight_nonneg := fun i => by exact_mod_cast hr i
      never_row := hnever
      future_row := hfuture
      join_row := fun A hA => by
        simpa only [withdrawalOutsideCoefficient, withdrawalAdvanceCoefficient,
          add_zero, sub_le_iff_le_add] using hjoin A hA }
  exact ⟨certificate, fun i => ⟨advance i, rfl⟩, fun i => ⟨retract i, rfl⟩⟩

end GameTheory
