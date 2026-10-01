import UniformEquilibrium.Quitting.Classification.QuietExtension.RationalWithdrawalWeights
import UniformEquilibrium.Quitting.Classification.QuietExtension.WithdrawalFutureJoinRaw

/-!
# Rational weights for all five omitted-Never withdrawal criteria

Only the actual finite F/J reward rows are rationalized. No Never row is
added, not even implicitly through the full-certificate producer. Actual
patient, zero-based and LP security floors inherit rationality from their
canonical source lemmas. Weak equalities, zero weights and empty child
types are retained. Separate-response coefficients remain sums, whereas
disjoint deadline-response coefficients remain maxima. This is not an
all-evaluation guarantee for a certificate with its Never row omitted.
-/

noncomputable section

namespace GameTheory

open scoped BigOperators

variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem WithdrawalFutureJoinKind.isRationalReal_gain
    (kind : WithdrawalFutureJoinKind)
    (reward : {A : Finset (Option ι) // A.Nonempty} → Option ι → ℝ)
    (hrational : ∀ coalition who, Math.IsRationalReal (reward coalition who))
    (i : ι) (A : Finset ι) (hA : A.Nonempty) :
    Math.IsRationalReal (kind.gain reward i A hA) := by
  cases kind with
  | patient =>
      exact isRationalReal_deadlineSecurityGainFloorWithRestart reward hrational _
        (isRationalReal_patientWithdrawalFloor reward hrational i) i A hA
  | deadline => exact isRationalReal_deadlineWithdrawalGainFloor reward hrational i A hA
  | evaluatedSecurity =>
      exact isRationalReal_deadlineSecurityGainFloorWithRestart reward hrational _
        ((isRationalReal_deadlineWithdrawalSecurityFloor reward hrational i).min
          Math.IsRationalReal.zero) i A hA
  | terminalSecurity =>
      exact isRationalReal_deadlineSecurityGainFloorWithRestart reward hrational _
        (isRationalReal_deadlineWithdrawalSecurityFloor reward hrational i) i A hA
  | cancellation => exact isRationalReal_deadlineWithdrawalGainFloor reward hrational i A hA

/-- No joint-Never row or source response-cap premise is imposed. -/
theorem exists_rational_withdrawalFutureJoinRewardCertificate
    (kind : WithdrawalFutureJoinKind)
    (reward : {A : Finset (Option ι) // A.Nonempty} → Option ι → ℝ)
    (hrational : ∀ coalition who, Math.IsRationalReal (reward coalition who))
    (hfeasible : Nonempty (WithdrawalFutureJoinRewardCertificate kind reward)) :
    ∃ certificate : WithdrawalFutureJoinRewardCertificate kind reward,
      (∀ i, Math.IsRationalReal (certificate.advanceWeight i)) ∧
        ∀ i, Math.IsRationalReal (certificate.withdrawalWeight i) := by
  classical
  let rows := Bool × {coalition : Finset ι // coalition.Nonempty}
  let retractCoefficient (row : rows) (i : ι) :=
    if row.1 then kind.gain reward i row.2.1 row.2.2
    else kind.futureWeight 1 * kind.gain reward i row.2.1 row.2.2
  let matrix := fun (row : rows) coordinate =>
    Sum.elim (withdrawalAdvanceCoefficient reward (some row))
      (retractCoefficient row) coordinate
  let rhs := fun (row : rows) => withdrawalOutsideCoefficient reward (some row)
  have hmatrix : ∀ row coordinate, Math.IsRationalReal (matrix row coordinate) := by
    rintro ⟨side, coalition⟩ coordinate
    cases coordinate with
    | inl i => cases side <;> exact (hrational _ _).sub (hrational _ _)
    | inr i =>
        have hgain := kind.isRationalReal_gain reward hrational i coalition.1 coalition.2
        cases side
        · have hfactor : Math.IsRationalReal (kind.futureWeight 1) := by
            cases kind <;> first | exact Math.IsRationalReal.one | exact Math.IsRationalReal.zero
          exact hfactor.mul hgain
        · exact hgain
  have hrhs : ∀ row, Math.IsRationalReal (rhs row) := by
    rintro ⟨side, coalition⟩
    cases side <;> exact (hrational _ _).sub (hrational _ _)
  obtain ⟨realCertificate⟩ := hfeasible
  have hreal : ∃ point : ι ⊕ ι → ℝ, (∀ coordinate, 0 ≤ point coordinate) ∧
      ∀ row, rhs row ≤ ∑ coordinate, matrix row coordinate * point coordinate := by
    refine ⟨Sum.elim realCertificate.advanceWeight realCertificate.withdrawalWeight, ?_, ?_⟩
    · intro coordinate
      cases coordinate with
      | inl i => exact realCertificate.advanceWeight_nonneg i
      | inr i => exact realCertificate.withdrawalWeight_nonneg i
    · rintro ⟨side, coalition⟩
      cases side
      · have hsource := realCertificate.future_row coalition.1 coalition.2
        cases kind
        all_goals simpa [matrix, rhs, retractCoefficient,
          withdrawalAdvanceCoefficient, withdrawalOutsideCoefficient,
          WithdrawalFutureJoinKind.futureWeight, Fintype.sum_sum_type,
          Finset.sum_add_distrib, mul_comm] using hsource
      · simpa [matrix, rhs, retractCoefficient,
          withdrawalAdvanceCoefficient, withdrawalOutsideCoefficient,
          Fintype.sum_sum_type, Finset.sum_add_distrib, mul_comm] using
          realCertificate.join_row coalition.1 coalition.2
  obtain ⟨point, hpoint, hrows⟩ :=
    Math.LinearProgramming.exists_nonnegative_rational_solution matrix rhs hmatrix hrhs hreal
  have hweightedRows (row : rows) : rhs row ≤
      ∑ i, ((point (.inl i) : ℝ) * withdrawalAdvanceCoefficient reward (some row) i +
        (point (.inr i) : ℝ) * retractCoefficient row i) := by
    calc
      rhs row ≤ ∑ coordinate, matrix row coordinate * (point coordinate : ℝ) := hrows row
      _ = _ := by
        rw [Fintype.sum_sum_type, Finset.sum_add_distrib]
        apply congrArg₂ (· + ·)
        · apply Finset.sum_congr rfl
          intro i _
          change withdrawalAdvanceCoefficient reward (some row) i * (point (.inl i) : ℝ) =
            (point (.inl i) : ℝ) * withdrawalAdvanceCoefficient reward (some row) i
          exact mul_comm _ _
        · apply Finset.sum_congr rfl
          intro i _
          change retractCoefficient row i * (point (.inr i) : ℝ) =
            (point (.inr i) : ℝ) * retractCoefficient row i
          exact mul_comm _ _
  let certificate : WithdrawalFutureJoinRewardCertificate kind reward :=
    { advanceWeight := fun i => (point (.inl i) : ℝ)
      withdrawalWeight := fun i => (point (.inr i) : ℝ)
      advanceWeight_nonneg := fun i => Rat.cast_nonneg.mpr (hpoint (.inl i))
      withdrawalWeight_nonneg := fun i => Rat.cast_nonneg.mpr (hpoint (.inr i))
      future_row := fun A hA => by
        cases kind
        all_goals simpa [rhs, retractCoefficient,
          withdrawalAdvanceCoefficient, withdrawalOutsideCoefficient,
          WithdrawalFutureJoinKind.futureWeight] using hweightedRows (false, ⟨A, hA⟩)
      join_row := fun A hA => by
        simpa [rhs, retractCoefficient, withdrawalAdvanceCoefficient,
          withdrawalOutsideCoefficient] using hweightedRows (true, ⟨A, hA⟩) }
  exact ⟨certificate, fun i => ⟨point (.inl i), rfl⟩, fun i => ⟨point (.inr i), rfl⟩⟩

theorem WithdrawalFutureJoinRewardCertificate.isRationalReal_debtWeight
    {kind : WithdrawalFutureJoinKind}
    {reward : {A : Finset (Option ι) // A.Nonempty} → Option ι → ℝ}
    (certificate : WithdrawalFutureJoinRewardCertificate kind reward)
    (hadvance : ∀ i, Math.IsRationalReal (certificate.advanceWeight i))
    (hwithdrawal : ∀ i, Math.IsRationalReal (certificate.withdrawalWeight i)) (i : ι) :
    Math.IsRationalReal (certificate.debtWeight i) := by
  change Math.IsRationalReal
    (kind.debtWeight (certificate.advanceWeight i) (certificate.withdrawalWeight i))
  cases kind
  all_goals
    first
    | exact (hadvance i).add (hwithdrawal i)
    | exact (hadvance i).max (hwithdrawal i)

theorem WithdrawalFutureJoinRewardCertificate.isRationalReal_neverExcess
    {kind : WithdrawalFutureJoinKind}
    {reward : {A : Finset (Option ι) // A.Nonempty} → Option ι → ℝ}
    (certificate : WithdrawalFutureJoinRewardCertificate kind reward)
    (hrational : ∀ coalition who, Math.IsRationalReal (reward coalition who))
    (hadvance : ∀ i, Math.IsRationalReal (certificate.advanceWeight i))
    (hwithdrawal : ∀ i, Math.IsRationalReal (certificate.withdrawalWeight i)) :
    Math.IsRationalReal certificate.neverExcess := by
  have hbonus : Math.IsRationalReal (kind.neverBonus reward certificate.withdrawalWeight) := by
    cases kind
    · apply Math.IsRationalReal.sum
      intro i _
      exact (hwithdrawal i).mul
        (isRationalReal_patientWithdrawalOwnNeverAlternative reward hrational i)
    all_goals exact Math.IsRationalReal.zero
  apply ((hrational _ _).sub (Math.IsRationalReal.add ?_ hbonus)).max Math.IsRationalReal.zero
  apply Math.IsRationalReal.sum
  intro i _
  exact (hadvance i).mul (hrational _ _)

/-- The same produced certificate retains rational operation-specific debt and residual. -/
theorem exists_rational_withdrawalFutureJoinRewardCertificate_debtWeight_and_neverExcess
    (kind : WithdrawalFutureJoinKind)
    (reward : {A : Finset (Option ι) // A.Nonempty} → Option ι → ℝ)
    (hrational : ∀ coalition who, Math.IsRationalReal (reward coalition who))
    (hfeasible : Nonempty (WithdrawalFutureJoinRewardCertificate kind reward)) :
    ∃ certificate : WithdrawalFutureJoinRewardCertificate kind reward,
      (∀ i, Math.IsRationalReal (certificate.advanceWeight i)) ∧
        (∀ i, Math.IsRationalReal (certificate.withdrawalWeight i)) ∧
        (∀ i, Math.IsRationalReal (certificate.debtWeight i)) ∧
        Math.IsRationalReal certificate.neverExcess := by
  obtain ⟨certificate, hadvance, hwithdrawal⟩ :=
    exists_rational_withdrawalFutureJoinRewardCertificate kind reward hrational hfeasible
  exact ⟨certificate, hadvance, hwithdrawal,
    fun i => certificate.isRationalReal_debtWeight hadvance hwithdrawal i,
    certificate.isRationalReal_neverExcess hrational hadvance hwithdrawal⟩

end GameTheory
