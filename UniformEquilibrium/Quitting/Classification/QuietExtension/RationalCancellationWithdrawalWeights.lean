import UniformEquilibrium.Quitting.Classification.QuietExtension.RationalWithdrawalWeights
import UniformEquilibrium.Quitting.Classification.QuietExtension.CancellationWithdrawal

/-!
# Exact rational cancellation weights

The canonical evaluated-cancellation raw reward rows admit rational weights
whenever they admit real weights and every actual reward coordinate is
rational. Both finite F/J families use the actual zero-based withdrawal gain;
the Never row has no withdrawal term. Cancellation and advancing weights
add in the debt comparison. Equality rows, zero weights and empty child
types are retained. This is finite row feasibility, not rational optimality
for an arbitrary real reward table or a supplied strategic-cap argument.
-/

noncomputable section

namespace GameTheory

open scoped BigOperators

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- A real-feasible actual cancellation certificate has rational weights. -/
theorem exists_rational_cancellationWithdrawalRewardCertificate
    (reward : {A : Finset (Option ι) // A.Nonempty} → Option ι → ℝ)
    (hrational : ∀ coalition who, Math.IsRationalReal (reward coalition who))
    (hfeasible : Nonempty (CancellationWithdrawalRewardCertificate reward)) :
    ∃ certificate : CancellationWithdrawalRewardCertificate reward,
      (∀ i, Math.IsRationalReal (certificate.advanceWeight i)) ∧
        ∀ i, Math.IsRationalReal (certificate.withdrawalWeight i) := by
  classical
  let withdrawal : WithdrawalResponseRow ι → ι → ℝ
    | none, _ => 0
    | some (_, coalition), i =>
        deadlineWithdrawalGainFloor reward i coalition.1 coalition.2
  have hwithdrawal : ∀ row i, Math.IsRationalReal (withdrawal row i) := by
    intro row
    cases row with
    | none => exact fun _ => Math.IsRationalReal.zero
    | some pair => exact fun i =>
        isRationalReal_deadlineWithdrawalGainFloor reward hrational i pair.2.1 pair.2.2
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
        simpa only [withdrawalOutsideCoefficient, withdrawalAdvanceCoefficient,
          withdrawal, mul_zero, add_zero] using realCertificate.never_row
    | some pair =>
        rcases pair with ⟨side, coalition⟩
        cases side
        · exact realCertificate.future_row coalition.1 coalition.2
        · exact realCertificate.join_row coalition.1 coalition.2
  obtain ⟨advance, retract, hadvance, hretract, hrows⟩ :=
    exists_rational_withdrawalResponseWeights reward hrational withdrawal hwithdrawal hreal
  let certificate : CancellationWithdrawalRewardCertificate reward :=
    { advanceWeight := fun i => (advance i : ℝ)
      withdrawalWeight := fun i => (retract i : ℝ)
      advanceWeight_nonneg := fun i => Rat.cast_nonneg.mpr (hadvance i)
      withdrawalWeight_nonneg := fun i => Rat.cast_nonneg.mpr (hretract i)
      never_row := by
        simpa only [withdrawalOutsideCoefficient, withdrawalAdvanceCoefficient,
          withdrawal, mul_zero, add_zero] using hrows none
      future_row := fun A hA => hrows (some (false, ⟨A, hA⟩))
      join_row := fun A hA => hrows (some (true, ⟨A, hA⟩)) }
  exact ⟨certificate, fun i => ⟨advance i, rfl⟩, fun i => ⟨retract i, rfl⟩⟩

/-- The same source-produced certificate has rational summed debt coefficients. -/
theorem exists_rational_cancellationWithdrawalRewardCertificate_debtWeight
    (reward : {A : Finset (Option ι) // A.Nonempty} → Option ι → ℝ)
    (hrational : ∀ coalition who, Math.IsRationalReal (reward coalition who))
    (hfeasible : Nonempty (CancellationWithdrawalRewardCertificate reward)) :
    ∃ certificate : CancellationWithdrawalRewardCertificate reward,
      (∀ i, Math.IsRationalReal (certificate.advanceWeight i)) ∧
        (∀ i, Math.IsRationalReal (certificate.withdrawalWeight i)) ∧
        ∀ i, Math.IsRationalReal (certificate.debtWeight i) := by
  obtain ⟨certificate, hadvance, hwithdrawal⟩ :=
    exists_rational_cancellationWithdrawalRewardCertificate reward hrational hfeasible
  exact ⟨certificate, hadvance, hwithdrawal, fun i => (hadvance i).add (hwithdrawal i)⟩

end GameTheory
