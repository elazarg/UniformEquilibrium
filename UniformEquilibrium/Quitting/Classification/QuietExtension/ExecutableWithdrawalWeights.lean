import UniformEquilibrium.Quitting.Classification.QuietExtension.ExecutableWithdrawalSecurity
import UniformEquilibrium.Quitting.Classification.QuietExtension.WithdrawalFutureJoinRaw

/-! # Executable weights for actual full and omitted-Never withdrawal rows

Every coefficient comes from the actual rational table and the canonical finite
or security floor. Source feasibility is used only as an erased proposition.
The five operation kinds retain their distinct future and Never coefficients.
-/

namespace GameTheory.ExecutableWithdrawal

open scoped BigOperators

variable {ι : Type} [Fintype ι] [DecidableEq ι] [Encodable ι]

def gain (kind : WithdrawalFutureJoinKind) (reward : Reward ι)
    (i : ι) (A : Finset ι) (hA : A.Nonempty) : ℚ :=
  match kind with
  | .patient => restartGain reward (patientFloor reward i) i A hA
  | .deadline | .cancellation => zeroGain reward i A hA
  | .evaluatedSecurity => restartGain reward (min (securityFloor reward i) 0) i A hA
  | .terminalSecurity => restartGain reward (securityFloor reward i) i A hA

theorem gain_cast (kind : WithdrawalFutureJoinKind) (reward : Reward ι)
    (i : ι) (A : Finset ι) (hA : A.Nonempty) :
    (gain kind reward i A hA : ℝ) = kind.gain (toReal reward) i A hA := by
  cases kind
  · change (restartGain reward (patientFloor reward i) i A hA : ℝ) =
      deadlineSecurityGainFloorWithRestart (toReal reward)
        (patientWithdrawalFloor (toReal reward) i) i A hA
    rw [restartGain_cast, patientFloor_cast]
  · exact zeroGain_cast reward i A hA
  · simp only [gain, restartGain_cast, Rat.cast_min, Rat.cast_zero, securityFloor_cast,
      WithdrawalFutureJoinKind.gain, deadlineSecurityGainFloor]
  · simp only [gain, restartGain_cast, securityFloor_cast, WithdrawalFutureJoinKind.gain]
  · exact zeroGain_cast reward i A hA

def futureFactor : WithdrawalFutureJoinKind → ℚ
  | .patient | .cancellation => 1
  | .deadline | .evaluatedSecurity | .terminalSecurity => 0

def retractCoefficient (kind : WithdrawalFutureJoinKind) (reward : Reward ι) :
    WithdrawalResponseRow ι → ι → ℚ
  | none, i => match kind with | .patient => ownNever reward i | _ => 0
  | some (false, A), i => futureFactor kind * gain kind reward i A.1 A.2
  | some (true, A), i => gain kind reward i A.1 A.2

noncomputable def realRetractCoefficient
    (kind : WithdrawalFutureJoinKind) (reward : Reward ι) :
    WithdrawalResponseRow ι → ι → ℝ
  | none, i => match kind with
      | .patient => patientWithdrawalOwnNeverAlternative (toReal reward) i | _ => 0
  | some (false, A), i => kind.futureWeight 1 * kind.gain (toReal reward) i A.1 A.2
  | some (true, A), i => kind.gain (toReal reward) i A.1 A.2

theorem retractCoefficient_cast (kind : WithdrawalFutureJoinKind) (reward : Reward ι)
    (row : WithdrawalResponseRow ι) (i : ι) :
    (retractCoefficient kind reward row i : ℝ) = realRetractCoefficient kind reward row i := by
  cases row with
  | none =>
      cases kind <;> simp only [retractCoefficient, realRetractCoefficient,
        ownNever_cast, Rat.cast_zero]
  | some row =>
      rcases row with ⟨side, A⟩
      cases side
      · cases kind <;> simp only [retractCoefficient, realRetractCoefficient,
          futureFactor, WithdrawalFutureJoinKind.futureWeight, Rat.cast_mul,
          Rat.cast_one, Rat.cast_zero, gain_cast]
      · exact gain_cast kind reward i A.1 A.2

def weightMatrix (kind : WithdrawalFutureJoinKind) (reward : Reward ι)
    (row : WithdrawalResponseRow ι) : ι ⊕ ι → ℚ :=
  Sum.elim (advanceCoefficient reward row) (retractCoefficient kind reward row)

theorem weightMatrix_eval (kind : WithdrawalFutureJoinKind) (reward : Reward ι)
    (row : WithdrawalResponseRow ι) (point : ι ⊕ ι → ℝ) :
    (∑ coordinate, (weightMatrix kind reward row coordinate : ℝ) * point coordinate) =
      ∑ i, (point (.inl i) * withdrawalAdvanceCoefficient (toReal reward) row i +
        point (.inr i) * realRetractCoefficient kind reward row i) := by
  simp only [weightMatrix, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr,
    advanceCoefficient_cast, retractCoefficient_cast, Finset.sum_add_distrib, mul_comm]

theorem futureJoin_realFeasible
    (kind : WithdrawalFutureJoinKind) (reward : Reward ι)
    (hsource : Nonempty (WithdrawalFutureJoinRewardCertificate kind (toReal reward))) :
    ∃ point : ι ⊕ ι → ℝ, (∀ coordinate, 0 ≤ point coordinate) ∧
      ∀ row : Bool × {A : Finset ι // A.Nonempty},
        (outsideCoefficient reward (some row) : ℝ) ≤
          ∑ coordinate, (weightMatrix kind reward (some row) coordinate : ℝ) *
            point coordinate := by
  obtain ⟨certificate⟩ := hsource
  refine ⟨Sum.elim certificate.advanceWeight certificate.withdrawalWeight, ?_, ?_⟩
  · intro coordinate
    cases coordinate with
    | inl i => exact certificate.advanceWeight_nonneg i
    | inr i => exact certificate.withdrawalWeight_nonneg i
  · rintro ⟨side, A⟩
    rw [outsideCoefficient_cast, weightMatrix_eval]
    cases side
    · have h := certificate.future_row A.1 A.2
      cases kind <;> simpa [withdrawalOutsideCoefficient, withdrawalAdvanceCoefficient,
        realRetractCoefficient, WithdrawalFutureJoinKind.futureWeight] using h
    · exact certificate.join_row A.1 A.2

theorem full_realFeasible
    (kind : WithdrawalFutureJoinKind) (reward : Reward ι)
    (hsource : Nonempty (kind.FullCertificate (toReal reward))) :
    ∃ point : ι ⊕ ι → ℝ, (∀ coordinate, 0 ≤ point coordinate) ∧
      ∀ row, (outsideCoefficient reward row : ℝ) ≤
        ∑ coordinate, (weightMatrix kind reward row coordinate : ℝ) * point coordinate := by
  obtain ⟨certificate⟩ := hsource
  cases kind
  all_goals
    refine ⟨Sum.elim certificate.advanceWeight certificate.withdrawalWeight, ?_, ?_⟩
    · intro coordinate
      cases coordinate with
      | inl i => exact certificate.advanceWeight_nonneg i
      | inr i => exact certificate.withdrawalWeight_nonneg i
    · intro row
      rw [outsideCoefficient_cast, weightMatrix_eval]
      cases row with
      | none =>
          simpa [withdrawalOutsideCoefficient, withdrawalAdvanceCoefficient,
            realRetractCoefficient, Finset.sum_add_distrib] using certificate.never_row
      | some row =>
          rcases row with ⟨side, A⟩
          cases side
          · simpa [withdrawalOutsideCoefficient, withdrawalAdvanceCoefficient,
              realRetractCoefficient, WithdrawalFutureJoinKind.futureWeight,
              WithdrawalFutureJoinKind.gain] using
                certificate.future_row A.1 A.2
          · simpa [withdrawalOutsideCoefficient, withdrawalAdvanceCoefficient,
              realRetractCoefficient, WithdrawalFutureJoinKind.gain] using
                certificate.join_row A.1 A.2

def futureJoinWeights (kind : WithdrawalFutureJoinKind) (reward : Reward ι)
    (hsource : Nonempty (WithdrawalFutureJoinRewardCertificate kind (toReal reward))) :
    ι ⊕ ι → ℚ :=
  Math.LinearProgramming.selectNonnegativeRationalFeasible
    (fun row => weightMatrix kind reward (some row))
    (fun row => outsideCoefficient reward (some row))
    (futureJoin_realFeasible kind reward hsource)

def fullWeights (kind : WithdrawalFutureJoinKind) (reward : Reward ι)
    (hsource : Nonempty (kind.FullCertificate (toReal reward))) : ι ⊕ ι → ℚ :=
  Math.LinearProgramming.selectNonnegativeRationalFeasible
    (weightMatrix kind reward) (outsideCoefficient reward) (full_realFeasible kind reward hsource)

/-- Real certificate construction is semantic only; its weights are the computed rational data. -/
noncomputable def futureJoinCertificateOfRows
    (kind : WithdrawalFutureJoinKind) (reward : Reward ι) (point : ι ⊕ ι → ℚ)
    (hnonneg : ∀ coordinate, 0 ≤ point coordinate)
    (hrows : ∀ row : Bool × {A : Finset ι // A.Nonempty},
      outsideCoefficient reward (some row) ≤
        ∑ coordinate, weightMatrix kind reward (some row) coordinate * point coordinate) :
    WithdrawalFutureJoinRewardCertificate kind (toReal reward) where
  advanceWeight i := (point (.inl i) : ℝ)
  withdrawalWeight i := (point (.inr i) : ℝ)
  advanceWeight_nonneg i := Rat.cast_nonneg.mpr (hnonneg (.inl i))
  withdrawalWeight_nonneg i := Rat.cast_nonneg.mpr (hnonneg (.inr i))
  future_row A hA := by
    have h : (outsideCoefficient reward (some (false, ⟨A, hA⟩)) : ℝ) ≤
        ∑ coordinate, (weightMatrix kind reward (some (false, ⟨A, hA⟩)) coordinate : ℝ) *
          (point coordinate : ℝ) := by exact_mod_cast hrows (false, ⟨A, hA⟩)
    rw [outsideCoefficient_cast, weightMatrix_eval] at h
    cases kind <;> simpa [withdrawalOutsideCoefficient, withdrawalAdvanceCoefficient,
      realRetractCoefficient, WithdrawalFutureJoinKind.futureWeight] using h
  join_row A hA := by
    have h : (outsideCoefficient reward (some (true, ⟨A, hA⟩)) : ℝ) ≤
        ∑ coordinate, (weightMatrix kind reward (some (true, ⟨A, hA⟩)) coordinate : ℝ) *
          (point coordinate : ℝ) := by exact_mod_cast hrows (true, ⟨A, hA⟩)
    rw [outsideCoefficient_cast, weightMatrix_eval] at h
    exact h

noncomputable def futureJoinCertificate
    (kind : WithdrawalFutureJoinKind) (reward : Reward ι)
    (hsource : Nonempty (WithdrawalFutureJoinRewardCertificate kind (toReal reward))) :
    WithdrawalFutureJoinRewardCertificate kind (toReal reward) :=
  futureJoinCertificateOfRows kind reward (futureJoinWeights kind reward hsource)
    (Math.LinearProgramming.selectNonnegativeRationalFeasible_spec _ _ _).1
    (Math.LinearProgramming.selectNonnegativeRationalFeasible_spec _ _ _).2

noncomputable def fullFutureJoinCertificate
    (kind : WithdrawalFutureJoinKind) (reward : Reward ι)
    (hsource : Nonempty (kind.FullCertificate (toReal reward))) :
    WithdrawalFutureJoinRewardCertificate kind (toReal reward) :=
  futureJoinCertificateOfRows kind reward (fullWeights kind reward hsource)
    (Math.LinearProgramming.selectNonnegativeRationalFeasible_spec _ _ _).1
    (fun row => (Math.LinearProgramming.selectNonnegativeRationalFeasible_spec _ _ _).2 (some row))

theorem fullFutureJoinCertificate_never
    (kind : WithdrawalFutureJoinKind) (reward : Reward ι)
    (hsource : Nonempty (kind.FullCertificate (toReal reward))) :
    toReal reward ⟨{none}, Finset.singleton_nonempty none⟩ none ≤
      (fullFutureJoinCertificate kind reward hsource).neverRightSide := by
  have h := (Math.LinearProgramming.selectNonnegativeRationalFeasible_spec
    (weightMatrix kind reward) (outsideCoefficient reward)
    (full_realFeasible kind reward hsource)).2 none
  have hcast : (outsideCoefficient reward none : ℝ) ≤
      ∑ coordinate, (weightMatrix kind reward none coordinate : ℝ) *
        (fullWeights kind reward hsource coordinate : ℝ) := by exact_mod_cast h
  rw [outsideCoefficient_cast, weightMatrix_eval] at hcast
  cases kind <;> simpa [fullFutureJoinCertificate, futureJoinCertificateOfRows,
    WithdrawalFutureJoinRewardCertificate.neverRightSide, WithdrawalFutureJoinKind.neverBonus,
    realRetractCoefficient, withdrawalOutsideCoefficient, withdrawalAdvanceCoefficient,
    Finset.sum_add_distrib] using hcast

end GameTheory.ExecutableWithdrawal
