import UniformEquilibrium.Quitting.Classification.QuietExtension.ExecutableWithdrawalWeights
import UniformEquilibrium.Quitting.Classification.QuietExtension.WithdrawalFutureJoinDebt

/-! # Computed debt coefficients and the exact omitted-Never correction

These rational values retain the operation's sum/max convention and the actual
patient Never bonus. The positive-singleton denominator is the actual reward.
-/

namespace GameTheory.ExecutableWithdrawal

open scoped BigOperators

variable {ι : Type} [Fintype ι] [DecidableEq ι] [Encodable ι]

def debtWeight (kind : WithdrawalFutureJoinKind) (point : ι ⊕ ι → ℚ) (i : ι) : ℚ :=
  match kind with
  | .patient | .cancellation => point (.inl i) + point (.inr i)
  | .deadline | .evaluatedSecurity | .terminalSecurity => max (point (.inl i)) (point (.inr i))

def neverBonus (kind : WithdrawalFutureJoinKind) (reward : Reward ι)
    (point : ι ⊕ ι → ℚ) : ℚ :=
  match kind with
  | .patient => ∑ i, point (.inr i) * ownNever reward i
  | _ => 0

def neverExcess (kind : WithdrawalFutureJoinKind) (reward : Reward ι)
    (point : ι ⊕ ι → ℚ) : ℚ :=
  max (outsideCoefficient reward none -
    ((∑ i, point (.inl i) * singleton reward i) + neverBonus kind reward point)) 0

def correctedWeight (kind : WithdrawalFutureJoinKind) (reward : Reward ι)
    (point : ι ⊕ ι → ℚ) (pivot i : ι) : ℚ :=
  debtWeight kind point i +
    if i = pivot then neverExcess kind reward point / singleton reward pivot else 0

theorem debtWeight_cast
    (kind : WithdrawalFutureJoinKind) (reward : Reward ι) (point : ι ⊕ ι → ℚ)
    (hnonneg : ∀ coordinate, 0 ≤ point coordinate)
    (hrows : ∀ row : Bool × {A : Finset ι // A.Nonempty},
      outsideCoefficient reward (some row) ≤
        ∑ coordinate, weightMatrix kind reward (some row) coordinate * point coordinate)
    (i : ι) :
    (debtWeight kind point i : ℝ) =
      (futureJoinCertificateOfRows kind reward point hnonneg hrows).debtWeight i := by
  cases kind <;> simp only [debtWeight, Rat.cast_add, Rat.cast_max,
    WithdrawalFutureJoinRewardCertificate.debtWeight, WithdrawalFutureJoinKind.debtWeight,
    futureJoinCertificateOfRows]

theorem neverExcess_cast
    (kind : WithdrawalFutureJoinKind) (reward : Reward ι) (point : ι ⊕ ι → ℚ)
    (hnonneg : ∀ coordinate, 0 ≤ point coordinate)
    (hrows : ∀ row : Bool × {A : Finset ι // A.Nonempty},
      outsideCoefficient reward (some row) ≤
        ∑ coordinate, weightMatrix kind reward (some row) coordinate * point coordinate) :
    (neverExcess kind reward point : ℝ) =
      (futureJoinCertificateOfRows kind reward point hnonneg hrows).neverExcess := by
  cases kind <;> simp only [neverExcess, neverBonus, Rat.cast_max, Rat.cast_sub,
    Rat.cast_add, Rat.cast_sum, Rat.cast_mul, Rat.cast_zero, ownNever_cast,
    outsideCoefficient_cast, withdrawalOutsideCoefficient, singleton, toReal,
    WithdrawalFutureJoinRewardCertificate.neverExcess,
    WithdrawalFutureJoinRewardCertificate.neverRightSide,
    WithdrawalFutureJoinKind.neverBonus, futureJoinCertificateOfRows]

theorem correctedWeight_cast
    (kind : WithdrawalFutureJoinKind) (reward : Reward ι) (point : ι ⊕ ι → ℚ)
    (hnonneg : ∀ coordinate, 0 ≤ point coordinate)
    (hrows : ∀ row : Bool × {A : Finset ι // A.Nonempty},
      outsideCoefficient reward (some row) ≤
        ∑ coordinate, weightMatrix kind reward (some row) coordinate * point coordinate)
    (pivot i : ι) :
    (correctedWeight kind reward point pivot i : ℝ) =
      (futureJoinCertificateOfRows kind reward point hnonneg hrows).positiveSingletonWeight
        pivot i := by
  unfold correctedWeight WithdrawalFutureJoinRewardCertificate.positiveSingletonWeight
  rw [Rat.cast_add, debtWeight_cast kind reward point hnonneg hrows i]
  congr 1
  split_ifs
  · rw [Rat.cast_div, neverExcess_cast kind reward point hnonneg hrows]
    rfl
  · exact Rat.cast_zero

theorem fullFutureJoinCertificate_excess_eq_zero
    (kind : WithdrawalFutureJoinKind) (reward : Reward ι)
    (hsource : Nonempty (kind.FullCertificate (toReal reward))) :
    (fullFutureJoinCertificate kind reward hsource).neverExcess = 0 := by
  exact max_eq_right (sub_nonpos.mpr (fullFutureJoinCertificate_never kind reward hsource))

theorem full_debtWeight_cast
    (kind : WithdrawalFutureJoinKind) (reward : Reward ι)
    (hsource : Nonempty (kind.FullCertificate (toReal reward))) (i : ι) :
    (debtWeight kind (fullWeights kind reward hsource) i : ℝ) =
      (fullFutureJoinCertificate kind reward hsource).debtWeight i :=
  debtWeight_cast kind reward _ _ _ i

theorem futureJoin_correctedWeight_cast
    (kind : WithdrawalFutureJoinKind) (reward : Reward ι)
    (hsource : Nonempty (WithdrawalFutureJoinRewardCertificate kind (toReal reward)))
    (pivot i : ι) :
    (correctedWeight kind reward (futureJoinWeights kind reward hsource) pivot i : ℝ) =
      (futureJoinCertificate kind reward hsource).positiveSingletonWeight pivot i :=
  correctedWeight_cast kind reward _ _ _ pivot i

end GameTheory.ExecutableWithdrawal
