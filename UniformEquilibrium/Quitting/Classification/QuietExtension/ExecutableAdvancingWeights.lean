import MathUE.LinearProgramming.ExecutableRationalSelection
import UniformEquilibrium.Quitting.Classification.QuietExtension.ExecutableWithdrawalCoefficients

/-! # Executable advancing-only raw weights

This special case retains a single weight block; no withdrawal column or
Never relaxation is introduced. All coefficient tests use the actual table.
-/

namespace GameTheory.ExecutableWithdrawal

open scoped BigOperators

variable {ι : Type} [Fintype ι] [DecidableEq ι] [Encodable ι]

omit [Encodable ι] in
theorem advancing_realFeasible (reward : Reward ι)
    (hsource : Nonempty (CappedClockParentRewardCertificate (toReal reward))) :
    ∃ point : ι → ℝ, (∀ i, 0 ≤ point i) ∧
      ∀ row, (outsideCoefficient reward row : ℝ) ≤
        ∑ i, (advanceCoefficient reward row i : ℝ) * point i := by
  obtain ⟨certificate⟩ := hsource
  refine ⟨certificate.weight, certificate.weight_nonneg, ?_⟩
  intro row
  simp only [outsideCoefficient_cast, advanceCoefficient_cast]
  cases row with
  | none =>
      simpa only [withdrawalOutsideCoefficient, withdrawalAdvanceCoefficient, mul_comm] using
        certificate.never_row
  | some row =>
      rcases row with ⟨side, A⟩
      cases side
      · simpa only [withdrawalOutsideCoefficient, withdrawalAdvanceCoefficient, mul_comm] using
          certificate.future_row A.1 A.2
      · simpa only [withdrawalOutsideCoefficient, withdrawalAdvanceCoefficient, mul_comm] using
          certificate.join_row A.1 A.2

def advancingWeights (reward : Reward ι)
    (hsource : Nonempty (CappedClockParentRewardCertificate (toReal reward))) : ι → ℚ :=
  Math.LinearProgramming.selectNonnegativeRationalFeasible
    (advanceCoefficient reward) (outsideCoefficient reward) (advancing_realFeasible reward hsource)

noncomputable def advancingCertificate (reward : Reward ι)
    (hsource : Nonempty (CappedClockParentRewardCertificate (toReal reward))) :
    CappedClockParentRewardCertificate (toReal reward) where
  weight i := (advancingWeights reward hsource i : ℝ)
  weight_nonneg i := Rat.cast_nonneg.mpr
    ((Math.LinearProgramming.selectNonnegativeRationalFeasible_spec _ _ _).1 i)
  never_row := by
    have h := (Math.LinearProgramming.selectNonnegativeRationalFeasible_spec
      (advanceCoefficient reward) (outsideCoefficient reward)
      (advancing_realFeasible reward hsource)).2 none
    have hcast : (outsideCoefficient reward none : ℝ) ≤
        ∑ i, (advanceCoefficient reward none i : ℝ) *
          (advancingWeights reward hsource i : ℝ) := by exact_mod_cast h
    simpa only [outsideCoefficient_cast, advanceCoefficient_cast, withdrawalOutsideCoefficient,
      withdrawalAdvanceCoefficient, mul_comm] using hcast
  future_row A hA := by
    have h := (Math.LinearProgramming.selectNonnegativeRationalFeasible_spec
      (advanceCoefficient reward) (outsideCoefficient reward)
      (advancing_realFeasible reward hsource)).2 (some (false, ⟨A, hA⟩))
    have hcast : (outsideCoefficient reward (some (false, ⟨A, hA⟩)) : ℝ) ≤
        ∑ i, (advanceCoefficient reward (some (false, ⟨A, hA⟩)) i : ℝ) *
          (advancingWeights reward hsource i : ℝ) := by exact_mod_cast h
    simpa only [outsideCoefficient_cast, advanceCoefficient_cast, withdrawalOutsideCoefficient,
      withdrawalAdvanceCoefficient, mul_comm] using hcast
  join_row A hA := by
    have h := (Math.LinearProgramming.selectNonnegativeRationalFeasible_spec
      (advanceCoefficient reward) (outsideCoefficient reward)
      (advancing_realFeasible reward hsource)).2 (some (true, ⟨A, hA⟩))
    have hcast : (outsideCoefficient reward (some (true, ⟨A, hA⟩)) : ℝ) ≤
        ∑ i, (advanceCoefficient reward (some (true, ⟨A, hA⟩)) i : ℝ) *
          (advancingWeights reward hsource i : ℝ) := by exact_mod_cast h
    simpa only [outsideCoefficient_cast, advanceCoefficient_cast, withdrawalOutsideCoefficient,
      withdrawalAdvanceCoefficient, mul_comm] using hcast

end GameTheory.ExecutableWithdrawal
