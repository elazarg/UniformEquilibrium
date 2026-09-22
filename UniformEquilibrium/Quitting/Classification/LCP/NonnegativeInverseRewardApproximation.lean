import MathUE.LinearProgramming.NonnegativeInverseApproximation
import UniformEquilibrium.Quitting.Classification.LCP.QuittingRewardAdapter

/-!
# Reward-table approximation for nonnegative singleton-matrix inverses

This module realizes subtraction of the off-diagonal-ones matrix by changing
exactly the off-own singleton reward coordinates.  The quitting-game skeleton
and every other reward coordinate are unchanged.
-/

noncomputable section

namespace GameTheory
namespace QuittingLCPClassification

open Math.LinearAlgebra Math.LinearProgramming

variable {ι : Type} [DecidableEq ι]

/-- Subtract `epsilon` exactly when the terminal coalition is a singleton not
containing the payoff recipient. -/
def subtractOffOwnSingletonReward
    (epsilon : ℝ) (reward : {S : Finset ι // S.Nonempty} → Payoff ι) :
    {S : Finset ι // S.Nonempty} → Payoff ι :=
  fun terminal player =>
    if terminal.1.card = 1 ∧ player ∉ terminal.1 then
      reward terminal player - epsilon
    else
      reward terminal player

@[simp] theorem subtractOffOwnSingletonReward_ownSingleton
    (epsilon : ℝ) (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (player : ι) :
    subtractOffOwnSingletonReward epsilon reward
        ⟨{player}, Finset.singleton_nonempty player⟩ player =
      reward ⟨{player}, Finset.singleton_nonempty player⟩ player := by
  simp [subtractOffOwnSingletonReward]

theorem subtractOffOwnSingletonReward_offOwnSingleton
    (epsilon : ℝ) (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    {player owner : ι} (hne : player ≠ owner) :
    subtractOffOwnSingletonReward epsilon reward
        ⟨{owner}, Finset.singleton_nonempty owner⟩ player =
      reward ⟨{owner}, Finset.singleton_nonempty owner⟩ player - epsilon := by
  simp [subtractOffOwnSingletonReward, hne]

theorem subtractOffOwnSingletonReward_nonsingleton
    (epsilon : ℝ) (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (terminal : {S : Finset ι // S.Nonempty}) (hcard : terminal.1.card ≠ 1)
    (player : ι) :
    subtractOffOwnSingletonReward epsilon reward terminal player =
      reward terminal player := by
  simp [subtractOffOwnSingletonReward, hcard]

/-- Every reward coordinate moves by at most `|epsilon|`. -/
theorem abs_subtractOffOwnSingletonReward_sub_le
    (epsilon : ℝ) (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (terminal : {S : Finset ι // S.Nonempty}) (player : ι) :
    |subtractOffOwnSingletonReward epsilon reward terminal player -
        reward terminal player| ≤ |epsilon| := by
  simp only [subtractOffOwnSingletonReward]
  split_ifs <;> simp

/-- Literal off-own singleton reward subtraction realizes matrix subtraction
by the off-diagonal-ones matrix. -/
theorem quittingSingletonMatrix_subtractOffOwnSingletonReward
    (epsilon : ℝ) (reward : {S : Finset ι // S.Nonempty} → Payoff ι) :
    quittingSingletonMatrix (subtractOffOwnSingletonReward epsilon reward) =
      quittingSingletonMatrix reward - epsilon • offDiagonalOnes ι := by
  funext player owner
  by_cases heq : player = owner
  · subst owner
    simp [quittingSingletonMatrix, offDiagonalOnes]
  · simp [quittingSingletonMatrix, subtractOffOwnSingletonReward,
      offDiagonalOnes, heq]
    ring

variable [Fintype ι]

/-- A nonnegative inverse of a singleton comparison matrix is approximated by
actual reward tables whose comparison matrices have strictly positive inverses.
One threshold works for every smaller positive perturbation, and determinant
sign is preserved. -/
theorem exists_pos_strictlyPositiveInverse_singletonMatrix_rewardApproximation
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hcard : 3 ≤ Fintype.card ι)
    (hdet : (quittingSingletonMatrix reward).det ≠ 0)
    (hinverse : ∀ i j, 0 ≤ (quittingSingletonMatrix reward)⁻¹ i j) :
    ∃ threshold : ℝ, 0 < threshold ∧ ∀ epsilon : ℝ,
      0 < epsilon → epsilon < threshold →
        HasStrictlyPositiveInverse
          (quittingSingletonMatrix (subtractOffOwnSingletonReward epsilon reward)) ∧
        SignType.sign
            (quittingSingletonMatrix
              (subtractOffOwnSingletonReward epsilon reward)).det =
          SignType.sign (quittingSingletonMatrix reward).det ∧
        (∀ terminal player,
          |subtractOffOwnSingletonReward epsilon reward terminal player -
              reward terminal player| ≤ |epsilon|) := by
  obtain ⟨threshold, hthreshold, hsmall⟩ :=
    exists_pos_strictlyPositiveInverse_sub_offDiagonalOnes
      (quittingSingletonMatrix reward) hcard hdet hinverse
  refine ⟨threshold, hthreshold, ?_⟩
  intro epsilon hepsilon hbound
  obtain ⟨hpositive, hsign, -⟩ := hsmall epsilon hepsilon hbound
  rw [quittingSingletonMatrix_subtractOffOwnSingletonReward]
  exact ⟨hpositive, hsign, abs_subtractOffOwnSingletonReward_sub_le epsilon reward⟩

end QuittingLCPClassification
end GameTheory
