import UniformEquilibrium.Quitting.Stationary.GuardedCrossedResponseHalfCeilingProducer
import UniformEquilibrium.Quitting.Classification.LCP.NonnegativeInverseRewardApproximation
import UniformEquilibrium.Quitting.Terminal.TerminalExploitabilityRewardRobustness

/-! # Literal reward-table perturbation at the weak four-player half ceiling -/

noncomputable section

namespace GameTheory

open QuittingLCPClassification Math.LinearProgramming Math.LinearAlgebra

/-- Packet Section 6.2: singleton cross rewards fall by `epsilon`, the selected
external pair by `epsilon`, and selected joint-quit rows by `3 * epsilon`. -/
def quittingCrossedWeakHalfPerturb
    (epsilon : ℝ)
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)) :
    {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4) :=
  fun terminal player =>
    if terminal.1.card = 1 ∧ player ∉ terminal.1 then
      reward terminal player - epsilon
    else if (player = 0 ∨ player = 1) ∧ terminal.1 = {2, 3} then
      reward terminal player - epsilon
    else if (player = 0 ∨ player = 1) ∧
        0 ∈ terminal.1 ∧ 1 ∈ terminal.1 then
      reward terminal player - 3 * epsilon
    else reward terminal player

/-- The weak-half strictification stays within `3ε` in every reward coordinate. -/
theorem abs_quittingCrossedWeakHalfPerturb_sub_le
    (epsilon : ℝ) (hepsilon : 0 ≤ epsilon)
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (terminal : {S : Finset (Fin 4) // S.Nonempty}) (player : Fin 4) :
    |quittingCrossedWeakHalfPerturb epsilon reward terminal player -
      reward terminal player| ≤ 3 * epsilon := by
  unfold quittingCrossedWeakHalfPerturb
  split_ifs <;> simp [abs_of_nonneg hepsilon] <;> linarith

/-- The additional nonsingleton changes leave the singleton comparison matrix
equal to the shared off-diagonal subtraction `Γ−εK`. -/
theorem quittingSingletonMatrix_weakHalfPerturb
    (epsilon : ℝ)
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)) :
    quittingSingletonMatrix (quittingCrossedWeakHalfPerturb epsilon reward) =
      quittingSingletonMatrix reward - epsilon • offDiagonalOnes (Fin 4) := by
  have hnotPair (owner : Fin 4) :
      ({owner} : Finset (Fin 4)) ≠ {2, 3} := by
    fin_cases owner <;> decide
  ext player owner
  fin_cases player <;> fin_cases owner <;>
    simp [quittingSingletonMatrix, quittingCrossedWeakHalfPerturb,
      offDiagonalOnes, hnotPair] <;> ring_nf

end GameTheory
