import UniformEquilibrium.Quitting.Examples.BlockPair.PairedResponseQuotientMatrix
import UniformEquilibrium.Quitting.Stationary.ResponseInvariantQuotientPermutation

/-! # Centered paired rows and their literal response quotient -/

noncomputable section

namespace GameTheory
namespace PairedResponseQuotient

open Math.LinearProgramming QuittingLCPClassification
open FourPlayerPairedSingleton

private def swap : Fin 4 ≃ Fin 4 := Equiv.swap 0 1

/-- A paired raw-table class. Only recipients zero and one are related;
recipients two and three are unconstrained away from the singleton matrix. -/
def IsPairedCenteredCompletion
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)) : Prop :=
  quittingSingletonMatrix reward = pairedSingletonMatrix ∧
    ∀ terminal,
      reward (quittingCoalitionEquiv swap terminal) 1 -
          quittingSoloReward reward 1 1 =
        reward terminal 0 - quittingSoloReward reward 0 0

private theorem paired_displacement_eq
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (hcenter : ∀ terminal,
      reward (quittingCoalitionEquiv swap terminal) 1 -
          quittingSoloReward reward 1 1 =
        reward terminal 0 - quittingSoloReward reward 0 0)
    (point : Fin 3 → ℝ) :
    quittingDiscountedDisplacement reward 0 (quittingBlockLift block point) 0 =
      quittingDiscountedDisplacement reward 0 (quittingBlockLift block point) 1 := by
  let offset := quittingSoloReward reward 1 1 - quittingSoloReward reward 0 0
  have hrow (terminal : {S : Finset (Fin 4) // S.Nonempty}) :
      reward (quittingCoalitionEquiv swap terminal) (swap 0) =
        reward terminal 0 + offset := by
    dsimp only [offset]
    simpa only [swap, Equiv.swap_apply_left] using
      (show reward (quittingCoalitionEquiv swap terminal) 1 =
          reward terminal 0 + offset by
        dsimp only [offset]
        linarith [hcenter terminal])
  have hinvariant (who : Fin 4) :
      quittingBlockLift block point (swap who) = quittingBlockLift block point who := by
    fin_cases who <;>
      simp [quittingBlockLift, block, swap, Equiv.swap_apply_def]
  have h := quittingDiscountedDisplacement_equiv_centered swap
    (quittingBlockLift block point) hinvariant reward 0 offset hrow
  simpa only [swap, Equiv.swap_apply_left] using h.symm

theorem responseInvariant_of_pairedCenteredCompletion
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (hclass : IsPairedCenteredCompletion reward) :
    QuittingResponseInvariantOnUnitCube reward block := by
  intro point _ first second hblock
  have hpair := paired_displacement_eq reward hclass.2 point
  fin_cases first <;> fin_cases second <;>
    simp [block] at hblock ⊢
  · exact hpair
  · exact hpair.symm

/-- Every literal member of the centered paired class has a fixed
uniform-equilibrium payoff, without sign restrictions on any reward entry. -/
theorem exists_uniformEquilibriumPayoff_of_pairedCenteredCompletion
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (hclass : IsPairedCenteredCompletion reward) :
    ∃ payoff, (quittingGame reward).IsUniformEquilibriumPayoff none payoff := by
  have hmatrix := quotientMatrix_eq_of_pairedSingletonMatrix reward hclass.1
  have hR0 : IsR0Matrix
      (quittingResponseQuotientMatrix reward block representative) := by
    rw [hmatrix]
    exact isR0
  have hdegree : r0Degree
      (quittingResponseQuotientMatrix reward block representative) hR0 ≠ 1 := by
    have hdet : (quittingResponseQuotientMatrix reward block representative).det < 0 := by
      rw [hmatrix]
      exact det_neg
    have hinverse (row column : Fin 3) : 0 ≤
        (quittingResponseQuotientMatrix reward block representative)⁻¹ row column := by
      rw [hmatrix]
      exact (inverse_pos row column).le
    rw [r0Degree_eq_sign_det_of_nonnegative_inverse _ hR0 hdet.ne hinverse,
      sign_neg hdet]
    decide
  exact exists_uniformEquilibriumPayoff_finFour_of_responseInvariant_degree_ne_one
    reward block representative block_representative
      (responseInvariant_of_pairedCenteredCompletion reward hclass) hR0 hdegree

end PairedResponseQuotient
end GameTheory
