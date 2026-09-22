import MathUE.LinearProgramming.FiniteSupportDegree
import UniformEquilibrium.Quitting.Classification.LCP.SingletonDegreeCriterion

/-!
# A finite raw singleton-matrix test for uniform equilibrium

A positive test anchor is used only to compute the canonical degree. The
finite principal inverse tests derive full R0 and the entire root inventory.
A support sign sum different from one therefore gives an original-game
uniform-equilibrium payoff. No reward normalization or identification of the
test anchor with a strategic payoff target is assumed.
-/

noncomputable section

namespace GameTheory

open _root_.Math.LinearProgramming QuittingLCPClassification

/-- Exact finite inverse-principal tests on the literal singleton matrix
suffice for an original-game uniform-equilibrium payoff. -/
theorem exists_uniformEquilibriumPayoff_of_finite_support_degree_test
    {n : ℕ} [Nonempty (Fin n)]
    (reward : {S : Finset (Fin n) // S.Nonempty} → Payoff (Fin n))
    (anchor : Fin n → ℝ) (hanchor : ∀ who, 0 < anchor who)
    (hnegative : ∀ column, ∃ row, quittingSingletonMatrix reward row column < 0)
    (hprincipal : ∀ support : Finset (Fin n), 2 ≤ support.card →
      (Matrix.toSquareBlockProp (quittingSingletonMatrix reward)
        (fun who => who ∈ support)).det ≠ 0)
    (hstrict : ∀ support ∈ admissibleLCPSupports (quittingSingletonMatrix reward) anchor
      (principalInverseCandidate (quittingSingletonMatrix reward) anchor),
      ∀ who ∉ support, 0 < lcpResidual (quittingSingletonMatrix reward) (-anchor)
        (principalInverseCandidate (quittingSingletonMatrix reward) anchor support) who)
    (hsum : (∑ support ∈ admissibleLCPSupports (quittingSingletonMatrix reward) anchor
      (principalInverseCandidate (quittingSingletonMatrix reward) anchor),
        (SignType.sign (Matrix.toSquareBlockProp (quittingSingletonMatrix reward)
          (fun who => who ∈ support)).det : ℤ)) ≠ 1) :
    ∃ payoff : Payoff (Fin n),
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff := by
  have hR0 := isR0Matrix_of_negative_columns_of_nonsingular_principals
    (quittingSingletonMatrix reward) hnegative hprincipal
  apply exists_uniformEquilibriumPayoff_of_r0Degree_ne_one reward hR0
  rw [r0Degree_eq_sum_admissible_inverse_supports (quittingSingletonMatrix reward) anchor
    (by intro who; simp only [quittingSingletonMatrix, sub_self]) hanchor
    hnegative hprincipal hstrict]
  exact hsum

end GameTheory
