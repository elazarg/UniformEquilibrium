import MathUE.LinearProgramming.RowSwapR0Restriction
import UniformEquilibrium.Quitting.Stationary.GuardedCrossedResponseStrategic

/-!
# The general guarded no-UE matrix restriction

The unswapped singleton matrix is R0, selected reciprocal entries are
positive, and both selected external rows are strictly negative. These
literal premises produce crossed R0 independently of inverse positivity.
The actual source guards then force crossed degree one if the original
game has no fixed uniform-equilibrium payoff. This is only a necessary
condition for such a no-UE game; degree one does not imply no UE.
-/

noncomputable section

namespace GameTheory

open Math.LinearProgramming QuittingLCPClassification

variable {n : ℕ}

/-- The packet's actual singleton matrix satisfies the generic row-swap restriction. -/
theorem quittingCrossedSingletonMatrix_isR0_of_reciprocal_pos_external_neg
    (reward : {S : Finset (Fin n) // S.Nonempty} → Payoff (Fin n))
    (first second : Fin n)
    (hR0 : IsR0Matrix (quittingSingletonMatrix reward))
    (hfirst : 0 < quittingSingletonMatrix reward first second)
    (hsecond : 0 < quittingSingletonMatrix reward second first)
    (hexternalFirst : ∀ outside, outside ≠ first → outside ≠ second →
      quittingSingletonMatrix reward first outside < 0)
    (hexternalSecond : ∀ outside, outside ≠ first → outside ≠ second →
      quittingSingletonMatrix reward second outside < 0) :
    IsR0Matrix (quittingCrossedSingletonMatrix reward first second) := by
  apply isR0Matrix_rowSwap_of_zero_diagonal_reciprocal_pos_external_neg
    (quittingSingletonMatrix reward) first second _ hR0 hfirst hsecond
    hexternalFirst hexternalSecond
  intro coordinate
  simp only [quittingSingletonMatrix, sub_self]

/-- In the explicitly specified matrix region, the literal source guards
and absence of any original-game UE target force crossed index one. -/
theorem quittingCrossedSingletonMatrix_degree_eq_one_of_sourceGuards_no_uniformPayoff
    (reward : {S : Finset (Fin n) // S.Nonempty} → Payoff (Fin n))
    (first second : Fin n)
    (height : ℝ) (hheight : 0 < height) (hheightOne : height ≤ 1)
    (hguard : QuittingCrossedSourceGuards reward first second height)
    (hR0 : IsR0Matrix (quittingSingletonMatrix reward))
    (hfirst : 0 < quittingSingletonMatrix reward first second)
    (hsecond : 0 < quittingSingletonMatrix reward second first)
    (hexternalFirst : ∀ outside, outside ≠ first → outside ≠ second →
      quittingSingletonMatrix reward first outside < 0)
    (hexternalSecond : ∀ outside, outside ≠ first → outside ≠ second →
      quittingSingletonMatrix reward second outside < 0)
    (hnoUE : ¬∃ value : Payoff (Fin n),
      (quittingGame reward).IsUniformEquilibriumPayoff none value) :
    ∃ hcrossedR0 : IsR0Matrix (quittingCrossedSingletonMatrix reward first second),
      r0Degree (quittingCrossedSingletonMatrix reward first second) hcrossedR0 = 1 := by
  have hdistinct : first ≠ second := by
    intro hequal
    rw [← hequal] at hfirst
    simp only [quittingSingletonMatrix, sub_self] at hfirst
    exact (lt_irrefl (0 : ℝ)) hfirst
  have hcrossedR0 := quittingCrossedSingletonMatrix_isR0_of_reciprocal_pos_external_neg
    reward first second hR0 hfirst hsecond hexternalFirst hexternalSecond
  refine ⟨hcrossedR0, ?_⟩
  by_contra hdegree
  obtain ⟨_, value, _, _, _, _, _, _, _, _, hUE⟩ :=
    exists_guardedCrossed_stationaryTerminalNash_uniformPayoff_of_sourceGuards
      reward first second hdistinct height hheight hheightOne hguard hfirst hsecond
      hcrossedR0 hdegree
  exact hnoUE ⟨value, hUE⟩

end GameTheory
