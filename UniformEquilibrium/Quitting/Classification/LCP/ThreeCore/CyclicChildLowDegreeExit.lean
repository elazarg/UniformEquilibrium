import MathUE.CyclicChildExteriorDegree
import UniformEquilibrium.Quitting.Classification.LCP.ThreeCore.CyclicChildSingletonAdapter
import UniformEquilibrium.Quitting.Classification.LCP.SingletonDegreeCriterion

/-! # Actual low-degree exit from literal cyclic-child singleton rows

Negative exterior balance determines the canonical degree from the complete
two-root census. The original game's singleton-degree consumer then supplies
one fixed uniform-equilibrium payoff. No root, degree or strategic witness is
an input, and nonsingleton reward entries are unrestricted.
-/

noncomputable section

namespace GameTheory.CyclicChildSingleton

open QuittingLCPClassification Math.LinearProgramming
open _root_.Math.CyclicChildJointPhase

theorem exists_uniformPayoff_of_below_resonance {a b c h₁ h₂ h₃ u v R : ℝ}
    {reward : Reward} (hrows : RawRows a b c h₁ h₂ h₃ u v R reward)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hh₁ : 0 < h₁) (hh₂ : 0 < h₂) (hh₃ : 0 < h₃) (hgap : 0 < gap a b c)
    (hR : R < resonance a b c h₁ h₂ h₃ u v) :
    ∃ payoff : Payoff (Fin 4), (quittingGame reward).IsUniformEquilibriumPayoff none payoff := by
  have hthird := balanceVector_pos ha hb hc hh₁ hh₂ hh₃ hgap 2
  have hnegative :
      ![u - 1, v - 1, R - 1] ⬝ᵥ balanceVector a b c h₁ h₂ h₃ < 0 := by
    rw [exteriorRow_balance u v R hthird.ne']
    exact mul_neg_of_pos_of_neg hthird (sub_neg.mpr hR)
  obtain ⟨hR0, hdegree⟩ := exterior_r0Degree_eq_zero ha hb hc hh₁ hh₂ hh₃ hgap
    ![u - 1, v - 1, R - 1] hnegative
  have hactual : IsR0Matrix (quittingSingletonMatrix reward) := by
    rw [singletonMatrix_eq hrows]
    exact hR0
  apply exists_uniformEquilibriumPayoff_of_r0Degree_ne_one reward hactual
  have hzero : r0Degree (quittingSingletonMatrix reward) hactual = 0 := by
    simpa only [singletonMatrix_eq hrows] using hdegree
  rw [hzero]
  norm_num

end GameTheory.CyclicChildSingleton
