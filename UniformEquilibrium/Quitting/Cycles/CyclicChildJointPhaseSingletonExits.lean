import UniformEquilibrium.Quitting.Cycles.CyclicChildJointPhaseSource
import UniformEquilibrium.Quitting.Classification.LCP.ThreeCore.CyclicChildSingletonAdapter

/-! # Singleton exits from the actual cyclic-child joint-phase table

The four singleton rows feed the canonical arbitrary-exterior-row adapter.
At the lower pivot endpoint its internally produced homogeneous witness gives
an actual uniform payoff. Away from that endpoint the original matrix is R0;
the low-degree and high-passive-inverse strategic exits are separate.
-/

noncomputable section

namespace GameTheory.CyclicChildJointPhase

open _root_.Math.CyclicChildJointPhase
open QuittingLCPClassification Math.LinearProgramming

theorem RawTable.singletonRows {data : JointPhaseData} {u v ξ R : ℝ} {reward : Reward}
    (htable : RawTable data u v ξ R reward) :
    CyclicChildSingleton.RawRows data.a data.b data.c data.h₁ data.h₂ data.h₃ u v R reward :=
  ⟨htable.singleton_zero, htable.singleton_one, htable.singleton_two, htable.singleton_three⟩

theorem singletonMatrix_isR0_of_ne_lower {data : JointPhaseData} {u v ξ R : ℝ}
    {reward : Reward} (htable : RawTable data u v ξ R reward)
    (hR : R ≠ data.pivotLower u v) : IsR0Matrix (quittingSingletonMatrix reward) := by
  apply CyclicChildSingleton.isR0_of_ne_resonance htable.singletonRows
    data.a_pos data.b_pos data.c_pos data.h₁_pos data.h₂_pos data.h₃_pos data.gap_pos
  exact hR

theorem exists_uniformPayoff_of_resonance {data : JointPhaseData} {u v ξ R : ℝ}
    {reward : Reward} (htable : RawTable data u v ξ R reward)
    (hR : R = data.pivotLower u v) :
    ∃ payoff : Payoff Player, (quittingGame reward).IsUniformEquilibriumPayoff none payoff := by
  apply CyclicChildSingleton.exists_uniformPayoff_of_resonance htable.singletonRows
    data.a_pos data.b_pos data.c_pos data.h₁_pos data.h₂_pos data.h₃_pos data.gap_pos
  exact hR

end GameTheory.CyclicChildJointPhase
