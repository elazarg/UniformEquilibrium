import UniformEquilibrium.Quitting.Cycles.CyclicChildJointPhaseSource
import UniformEquilibrium.Quitting.Classification.LCP.ThreeCore.CyclicChildSingletonAdapter
import UniformEquilibrium.Quitting.Classification.LCP.ThreeCore.CyclicChildPassiveInverseExit

/-! # Singleton exits from the actual cyclic-child joint-phase table

The four singleton rows feed the canonical arbitrary-exterior-row adapter.
At the lower pivot endpoint its internally produced homogeneous witness gives
an actual uniform payoff. Away from that endpoint the original matrix is R0;
the high-passive-inverse exit also supplies its original fixed target, including
the weak threshold boundary. The low-degree strategic exit is separate.
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

/-- Literal two-threshold high exit from the one-joint packet. -/
def passiveExitThreshold (data : JointPhaseData) (u v : ℝ) : ℝ :=
  max (1 + data.a * data.c * (1 - u) + data.a * (1 - v))
    (1 + ((1 - u) + data.a * data.b * (1 - v)) / data.b)

theorem passiveExitThreshold_eq (data : JointPhaseData) (u v : ℝ) :
    passiveExitThreshold data u v =
      max (CyclicChildSingleton.passiveThresholdSecond data.a data.c u v)
        (CyclicChildSingleton.passiveThresholdThird data.a data.b u v) := by
  unfold passiveExitThreshold CyclicChildSingleton.passiveThresholdSecond
    CyclicChildSingleton.passiveThresholdThird
  congr 1 <;> ring

theorem exists_uniformPayoff_of_passiveExit {data : JointPhaseData} {u v ξ R : ℝ}
    {reward : Reward} (htable : RawTable data u v ξ R reward) (hv : v < 1)
    (hR : passiveExitThreshold data u v ≤ R) :
    ∃ payoff : Payoff Player, (quittingGame reward).IsUniformEquilibriumPayoff none payoff := by
  apply CyclicChildSingleton.exists_uniformPayoff_of_twoPassiveThresholds htable.singletonRows
    data.a_pos data.b_pos data.c_pos data.gap_pos hv
  rwa [← passiveExitThreshold_eq]

end GameTheory.CyclicChildJointPhase
