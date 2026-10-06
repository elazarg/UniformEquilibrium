import UniformEquilibrium.Quitting.Cycles.CyclicChildJointPhaseSource
import UniformEquilibrium.Quitting.Classification.LCP.ThreeCore.CyclicChildSingletonAdapter
import UniformEquilibrium.Quitting.Classification.LCP.ThreeCore.CyclicChildPassiveInverseExit
import UniformEquilibrium.Quitting.Classification.LCP.ThreeCore.CyclicChildLowDegreeExit

/-! # Singleton exits from the actual cyclic-child joint-phase table

The four singleton rows feed the canonical arbitrary-exterior-row adapter.
At the lower pivot endpoint its internally produced homogeneous witness gives
an actual uniform payoff. Away from that endpoint the original matrix is R0;
the low-degree and high-passive-inverse exits also supply original fixed targets,
including the weak threshold boundary. The literal threshold comparisons cover
every real pivot payoff without changing the signed singleton assumptions.
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

theorem exists_uniformPayoff_of_below_lower {data : JointPhaseData} {u v ξ R : ℝ}
    {reward : Reward} (htable : RawTable data u v ξ R reward)
    (hR : R < data.pivotLower u v) :
    ∃ payoff : Payoff Player, (quittingGame reward).IsUniformEquilibriumPayoff none payoff := by
  apply CyclicChildSingleton.exists_uniformPayoff_of_below_resonance htable.singletonRows
    data.a_pos data.b_pos data.c_pos data.h₁_pos data.h₂_pos data.h₃_pos data.gap_pos
  exact hR

theorem passiveExitThreshold_le_pivotUpper (data : JointPhaseData) {u v ξ : ℝ}
    (hξ : 0 ≤ ξ) (hu : u ≤ 1 + ξ) :
    passiveExitThreshold data u v ≤ data.pivotUpper u v ξ := by
  unfold passiveExitThreshold JointPhaseData.pivotUpper
  apply max_le
  · exact le_add_of_nonneg_right (div_nonneg (mul_nonneg hξ data.gap_pos.le) data.b_pos.le)
  · have hthird : ((1 - u) + data.a * data.b * (1 - v)) / data.b ≤
        data.a * data.c * (1 - u) + data.a * (1 - v) +
          ξ * gap data.a data.b data.c / data.b := by
      apply (div_le_iff₀ data.b_pos).mpr
      have hgapterm : 0 ≤ gap data.a data.b data.c * (1 + ξ - u) :=
        mul_nonneg data.gap_pos.le (by linarith)
      have hcancel : ξ * gap data.a data.b data.c / data.b * data.b =
          ξ * gap data.a data.b data.c := div_mul_cancel₀ _ data.b_pos.ne'
      rw [add_mul, add_mul, hcancel]
      dsimp [gap] at hgapterm ⊢
      nlinarith only [hgapterm]
    linarith only [hthird]

theorem pivotLower_lt_passiveExitThreshold (data : JointPhaseData) {u v : ℝ}
    (hv : v < 1) : data.pivotLower u v < passiveExitThreshold data u v := by
  have hν := data.balance_pos
  obtain ⟨hfirst, hsecond, hthird⟩ := balanceVector_balances
    data.a data.b data.c data.h₁ data.h₂ data.h₃ data.gap_pos.ne'
  change data.a * data.balance 2 - data.balance 1 = data.h₁ at hfirst
  change data.b * data.balance 0 - data.balance 2 = data.h₂ at hsecond
  change data.c * data.balance 1 - data.balance 0 = data.h₃ at hthird
  by_cases hu : u ≤ 1
  · apply lt_of_lt_of_le _ (le_max_left _ _)
    unfold JointPhaseData.pivotLower
    rw [add_assoc]
    apply (add_lt_add_iff_left 1).mpr
    apply (div_lt_iff₀ (hν 2)).mpr
    have hpositive : 0 < (data.c * (1 - u) + (1 - v)) * data.h₁ +
        (1 - u) * data.h₃ := by
      have hc := data.c_pos
      have hh₁ := data.h₁_pos
      have hh₃ := data.h₃_pos
      have hσ₁ : 0 ≤ 1 - u := by linarith
      have hσ₂ : 0 < 1 - v := by linarith
      positivity
    have hfirstScaled := congrArg (fun z => (data.c * (1 - u) + (1 - v)) * z) hfirst
    have hthirdScaled := congrArg (fun z => (1 - u) * z) hthird
    nlinarith only [hpositive, hfirstScaled, hthirdScaled]
  · apply lt_of_lt_of_le _ (le_max_right _ _)
    unfold JointPhaseData.pivotLower
    apply (add_lt_add_iff_left 1).mpr
    apply (div_lt_iff₀ (hν 2)).mpr
    rw [div_mul_eq_mul_div]
    apply (lt_div_iff₀ data.b_pos).mpr
    have hpositive : 0 < data.b * (1 - v) * data.h₁ - (1 - u) * data.h₂ := by
      have : 0 < (1 - v) * data.h₁ := mul_pos (by linarith) data.h₁_pos
      have : 0 < data.b * ((1 - v) * data.h₁) := mul_pos data.b_pos this
      have : 0 < -(1 - u) * data.h₂ := mul_pos (by linarith) data.h₂_pos
      nlinarith
    have hfirstScaled := congrArg (fun z => data.b * (1 - v) * z) hfirst
    have hsecondScaled := congrArg (fun z => (1 - u) * z) hsecond
    nlinarith only [hpositive, hfirstScaled, hsecondScaled]

/-- The literal raw one-joint class, for every real pivot singleton payoff. -/
theorem exists_uniformPayoff_all_pivots {data : JointPhaseData} {u v ξ R : ℝ}
    {reward : Reward} (htable : RawTable data u v ξ R reward)
    (hξ : 0 < ξ) (hv : v < 1) (hu : u ≤ 1 + ξ) :
    ∃ payoff : Payoff Player, (quittingGame reward).IsUniformEquilibriumPayoff none payoff := by
  rcases lt_trichotomy R (data.pivotLower u v) with hlow | hequal | hhigh
  · exact exists_uniformPayoff_of_below_lower htable hlow
  · exact exists_uniformPayoff_of_resonance htable hequal
  · by_cases hpassive : passiveExitThreshold data u v ≤ R
    · exact exists_uniformPayoff_of_passiveExit htable hv hpassive
    · obtain ⟨y, _, hpayoff⟩ := exists_uniformPayoff data u v ξ R reward htable hξ hv hu
        ⟨hhigh, (lt_of_not_ge hpassive).trans_le
          (passiveExitThreshold_le_pivotUpper data hξ.le hu)⟩
      exact ⟨valueA data ξ y, hpayoff⟩

end GameTheory.CyclicChildJointPhase
