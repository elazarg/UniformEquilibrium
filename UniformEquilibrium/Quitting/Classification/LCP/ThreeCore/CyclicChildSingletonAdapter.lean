import MathUE.CyclicChildComplementarity
import UniformEquilibrium.Quitting.Classification.LCP.PunishmentNormalR0
import UniformEquilibrium.Quitting.Classification.LCP.NormalCorePunishmentNormal
import UniformEquilibrium.Quitting.Classification.LCP.ThreeCore.AmbientCarrierElimination

/-! # Actual cyclic-child singleton matrix adapter

Only four literal singleton rows are prescribed. The exterior entries are
arbitrary real numbers, so the same adapter covers both joint-phase families.
The homogeneous resonance exit constructs its witness from the canonical child
inverse and consumes the original game's unrestricted uniform-payoff criterion.
-/

noncomputable section

namespace GameTheory.CyclicChildSingleton

open QuittingLCPClassification Math.LinearProgramming ThreeCoreAmbientCarrierElimination
open _root_.Math.CyclicChildJointPhase

abbrev Reward := {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)

structure RawRows (a b c h₁ h₂ h₃ u v R : ℝ) (reward : Reward) : Prop where
  zero : reward (quittingSingletonTerminal 0) = ![1, -h₁, -h₂, -h₃]
  one : reward (quittingSingletonTerminal 1) = ![u, 0, b, -1]
  two : reward (quittingSingletonTerminal 2) = ![v, -1, 0, c]
  three : reward (quittingSingletonTerminal 3) = ![R, a, -1, 0]

theorem singletonMatrix_eq {a b c h₁ h₂ h₃ u v R : ℝ} {reward : Reward}
    (hrows : RawRows a b c h₁ h₂ h₃ u v R reward) :
    quittingSingletonMatrix reward = exteriorMatrix a b c h₁ h₂ h₃ ![u - 1, v - 1, R - 1] := by
  funext who owner
  change reward (quittingSingletonTerminal owner) who -
    reward (quittingSingletonTerminal who) who = _
  fin_cases who <;> fin_cases owner <;>
    simp [hrows.zero, hrows.one, hrows.two, hrows.three, exteriorMatrix]

def resonance (a b c h₁ h₂ h₃ u v : ℝ) : ℝ :=
  let ν := balanceVector a b c h₁ h₂ h₃
  1 + ((1 - u) * ν 0 + (1 - v) * ν 1) / ν 2

theorem exteriorRow_balance {a b c h₁ h₂ h₃ : ℝ} (u v R : ℝ)
    (hthird : balanceVector a b c h₁ h₂ h₃ 2 ≠ 0) :
    ![u - 1, v - 1, R - 1] ⬝ᵥ balanceVector a b c h₁ h₂ h₃ =
      balanceVector a b c h₁ h₂ h₃ 2 * (R - resonance a b c h₁ h₂ h₃ u v) := by
  simp [dotProduct, Fin.sum_univ_succ, resonance]
  field_simp [hthird]
  ring

theorem isR0_of_ne_resonance {a b c h₁ h₂ h₃ u v R : ℝ} {reward : Reward}
    (hrows : RawRows a b c h₁ h₂ h₃ u v R reward)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hh₁ : 0 < h₁) (hh₂ : 0 < h₂) (hh₃ : 0 < h₃) (hgap : 0 < gap a b c)
    (hR : R ≠ resonance a b c h₁ h₂ h₃ u v) :
    IsR0Matrix (quittingSingletonMatrix reward) := by
  rw [singletonMatrix_eq hrows]
  apply exterior_isR0_of_row_balance_ne_zero hh₁ hh₂ hh₃ hgap.ne'
  rw [exteriorRow_balance u v R
    (balanceVector_pos ha hb hc hh₁ hh₂ hh₃ hgap 2).ne']
  exact mul_ne_zero (balanceVector_pos ha hb hc hh₁ hh₂ hh₃ hgap 2).ne'
    (sub_ne_zero.mpr hR)

theorem exists_uniformPayoff_of_resonance {a b c h₁ h₂ h₃ u v R : ℝ} {reward : Reward}
    (hrows : RawRows a b c h₁ h₂ h₃ u v R reward)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hh₁ : 0 < h₁) (hh₂ : 0 < h₂) (hh₃ : 0 < h₃) (hgap : 0 < gap a b c)
    (hR : R = resonance a b c h₁ h₂ h₃ u v) :
    ∃ payoff : Payoff (Fin 4), (quittingGame reward).IsUniformEquilibriumPayoff none payoff := by
  by_contra hnot
  have hcore := normalCore_eq_univ_of_fourPlayer_not_exists_uniformEquilibriumPayoff
    reward (by norm_num) hnot
  have hnormal := all_punishmentNormal_of_normalCore_eq_univ reward hcore
  have hR0 := isR0Matrix_quittingSingletonMatrix_of_normal_of_no_uniformPayoff
    reward hnormal hnot
  rw [singletonMatrix_eq hrows] at hR0
  apply exterior_not_isR0_of_row_balance_zero hgap.ne'
    (fun who => (balanceVector_pos ha hb hc hh₁ hh₂ hh₃ hgap who).le)
    ![u - 1, v - 1, R - 1] _ hR0
  rw [exteriorRow_balance u v R
    (balanceVector_pos ha hb hc hh₁ hh₂ hh₃ hgap 2).ne', hR, sub_self, mul_zero]

end GameTheory.CyclicChildSingleton
