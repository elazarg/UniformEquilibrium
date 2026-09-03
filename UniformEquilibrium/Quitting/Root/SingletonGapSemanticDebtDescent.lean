/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Boundary.Repair.FixedTailUniformAbsorption
import UniformEquilibrium.Quitting.Root.TerminalSemanticDebt

/-!
# Semantic-debt descent below a singleton reward

A strict gap between one displayed payoff coordinate and its singleton reward
forces every exact Nash prefix to spend a fixed amount of terminal semantic
debt and to carry a fixed amount of joint absorption.  Both conclusions concern
the same literal product root and the same prefixed semantic pair.

The result consumes a point of the actual terminal-semantic carrier.  It does
not select that point or an exact root, and it does not regenerate a source
family after prefixing.
-/

noncomputable section

namespace GameTheory

open Math.Probability Math.SurvivalWeightedObstruction

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The explicit debt-drop and absorption floors used below are both strictly
positive when the debt floor, singleton gap, and reward bound are positive. -/
theorem singletonGapDebtDrop_and_absorptionFloors_pos
    {M debtFloor gap : ℝ}
    (hM : 0 < M) (hdebtFloor : 0 < debtFloor) (hgap : 0 < gap) :
    0 < min debtFloor
        (min (gap / 2) (gap * debtFloor / (8 * M))) ∧
      0 < min 1 (gap / (8 * M)) := by
  constructor <;> positivity

/-- Quantitative descent of one nonnegative semantic-debt coordinate under
every exact root Nash prefix against the displayed payoff. -/
theorem quittingTerminalSemanticDebt_prefix_le_sub_min_of_singleton_gap
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (pair : QuittingTerminalSemanticPair ι)
    (root : ι → PMF Bool) (who : ι) {M gap : ℝ}
    (hgap : 0 < gap)
    (hreward : ∀ S player, |reward S player| ≤ M)
    (hpayoff : |pair.1 who| ≤ M)
    (hsingleton : gap ≤
      reward (quittingSingletonTerminal who) who - pair.1 who)
    (hdebt : 0 ≤ quittingTerminalSemanticDebt pair who)
    (hnash : IsεQuittingRootNash reward pair.1 0 root) :
    quittingTerminalSemanticDebt
        (quittingTerminalSemanticPrefix reward root pair) who ≤
      quittingTerminalSemanticDebt pair who -
        min
          ((gap / (8 * M)) * quittingTerminalSemanticDebt pair who)
          (gap / 2) := by
  have hM := quittingRewardCoordinateBound_nonneg_of_player reward who hreward
  let debt := quittingTerminalSemanticDebt pair who
  let opponentAbsorption := quittingRootOpponentAbsorptionMass root who
  let opponentContinue := quittingRootOpponentContinueMass root who
  let threshold := gap / (8 * M)
  let premium := quittingRootExercisePremium reward pair.1 root who
  have hsingletonAbs :
      |reward (quittingSingletonTerminal who) who| ≤ M :=
    hreward (quittingSingletonTerminal who) who
  have hgapBound : gap ≤ 2 * M := by
    have hsingletonUpper :=
      (le_abs_self (reward (quittingSingletonTerminal who) who)).trans
        hsingletonAbs
    have hpayoffLower := neg_le_of_abs_le hpayoff
    linarith
  have hMpos : 0 < M := by linarith
  have hthresholdLeOne : threshold ≤ 1 := by
    dsimp [threshold]
    apply (div_le_one (by positivity : 0 < 8 * M)).2
    linarith
  have hopponentContinueLeOne : opponentContinue ≤ 1 :=
    quittingRootOpponentContinueMass_le_one root who
  have hcomplement : opponentContinue = 1 - opponentAbsorption :=
    quittingRootOpponentContinueMass_eq_one_sub_absorptionMass root who
  have hrecursion := quittingTerminalSemanticDebt_prefix_eq_blockAct
    reward pair root who hdebt hnash
  have hmonotone := quittingTerminalSemanticDebt_prefix_le
    reward pair root who hdebt hnash
  have hpremium : gap - 4 * M * opponentAbsorption ≤ premium := by
    simpa [premium, quittingRootExercisePremium] using
      (le_max_right 0
        (quittingRootEndpointDifference reward pair.1 root who)).trans' <|
          quittingRootEndpointDifference_ge_singletonGap_sub_four_mul_of_tail_bound
            reward pair.1 root who hreward hpayoff hsingleton
  by_cases hlarge : threshold ≤ opponentAbsorption
  · have hcontinueBound : opponentContinue ≤ 1 - threshold := by
      rw [hcomplement]
      linarith
    have hscaled : opponentContinue * debt ≤ (1 - threshold) * debt :=
      mul_le_mul_of_nonneg_right hcontinueBound (by simpa [debt] using hdebt)
    have hmin : min (threshold * debt) (gap / 2) ≤ threshold * debt :=
      min_le_left _ _
    change quittingTerminalSemanticDebt
        (quittingTerminalSemanticPrefix reward root pair) who ≤
      debt - min (threshold * debt) (gap / 2)
    have hsurvival : quittingTerminalSemanticDebt
        (quittingTerminalSemanticPrefix reward root pair) who ≤
        opponentContinue * debt := by
      rw [hrecursion]
      exact Block.act_le_survival_mul_debt
        (quittingTerminalSemanticDebtBlock reward pair root who) () hdebt
    linarith
  · have hsmall : opponentAbsorption < threshold := lt_of_not_ge hlarge
    have hdenom : 0 < 8 * M := by positivity
    have hscaledAbsorption : opponentAbsorption * (8 * M) < gap :=
      (lt_div_iff₀ hdenom).mp (by simpa [threshold] using hsmall)
    have hpremiumStrict : gap / 2 < premium := by
      nlinarith
    have hminThreshold : min (threshold * debt) (gap / 2) ≤
        threshold * debt := min_le_left _ _
    have hminGap : min (threshold * debt) (gap / 2) ≤ gap / 2 :=
      min_le_right _ _
    have hthresholdDebtLe : threshold * debt ≤ debt := by
      have hdebtNonneg : 0 ≤ debt := by simpa [debt] using hdebt
      nlinarith
    change quittingTerminalSemanticDebt
        (quittingTerminalSemanticPrefix reward root pair) who ≤
      debt - min (threshold * debt) (gap / 2)
    rw [hrecursion]
    change max 0 (opponentContinue * debt - premium) ≤
      debt - min (threshold * debt) (gap / 2)
    by_cases hnew : opponentContinue * debt ≤ premium
    · rw [max_eq_left (sub_nonpos.mpr hnew)]
      linarith
    · rw [max_eq_right (sub_nonneg.mpr (le_of_not_ge hnew))]
      have hcontinueDebt : opponentContinue * debt ≤ debt :=
        mul_le_of_le_one_left (by simpa [debt] using hdebt)
          hopponentContinueLeOne
      linarith

/-- A strict singleton wall and a fixed debt floor force the same exact root
to spend total semantic debt and to absorb with quantitative lower bounds. -/
theorem quittingTerminalSemanticPrefix_totalDebtDrop_and_absorption_of_singleton_gap
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (pair : QuittingTerminalSemanticPair ι)
    (root : ι → PMF Bool) (who : ι) {M debtFloor gap : ℝ}
    (hdebtNonneg : ∀ player,
      0 ≤ quittingTerminalSemanticDebt pair player)
    (hgap : 0 < gap)
    (hreward : ∀ S player, |reward S player| ≤ M)
    (hpayoff : |pair.1 who| ≤ M)
    (hdebt : debtFloor ≤ quittingTerminalSemanticDebt pair who)
    (hsingleton : pair.1 who ≤
      reward (quittingSingletonTerminal who) who - gap)
    (hnash : IsεQuittingRootNash reward pair.1 0 root) :
    min debtFloor
          (min (gap / 2) (gap * debtFloor / (8 * M))) ≤
        quittingTerminalSemanticDebtSum pair -
          quittingTerminalSemanticDebtSum
            (quittingTerminalSemanticPrefix reward root pair) ∧
      gap / (gap + 2 * M) ≤ quittingRootAbsorptionMass root := by
  have hMpos : 0 < M := by
    have hsingletonAbs := hreward (quittingSingletonTerminal who) who
    have hpayoffLower := neg_le_of_abs_le hpayoff
    have hsingletonUpper :=
      (le_abs_self (reward (quittingSingletonTerminal who) who)).trans
        hsingletonAbs
    linarith
  have hselected :=
    quittingTerminalSemanticDebt_prefix_le_sub_min_of_singleton_gap
      reward pair root who hgap hreward hpayoff (by linarith)
        (hdebtNonneg who) hnash
  have hfixedLeActual : gap * debtFloor / (8 * M) ≤
      (gap / (8 * M)) * quittingTerminalSemanticDebt pair who := by
    rw [show gap * debtFloor / (8 * M) =
      (gap / (8 * M)) * debtFloor by ring]
    exact mul_le_mul_of_nonneg_left hdebt (by positivity)
  have hrequestedLeSelected :
      min debtFloor (min (gap / 2) (gap * debtFloor / (8 * M))) ≤
        min
          ((gap / (8 * M)) * quittingTerminalSemanticDebt pair who)
          (gap / 2) := by
    apply le_min
    · exact (min_le_right debtFloor _).trans
        ((min_le_right (gap / 2) _).trans hfixedLeActual)
    · exact (min_le_right debtFloor _).trans (min_le_left _ _)
  have hcoordinateDrop :
      min debtFloor (min (gap / 2) (gap * debtFloor / (8 * M))) ≤
        quittingTerminalSemanticDebt pair who -
          quittingTerminalSemanticDebt
            (quittingTerminalSemanticPrefix reward root pair) who := by
    linarith
  have hcoordinate : ∀ player,
      quittingTerminalSemanticDebt
          (quittingTerminalSemanticPrefix reward root pair) player ≤
        quittingTerminalSemanticDebt pair player := by
    intro player
    exact quittingTerminalSemanticDebt_prefix_le reward pair root player
      (hdebtNonneg player) hnash
  have hothers :
      ∑ player ∈ Finset.univ.erase who,
          quittingTerminalSemanticDebt
            (quittingTerminalSemanticPrefix reward root pair) player ≤
        ∑ player ∈ Finset.univ.erase who,
          quittingTerminalSemanticDebt pair player :=
    Finset.sum_le_sum fun player _ ↦ hcoordinate player
  constructor
  · unfold quittingTerminalSemanticDebtSum
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ who),
      ← Finset.sum_erase_add _ _ (Finset.mem_univ who)]
    linarith
  · exact gap_div_le_quittingRootAbsorptionMass_of_isZeroEndpointNash
      reward pair.1 root who hgap hreward hsingleton
        ((isZeroQuittingRootEndpointNash_iff_isZeroQuittingRootNash
          reward pair.1 root).2 hnash)

/-- The same root satisfies the coarser denominator-only absorption floor
used when a downstream argument fixes only `M` and the singleton gap. -/
theorem quittingTerminalSemanticPrefix_debtDrop_and_minAbsorption_of_carrier
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (pair : QuittingTerminalSemanticPair ι)
    (root : ι → PMF Bool) (who : ι) {M debtFloor gap : ℝ}
    (hpair : pair ∈ quittingTerminalSemanticCarrier reward)
    (hgap : 0 < gap)
    (hreward : ∀ S player, |reward S player| ≤ M)
    (hpayoff : |pair.1 who| ≤ M)
    (hdebt : debtFloor ≤ quittingTerminalSemanticDebt pair who)
    (hsingleton : pair.1 who ≤
      reward (quittingSingletonTerminal who) who - gap)
    (hnash : IsεQuittingRootNash reward pair.1 0 root) :
    quittingTerminalSemanticPrefix reward root pair ∈
        quittingTerminalSemanticCarrier reward ∧
      min debtFloor
            (min (gap / 2) (gap * debtFloor / (8 * M))) ≤
          quittingTerminalSemanticDebtSum pair -
            quittingTerminalSemanticDebtSum
              (quittingTerminalSemanticPrefix reward root pair) ∧
        min 1 (gap / (8 * M)) ≤ quittingRootAbsorptionMass root := by
  have hstrong :=
    quittingTerminalSemanticPrefix_totalDebtDrop_and_absorption_of_singleton_gap
      reward pair root who
        (quittingTerminalSemanticDebt_nonneg_of_mem_carrier reward hpair)
        hgap hreward hpayoff hdebt hsingleton hnash
  refine ⟨quittingTerminalSemanticPrefix_mem_carrier
    reward root pair hpair, hstrong.1, ?_⟩
  have hgapBound : gap ≤ 2 * M := by
    have hsingletonAbs := hreward (quittingSingletonTerminal who) who
    have hpayoffLower := neg_le_of_abs_le hpayoff
    have hsingletonUpper :=
      (le_abs_self (reward (quittingSingletonTerminal who) who)).trans
        hsingletonAbs
    linarith
  have hMpos : 0 < M := by linarith
  have hdenom : 0 < gap + 2 * M := by positivity
  have hcoarse : gap / (8 * M) ≤ gap / (gap + 2 * M) := by
    apply (div_le_div_iff₀ (by positivity : 0 < 8 * M) hdenom).2
    nlinarith
  exact (min_le_right 1 _).trans (hcoarse.trans hstrong.2)

end GameTheory
