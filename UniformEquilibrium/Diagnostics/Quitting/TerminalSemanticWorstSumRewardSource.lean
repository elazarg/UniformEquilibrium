import UniformEquilibrium.Quitting.Terminal.TerminalDebtSumRewardGeometry
import UniformEquilibrium.Quitting.Terminal.StrictUnitRewardScale
import UniformEquilibrium.Quitting.Terminal.TailCompression.ElementaryCaps
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticAuxiliaryNashBudget
import Mathlib.Topology.Order.Compact

/-! # A worst reward table for the literal SUM-debt infimum

The unit-cube bound uses an internally obtained global semantic minimum and
the actual all-Never competitor. Compactness then selects a worst table for
the true SUM infimum. Common positive reward scaling supplies a positive
unit-cube source from any positive original SUM infimum.
-/

noncomputable section

namespace GameTheory

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The all-Never profile has exactly the sum of positive singleton rewards as debt. -/
theorem quittingTerminalDebtSum_quittingAlwaysContinueProfile_eq
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) :
    quittingTerminalDebtSum reward (quittingAlwaysContinueProfile reward) =
      ∑ who, max 0 (reward (quittingSingletonTerminal who) who) := by
  unfold quittingTerminalDebtSum quittingTerminalDeviationDebt
  simp only [quittingContinuationBestResponseValue_quittingAlwaysContinueProfile,
    quittingTerminalPayoff_quittingAlwaysContinue, sub_zero]

/-- Every unit-cube table has SUM infimum at most player count divided by count plus one. -/
theorem quittingTerminalDebtSumInf_le_card_div_card_add_one_of_unitReward
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hbound : ∀ terminal who, |reward terminal who| ≤ 1) :
    quittingTerminalDebtSumInf reward ≤
      (Fintype.card ι : ℝ) / ((Fintype.card ι : ℝ) + 1) := by
  classical
  by_cases hpositive : 0 < quittingTerminalDebtSumInf reward
  · obtain ⟨pair, hpair, hminimum⟩ := exists_minimum_quittingTerminalSemanticDebtSum reward
    have heq := quittingTerminalDebtSumInf_eq_terminalSemanticDebtSum_of_minimum
      pair hpair hminimum
    have hpositivePair : 0 < quittingTerminalSemanticDebtSum pair := heq ▸ hpositive
    have hbox := quittingTerminalSemanticCarrier_mem_box reward pair hbound hpair
    have hsingleton : ∀ who,
        reward (quittingSingletonTerminal who) who ≤
          1 - quittingTerminalDebtSumInf reward := by
      intro who
      have hmargin := minimumTerminalSemantic_singletonMargin
        pair hpair hminimum hpositivePair who
      rw [← heq] at hmargin
      have hcap : pair.2 who ≤ 1 := hbox.2.2 who
      linarith
    have hnever := quittingTerminalDebtSumInf_le
      (reward := reward) (quittingAlwaysContinueProfile reward)
    rw [quittingTerminalDebtSum_quittingAlwaysContinueProfile_eq] at hnever
    have hsum : quittingTerminalDebtSumInf reward ≤
        (Fintype.card ι : ℝ) * max 0 (1 - quittingTerminalDebtSumInf reward) := by
      calc
        quittingTerminalDebtSumInf reward ≤
            ∑ who, max 0 (reward (quittingSingletonTerminal who) who) := hnever
        _ ≤ ∑ _who : ι, max 0 (1 - quittingTerminalDebtSumInf reward) :=
          Finset.sum_le_sum fun who _ => max_le_max_left 0 (hsingleton who)
        _ = _ := by simp
    have hltOne : quittingTerminalDebtSumInf reward < 1 := by
      by_contra hnot
      have hsub : 1 - quittingTerminalDebtSumInf reward ≤ 0 := by
        linarith [not_lt.mp hnot]
      rw [max_eq_left hsub, mul_zero] at hsum
      exact (not_le_of_gt hpositive) hsum
    rw [max_eq_right (sub_nonneg.mpr hltOne.le)] at hsum
    apply (le_div_iff₀ (by positivity : 0 < (Fintype.card ι : ℝ) + 1)).mpr
    nlinarith
  · exact (le_of_not_gt hpositive).trans (div_nonneg (Nat.cast_nonneg _)
      (by positivity))

/-- The literal four-player SUM bound is four fifths. -/
theorem quittingTerminalDebtSumInf_le_four_fifths_of_unitReward
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (hbound : ∀ terminal who, |reward terminal who| ≤ 1) :
    quittingTerminalDebtSumInf reward ≤ 4 / 5 := by
  have h := quittingTerminalDebtSumInf_le_card_div_card_add_one_of_unitReward reward hbound
  norm_num at h
  exact h

/-- The whole closed reward cube has a maximizing table for the true SUM infimum. -/
theorem exists_maximum_quittingTerminalDebtSumInf_unitReward :
    ∃ original : {S : Finset ι // S.Nonempty} → Payoff ι,
      (∀ terminal who, |original terminal who| ≤ 1) ∧
      ∀ candidate : {S : Finset ι // S.Nonempty} → Payoff ι,
        (∀ terminal who, |candidate terminal who| ≤ 1) →
          quittingTerminalDebtSumInf candidate ≤ quittingTerminalDebtSumInf original := by
  let Cube := Set.Icc (-1 : {S : Finset ι // S.Nonempty} → Payoff ι) 1
  have hzero : (0 : {S : Finset ι // S.Nonempty} → Payoff ι) ∈ Cube := by
    constructor <;> intro terminal who <;> norm_num
  obtain ⟨original, horiginal, hmaximum⟩ :=
    (isCompact_Icc : IsCompact Cube).exists_isMaxOn ⟨0, hzero⟩
      continuous_quittingTerminalDebtSumInf.continuousOn
  refine ⟨original, ?_, ?_⟩
  · intro terminal who
    exact abs_le.mpr ⟨horiginal.1 terminal who, horiginal.2 terminal who⟩
  · intro candidate hcandidate
    apply hmaximum
    exact ⟨fun terminal who => (abs_le.mp (hcandidate terminal who)).1,
      fun terminal who => (abs_le.mp (hcandidate terminal who)).2⟩

/-- A positive original SUM infimum supplies a positive worst unit-cube table. -/
theorem exists_positive_maximum_quittingTerminalDebtSumInf_unitReward
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hpositive : 0 < quittingTerminalDebtSumInf reward) :
    ∃ original : {S : Finset ι // S.Nonempty} → Payoff ι,
      (∀ terminal who, |original terminal who| ≤ 1) ∧
      0 < quittingTerminalDebtSumInf original ∧
      quittingTerminalDebtSumInf original ≤
        (Fintype.card ι : ℝ) / ((Fintype.card ι : ℝ) + 1) ∧
      ∀ candidate : {S : Finset ι // S.Nonempty} → Payoff ι,
        (∀ terminal who, |candidate terminal who| ≤ 1) →
          quittingTerminalDebtSumInf candidate ≤ quittingTerminalDebtSumInf original := by
  obtain ⟨scale, hscale, hscaledBound⟩ := exists_strictUnit_scaleQuittingReward reward
  have hscaledPositive : 0 < quittingTerminalDebtSumInf
      (scaleQuittingReward scale reward) :=
    (quittingTerminalDebtSumInf_scaleQuittingReward_pos_iff hscale reward).mpr hpositive
  obtain ⟨original, horiginalBound, hmaximum⟩ :=
    exists_maximum_quittingTerminalDebtSumInf_unitReward (ι := ι)
  have hscaledLe := hmaximum (scaleQuittingReward scale reward)
    (fun terminal who => (hscaledBound terminal who).le)
  exact ⟨original, horiginalBound, hscaledPositive.trans_le hscaledLe,
    quittingTerminalDebtSumInf_le_card_div_card_add_one_of_unitReward
      original horiginalBound, hmaximum⟩

/-- Failure of a uniform payoff supplies the actual positive worst SUM source. -/
theorem exists_positive_maximum_sum_source_of_not_uniformPayoff
    [Nonempty ι] (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hnot : ¬∃ target : Payoff ι,
      (quittingGame reward).IsUniformEquilibriumPayoff none target) :
    ∃ original : {S : Finset ι // S.Nonempty} → Payoff ι,
      (∀ terminal who, |original terminal who| ≤ 1) ∧
      0 < quittingTerminalDebtSumInf original ∧
      quittingTerminalDebtSumInf original ≤
        (Fintype.card ι : ℝ) / ((Fintype.card ι : ℝ) + 1) ∧
      ∀ candidate : {S : Finset ι // S.Nonempty} → Payoff ι,
        (∀ terminal who, |candidate terminal who| ≤ 1) →
          quittingTerminalDebtSumInf candidate ≤ quittingTerminalDebtSumInf original := by
  exact exists_positive_maximum_quittingTerminalDebtSumInf_unitReward reward
    (quittingTerminalDebtSumInf_pos_iff_not_exists_uniformEquilibriumPayoff.mpr hnot)

end GameTheory
