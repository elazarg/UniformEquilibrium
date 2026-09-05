import UniformEquilibrium.Quitting.Punishment.SinglePivotTailLift
import UniformEquilibrium.Quitting.Punishment.SinglePivotProfileDebtTransport
import MathUE.LinearSqrtGapBound
import UniformEquilibrium.Quitting.Terminal.ExploitabilityGap
import UniformEquilibrium.Quitting.Terminal.TerminalDebtPrefixDescent

/-! # Quantitative preservation of a positive terminal gap -/

noncomputable section

namespace GameTheory

open Filter
open scoped Topology

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Actual lifts at successively smaller positive slack compare a global
original gap to one fixed normalized source, without assuming any infimum is attained. -/
theorem terminalGap_le_singlePivot_linear_sqrt_error
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (pivot : ι)
    (profile : (quittingGame (quittingSinglePivotNormalizedReward reward pivot)).BehaviorProfile)
    {bound gap : ℝ}
    (hreward : ∀ terminal player, |reward terminal player| ≤ bound)
    (hpivot : 0 < quittingSoloReward reward pivot pivot)
    (hnormal : ∀ who, quittingPunishmentValue reward who ≤ quittingSoloReward reward who who) :
    letI : Nonempty ι := ⟨pivot⟩
    (∀ original : (quittingGame reward).BehaviorProfile,
      gap ≤ quittingTerminalExploitability reward original) →
    gap ≤ (quittingSoloReward reward pivot pivot + 2 * bound) *
        quittingTerminalExploitability (quittingSinglePivotNormalizedReward reward pivot) profile +
      2 * bound * Real.sqrt
        (quittingTerminalExploitability
          (quittingSinglePivotNormalizedReward reward pivot) profile) := by
  letI : Nonempty ι := ⟨pivot⟩
  intro hgap
  let error := quittingTerminalExploitability (quittingSinglePivotNormalizedReward reward pivot)
    profile
  let margin : ℕ → ℝ := fun n ↦ 1 / ((n : ℝ) + 1)
  have hmargin : ∀ n, 0 < margin n := by intro n; dsimp [margin]; positivity
  have hmarginLimit : Tendsto margin atTop (nhds 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hrho : Tendsto (fun n ↦ error + margin n) atTop (nhds error) := by
    simpa only [add_zero] using tendsto_const_nhds.add hmarginLimit
  have hlimit : Tendsto (fun n ↦ quittingSoloReward reward pivot pivot * error +
        2 * bound * ((error + margin n) + Real.sqrt (error + margin n)) + margin n)
      atTop (nhds (quittingSoloReward reward pivot pivot * error +
        2 * bound * (error + Real.sqrt error))) := by
    simpa only [add_zero] using
      (tendsto_const_nhds.add ((hrho.add hrho.sqrt).const_mul (2 * bound))).add hmarginLimit
  have hpoint (n : ℕ) : gap ≤ quittingSoloReward reward pivot pivot * error +
      2 * bound * ((error + margin n) + Real.sqrt (error + margin n)) + margin n := by
    have hreach : quittingLiveMassLimit (quittingSinglePivotNormalizedReward reward pivot)
        profile < error + margin n :=
      (quittingLiveMassLimit_singlePivotNormalized_le_exploitability
        reward pivot profile hpivot.ne').trans_lt (lt_add_of_pos_right _ (hmargin n))
    obtain ⟨cutoff, _, root, _, _, herror, _⟩ :=
      exists_singlePivot_samePrefix_terminal_lift reward pivot profile hreward hpivot hnormal
        hreach (hmargin n)
    exact (hgap (quittingStationaryTailSpliceProfile reward profile cutoff root)).trans herror
  have h := ge_of_tendsto hlimit (Eventually.of_forall hpoint)
  dsimp only [error] at h
  nlinarith

/-- The original global exploitability infimum obeys the same quantitative
comparison for each actual normalized profile, including zero source error. -/
theorem quittingTerminalExploitabilityInf_le_singlePivot_error
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (pivot : ι)
    (profile : (quittingGame (quittingSinglePivotNormalizedReward reward pivot)).BehaviorProfile)
    {bound : ℝ}
    (hreward : ∀ terminal player, |reward terminal player| ≤ bound)
    (hpivot : 0 < quittingSoloReward reward pivot pivot)
    (hnormal : ∀ who, quittingPunishmentValue reward who ≤ quittingSoloReward reward who who) :
    letI : Nonempty ι := ⟨pivot⟩
    quittingTerminalExploitabilityInf reward ≤
      (quittingSoloReward reward pivot pivot + 2 * bound) *
          quittingTerminalExploitability
            (quittingSinglePivotNormalizedReward reward pivot) profile +
        2 * bound * Real.sqrt (quittingTerminalExploitability
          (quittingSinglePivotNormalizedReward reward pivot) profile) := by
  letI : Nonempty ι := ⟨pivot⟩
  exact terminalGap_le_singlePivot_linear_sqrt_error reward pivot profile hreward hpivot hnormal
    (quittingTerminalExploitabilityInf_le reward)

/-- A global positive original gap gives the literal quadratic lower bound
for every complete behavioral profile of the normalized game. -/
theorem singlePivot_terminalExploitability_ge_gap_sq_div
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (pivot : ι)
    (profile : (quittingGame (quittingSinglePivotNormalizedReward reward pivot)).BehaviorProfile)
    {bound gap : ℝ}
    (hreward : ∀ terminal player, |reward terminal player| ≤ bound)
    (hpivot : 0 < quittingSoloReward reward pivot pivot)
    (hnormal : ∀ who, quittingPunishmentValue reward who ≤ quittingSoloReward reward who who)
    (hgap : 0 < gap) :
    letI : Nonempty ι := ⟨pivot⟩
    (∀ original : (quittingGame reward).BehaviorProfile,
      gap ≤ quittingTerminalExploitability reward original) →
    gap ^ 2 / (16 * bound ^ 2) ≤
      quittingTerminalExploitability
        (quittingSinglePivotNormalizedReward reward pivot) profile := by
  letI : Nonempty ι := ⟨pivot⟩
  intro hglobal
  have hgapBound : gap ≤ 2 * bound := by
    apply (hglobal (quittingAlwaysContinueProfile reward)).trans
    rw [quittingTerminalExploitability_eq_max_debt]
    apply QuittingBoundaryHolonomy.finitePlayerMax_le
    intro who
    exact quittingTerminalDeviationDebt_le_two_mul_bound reward _ who bound hreward
  exact Math.gap_sq_div_le_of_linear_sqrt_bound
    (quittingSoloReward reward pivot pivot) bound gap _
    (le_of_abs_le (hreward (quittingSingletonTerminal pivot) pivot)) hgap hgapBound
    (quittingTerminalExploitability_nonneg _ profile)
    (terminalGap_le_singlePivot_linear_sqrt_error
      reward pivot profile hreward hpivot hnormal hglobal)

/-- A strict sub-cap margin has a literal profitable behavioral response;
no maximizer of the response supremum is needed. -/
theorem exists_terminalDeviation_of_lt_exploitability [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) {margin : ℝ}
    (hmargin : 0 ≤ margin) (hlt : margin < quittingTerminalExploitability reward profile) :
    ∃ who, ∃ deviation : (quittingGame reward).BehaviorStrategy who,
      quittingTerminalPayoff reward profile who + margin <
        quittingTerminalPayoff reward (Function.update profile who deviation) who := by
  by_contra hnot
  push Not at hnot
  have hnash : (quittingGame reward).IsεAsymptoticNash
      (quittingTerminalPayoff reward) margin profile := hnot
  exact (not_le_of_gt hlt)
    (quittingTerminalExploitability_le_of_isεAsymptoticNash reward profile hmargin hnash)

/-- Half the quadratic cap floor is a genuine actual-deviation gap on every
normalized profile. This is a witness-producing conclusion, not cap attainment. -/
theorem hasTerminalExploitabilityGap_singlePivotNormalized
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (pivot : ι)
    {bound gap : ℝ}
    (hreward : ∀ terminal player, |reward terminal player| ≤ bound)
    (hpivot : 0 < quittingSoloReward reward pivot pivot)
    (hnormal : ∀ who, quittingPunishmentValue reward who ≤ quittingSoloReward reward who who)
    (hgap : 0 < gap) :
    letI : Nonempty ι := ⟨pivot⟩
    (∀ original : (quittingGame reward).BehaviorProfile,
      gap ≤ quittingTerminalExploitability reward original) →
    HasTerminalExploitabilityGap (quittingSinglePivotNormalizedReward reward pivot)
      (gap ^ 2 / (32 * bound ^ 2)) := by
  letI : Nonempty ι := ⟨pivot⟩
  intro hglobal
  have hbound : 0 < bound := hpivot.trans_le
    (le_of_abs_le (hreward (quittingSingletonTerminal pivot) pivot))
  have hpositive : 0 < gap ^ 2 / (32 * bound ^ 2) := by positivity
  have hstrict : gap ^ 2 / (32 * bound ^ 2) < gap ^ 2 / (16 * bound ^ 2) := by
    have heq : gap ^ 2 / (16 * bound ^ 2) = 2 * (gap ^ 2 / (32 * bound ^ 2)) := by ring
    rw [heq]
    linarith
  intro profile
  obtain ⟨who, deviation, hdeviation⟩ := exists_terminalDeviation_of_lt_exploitability
    (quittingSinglePivotNormalizedReward reward pivot) profile hpositive.le
    (hstrict.trans_le (singlePivot_terminalExploitability_ge_gap_sq_div
      reward pivot profile hreward hpivot hnormal hgap hglobal))
  exact ⟨who, deviation, hdeviation.le⟩

end GameTheory
