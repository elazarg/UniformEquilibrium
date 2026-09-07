import MathUE.ReciprocalDebtRecurrence
import UniformEquilibrium.Quitting.Paths.GroupExclusionFiniteWords
import UniformEquilibrium.Quitting.Terminal.PositiveMinimumSemanticDebt
import UniformEquilibrium.Quitting.Terminal.TargetTail.TerminalUniformPayoffSelection

/-! # Reciprocal debt decay and uniform payoff from finite-word group exclusion -/

noncomputable section

namespace GameTheory

open Filter Math.Probability
open scoped Topology

variable {ι : Type} [Fintype ι] [DecidableEq ι]

def quittingGroupExclusionExactWordDebt
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (beta : ℝ)
    (time : ℕ) : ℝ :=
  quittingTerminalSemanticDebtSum <|
    quittingTerminalSemanticPair reward <|
      quittingLiteralRootStackProfile reward
        (quittingGroupExclusionExactWords reward beta time)
        (quittingAlwaysContinueProfile reward)

theorem quittingGroupExclusionExactWordDebt_nonneg
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (beta : ℝ) (time : ℕ) :
    0 ≤ quittingGroupExclusionExactWordDebt reward beta time := by
  unfold quittingGroupExclusionExactWordDebt quittingTerminalSemanticDebtSum
  exact Finset.sum_nonneg fun who _ =>
    quittingTerminalDeviationDebt_nonneg reward _ who

theorem quittingGroupExclusionExactWordDebt_step_of_pos
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    {M beta : ℝ} (hbeta : beta < 1)
    (hreward : ∀ S player, |reward S player| ≤ M)
    (hexclusion : HasQuittingFiniteWordNonconcentratedGroupExclusion reward beta)
    (time : ℕ) (hpositive : 0 <
      quittingGroupExclusionExactWordDebt reward beta time) :
    quittingGroupExclusionExactWordDebt reward beta (time + 1) ≤
      quittingGroupExclusionExactWordDebt reward beta time -
        (1 - beta) ^ 2 *
            quittingGroupExclusionExactWordDebt reward beta time ^ 2 /
          (8 * M + 2 * (1 - beta) *
            quittingGroupExclusionExactWordDebt reward beta time) := by
  have hstep := quittingGroupExclusionExactWords_step
    reward hbeta hreward hexclusion time hpositive
  unfold quittingGroupExclusionExactWordDebt
  rw [quittingGroupExclusionExactWords_succ]
  exact hstep

/-- Zero total debt is invariant under the selected exact auxiliary prefix. -/
theorem quittingGroupExclusionExactWordDebt_step_of_eq_zero
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (beta : ℝ) (time : ℕ)
    (hzero : quittingGroupExclusionExactWordDebt reward beta time = 0) :
    quittingGroupExclusionExactWordDebt reward beta (time + 1) = 0 := by
  let old := quittingGroupExclusionExactWords reward beta time
  let profile := quittingLiteralRootStackProfile reward old
    (quittingAlwaysContinueProfile reward)
  let pair := quittingTerminalSemanticPair reward profile
  let root := quittingGroupExclusionSelectedRoot reward pair beta
  have hnash := quittingGroupExclusionSelectedRoot_isZeroNash reward pair beta
  have hauxiliary : quittingGroupExclusionAuxiliary pair beta = pair.2 := by
    funext who
    dsimp [quittingGroupExclusionAuxiliary]
    change quittingTerminalSemanticDebtSum pair = 0 at hzero
    rw [hzero]
    ring
  have hbudget := quittingTerminalSemanticDebtSum_prefix_le_auxiliaryNashDefect
    (reward := reward) pair 0 root (le_refl 0)
  have hdefect :=
    (isZeroQuittingRootNash_iff_totalNashDefect_eq_zero reward pair.2 root).mp
      (by rw [← hauxiliary]; exact hnash)
  have htail : pair.2 - (fun _ => 0) = pair.2 := by
    funext who
    simp
  have hsemantic : quittingTerminalSemanticPair reward
      (quittingLiteralRootStackProfile reward (root :: old)
        (quittingAlwaysContinueProfile reward)) =
      quittingTerminalSemanticPrefix reward root pair := by
    rw [quittingLiteralRootStackProfile_cons,
      quittingTerminalSemanticPair_rootThenContinuation]
  have hnextNonneg := quittingGroupExclusionExactWordDebt_nonneg
    reward beta (time + 1)
  unfold quittingGroupExclusionExactWordDebt at hnextNonneg
  rw [quittingGroupExclusionExactWords_succ, hsemantic] at hnextNonneg
  unfold quittingGroupExclusionExactWordDebt
  rw [quittingGroupExclusionExactWords_succ, hsemantic]
  rw [htail, hdefect, add_zero] at hbudget
  change quittingTerminalSemanticDebtSum pair = 0 at hzero
  rw [hzero] at hbudget
  exact le_antisymm (by simpa using hbudget) hnextNonneg

theorem quittingGroupExclusionExactWordDebt_antitone
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    {M beta : ℝ} (hbeta : beta < 1)
    (hreward : ∀ S player, |reward S player| ≤ M)
    (hexclusion : HasQuittingFiniteWordNonconcentratedGroupExclusion reward beta) :
    Antitone (quittingGroupExclusionExactWordDebt reward beta) := by
  apply antitone_nat_of_succ_le
  intro time
  obtain ⟨weight, _, hsum, _, _⟩ := hexclusion []
  have hsumNe : (∑ who, weight who) ≠ 0 := by rw [hsum]; norm_num
  obtain ⟨who, _, _⟩ := Finset.exists_ne_zero_of_sum_ne_zero hsumNe
  by_cases hpositive : 0 < quittingGroupExclusionExactWordDebt reward beta time
  · have hstep := quittingGroupExclusionExactWordDebt_step_of_pos
      reward hbeta hreward hexclusion time hpositive
    have hM := quittingRewardCoordinateBound_nonneg_of_player reward who hreward
    have hdecrease : 0 ≤ (1 - beta) ^ 2 *
        quittingGroupExclusionExactWordDebt reward beta time ^ 2 /
          (8 * M + 2 * (1 - beta) *
            quittingGroupExclusionExactWordDebt reward beta time) := by positivity
    linarith
  · have hzero : quittingGroupExclusionExactWordDebt reward beta time = 0 :=
      le_antisymm (le_of_not_gt hpositive)
        (quittingGroupExclusionExactWordDebt_nonneg reward beta time)
    rw [hzero, quittingGroupExclusionExactWordDebt_step_of_eq_zero
      reward beta time hzero]

def quittingGroupExclusionReciprocalConstant
    (M beta initial : ℝ) : ℝ :=
  (8 * M + (2 * (1 - beta) - (1 - beta) ^ 2) * initial) /
    (1 - beta) ^ 2

/-- The exact group-exclusion words satisfy an explicit reciprocal debt
rate whenever the initial debt is positive. -/
theorem quittingGroupExclusionExactWordDebt_reciprocal
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    {M beta : ℝ} (hbeta : beta < 1)
    (hreward : ∀ S player, |reward S player| ≤ M)
    (hexclusion : HasQuittingFiniteWordNonconcentratedGroupExclusion reward beta)
    (hinitial : 0 < quittingGroupExclusionExactWordDebt reward beta 0) :
    ∀ time,
      quittingGroupExclusionExactWordDebt reward beta time ≤
        quittingGroupExclusionReciprocalConstant M beta
            (quittingGroupExclusionExactWordDebt reward beta 0) *
          quittingGroupExclusionExactWordDebt reward beta 0 /
        (quittingGroupExclusionReciprocalConstant M beta
            (quittingGroupExclusionExactWordDebt reward beta 0) +
          time * quittingGroupExclusionExactWordDebt reward beta 0) := by
  let debt := quittingGroupExclusionExactWordDebt reward beta
  let initial := debt 0
  let rho := 1 - beta
  obtain ⟨weight, hweight, hsum, hmax, _⟩ := hexclusion []
  have hbetaNonneg : 0 ≤ beta := by
    have hsumNe : (∑ who, weight who) ≠ 0 := by rw [hsum]; norm_num
    obtain ⟨who, _, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hsumNe
    have hpos : 0 < weight who := lt_of_le_of_ne (hweight who) (Ne.symm hne)
    exact hpos.le.trans (hmax who)
  have hrho : 0 < rho := by dsimp only [rho]; linarith
  obtain ⟨who, _⟩ := show ∃ who, 0 < weight who by
    have hsumNe : (∑ who, weight who) ≠ 0 := by rw [hsum]; norm_num
    obtain ⟨who, _, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hsumNe
    exact ⟨who, lt_of_le_of_ne (hweight who) (Ne.symm hne)⟩
  have hM := quittingRewardCoordinateBound_nonneg_of_player reward who hreward
  let base := 8 * M / rho ^ 2
  let slope := 2 / rho
  have hbase : 0 ≤ base := by dsimp only [base]; positivity
  have hslope : 1 ≤ slope := by
    dsimp only [slope, rho]
    apply (le_div_iff₀ hrho).2
    linarith
  have hC : 0 < base + (slope - 1) * initial := by
    have hslopeOne : 1 < slope := by
      dsimp only [slope]
      apply (lt_div_iff₀ hrho).2
      dsimp only [rho]
      linarith
    dsimp only [base]
    positivity
  have hantitone := quittingGroupExclusionExactWordDebt_antitone
    reward hbeta hreward hexclusion
  have hstep : ∀ time, 0 < debt time → debt (time + 1) ≤
      debt time - debt time ^ 2 / (base + slope * debt time) := by
    intro time hpositive
    have hraw := quittingGroupExclusionExactWordDebt_step_of_pos
      reward hbeta hreward hexclusion time hpositive
    have hdenom : 0 < 8 * M + 2 * rho * debt time := by positivity
    have heq : debt time ^ 2 / (base + slope * debt time) =
        rho ^ 2 * debt time ^ 2 / (8 * M + 2 * rho * debt time) := by
      dsimp only [base, slope]
      field_simp [hrho.ne', hdenom.ne']
    simpa [rho, heq] using hraw
  have hrate := Math.sequence_le_reciprocal_of_variable_quadratic_step
    debt base slope initial hbase hslope hinitial hC (le_refl _)
      (quittingGroupExclusionExactWordDebt_nonneg reward beta) hantitone hstep
  have hconstant : base + (slope - 1) * initial =
      quittingGroupExclusionReciprocalConstant M beta initial := by
    dsimp [base, slope, rho, quittingGroupExclusionReciprocalConstant]
    field_simp [show 1 - beta ≠ 0 by linarith]
  simpa [debt, initial, hconstant] using hrate

/-- The debts of the selected literal group-exclusion words converge to zero. -/
theorem tendsto_quittingGroupExclusionExactWordDebt_zero
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    {M beta : ℝ} (hbeta : beta < 1)
    (hreward : ∀ S player, |reward S player| ≤ M)
    (hexclusion : HasQuittingFiniteWordNonconcentratedGroupExclusion reward beta) :
    Tendsto (quittingGroupExclusionExactWordDebt reward beta)
      atTop (nhds 0) := by
  let debt := quittingGroupExclusionExactWordDebt reward beta
  by_cases hinitial : 0 < debt 0
  · let initial := debt 0
    let C := quittingGroupExclusionReciprocalConstant M beta initial
    have hrate := quittingGroupExclusionExactWordDebt_reciprocal
      reward hbeta hreward hexclusion hinitial
    have hC : 0 < C := by
      obtain ⟨weight, hweight, hsum, hmax, _⟩ := hexclusion []
      have hsumNe : (∑ who, weight who) ≠ 0 := by rw [hsum]; norm_num
      obtain ⟨who, _, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hsumNe
      have hpositive : 0 < weight who :=
        lt_of_le_of_ne (hweight who) (Ne.symm hne)
      have hbetaNonneg : 0 ≤ beta := hpositive.le.trans (hmax who)
      have hM := quittingRewardCoordinateBound_nonneg_of_player reward who hreward
      have hrho : 0 < 1 - beta := by linarith
      have hrhoOne : 1 - beta ≤ 1 := by linarith
      have hcoefficient : 0 < 2 * (1 - beta) - (1 - beta) ^ 2 := by
        nlinarith
      dsimp only [C, quittingGroupExclusionReciprocalConstant]
      positivity
    have hdenominator : Tendsto (fun time : ℕ => C + time * initial)
        atTop atTop := by
      exact tendsto_const_nhds.add_atTop
        (tendsto_natCast_atTop_atTop.atTop_mul_const hinitial)
    have hbound : Tendsto (fun time : ℕ => C * initial /
        (C + time * initial)) atTop (nhds 0) :=
      tendsto_const_nhds.div_atTop hdenominator
    apply squeeze_zero'
      (Eventually.of_forall <| quittingGroupExclusionExactWordDebt_nonneg
        reward beta)
      (Eventually.of_forall <| by simpa [debt, initial, C] using hrate)
      hbound
  · have hzero : debt 0 = 0 := le_antisymm (le_of_not_gt hinitial)
      (quittingGroupExclusionExactWordDebt_nonneg reward beta 0)
    have hdebt : debt = fun _ => 0 := by
      funext time
      apply le_antisymm
      · exact (quittingGroupExclusionExactWordDebt_antitone
          reward hbeta hreward hexclusion (Nat.zero_le time)).trans_eq hzero
      · exact quittingGroupExclusionExactWordDebt_nonneg reward beta time
    change Tendsto debt atTop (nhds 0)
    rw [hdebt]
    exact tendsto_const_nhds

/-- Every positive target error is reached by one actual selected finite
group-exclusion word. -/
theorem exists_quittingGroupExclusionExactWordDebt_lt
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    {M beta error : ℝ} (hbeta : beta < 1) (herror : 0 < error)
    (hreward : ∀ S player, |reward S player| ≤ M)
    (hexclusion : HasQuittingFiniteWordNonconcentratedGroupExclusion reward beta) :
    ∃ time, quittingGroupExclusionExactWordDebt reward beta time < error := by
  have hlimit := tendsto_quittingGroupExclusionExactWordDebt_zero
    reward hbeta hreward hexclusion
  exact ((tendsto_order.1 hlimit).2 _ herror).exists

/-- Literal finite-word group exclusion produces a terminal approximate Nash
profile against every behavioral deviation. -/
theorem exists_literalFiniteWord_isEpsilonAsymptoticNash_of_groupExclusion
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    {M beta error : ℝ} (hbeta : beta < 1) (herror : 0 < error)
    (hreward : ∀ S player, |reward S player| ≤ M)
    (hexclusion : HasQuittingFiniteWordNonconcentratedGroupExclusion reward beta) :
    ∃ roots : List (ι → PMF Bool),
      quittingTerminalSemanticDebtSum
          (quittingTerminalSemanticPair reward
            (quittingLiteralRootStackProfile reward roots
              (quittingAlwaysContinueProfile reward))) < error ∧
        (quittingGame reward).IsεAsymptoticNash
          (quittingTerminalPayoff reward) error
          (quittingLiteralRootStackProfile reward roots
            (quittingAlwaysContinueProfile reward)) := by
  obtain ⟨time, htime⟩ := exists_quittingGroupExclusionExactWordDebt_lt
    reward hbeta herror hreward hexclusion
  let roots := quittingGroupExclusionExactWords reward beta time
  refine ⟨roots, htime, ?_⟩
  exact isEpsilonAsymptoticNash_of_terminalSemanticDebtSum_le reward _ htime.le

/-- Finite-word group exclusion is sufficient for existence of one
uniform-equilibrium payoff. -/
theorem exists_uniformEquilibriumPayoff_of_finiteWordGroupExclusion
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    {beta : ℝ} (hbeta : beta < 1)
    (hexclusion : HasQuittingFiniteWordNonconcentratedGroupExclusion reward beta) :
    ∃ payoff : Payoff ι,
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff := by
  apply (quittingGame_exists_uniformEquilibriumPayoff_iff_terminalNash_all_errors
    reward).2
  intro error herror
  obtain ⟨roots, _, hnash⟩ :=
    exists_literalFiniteWord_isEpsilonAsymptoticNash_of_groupExclusion
      reward hbeta herror (abs_reward_le_quittingRewardBound reward) hexclusion
  exact ⟨quittingLiteralRootStackProfile reward roots
    (quittingAlwaysContinueProfile reward), hnash⟩

end GameTheory
