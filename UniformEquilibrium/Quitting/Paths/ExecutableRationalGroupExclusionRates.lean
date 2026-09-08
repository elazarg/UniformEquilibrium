import MathUE.ReciprocalDebtRecurrence
import UniformEquilibrium.Quitting.Paths.ExecutableRationalGroupExclusionStep
import UniformEquilibrium.Quitting.Terminal.PositiveMinimumSemanticDebt

/-! # Executable rational group-exclusion words and reciprocal rate -/

namespace GameTheory

variable {players : ℕ}

/-- Literal rational words obtained by prefixing group-exclusion grid roots,
with a zero-debt stopping branch before any positive-accuracy division. -/
def executableRationalGroupExclusionWords
    (reward : RationalQuittingReward players) (beta M : ℚ)
    (hM : 0 < M) (hbeta : beta < 1) :
    ℕ → List (RationalQuittingRoot players)
  | 0 => []
  | time + 1 =>
      let old := executableRationalGroupExclusionWords reward beta M hM hbeta time
      if hdebt : 0 < rationalFiniteSourceDebt reward old then
        rationalQuittingGroupExclusionRoot reward
          (rationalQuittingFiniteWordSemanticPair reward old)
          M beta hM hbeta (by
            simpa only [rationalFiniteSourceDebt] using hdebt) :: old
      else old

@[simp] theorem executableRationalGroupExclusionWords_zero
    (reward : RationalQuittingReward players) (beta M : ℚ)
    (hM : 0 < M) (hbeta : beta < 1) :
    executableRationalGroupExclusionWords reward beta M hM hbeta 0 = [] := rfl

@[simp] theorem executableRationalGroupExclusionWords_succ
    (reward : RationalQuittingReward players) (beta M : ℚ)
    (hM : 0 < M) (hbeta : beta < 1) (time : ℕ) :
    executableRationalGroupExclusionWords reward beta M hM hbeta (time + 1) =
      let old := executableRationalGroupExclusionWords reward beta M hM hbeta time
      if hdebt : 0 < rationalFiniteSourceDebt reward old then
        rationalQuittingGroupExclusionRoot reward
          (rationalQuittingFiniteWordSemanticPair reward old)
          M beta hM hbeta hdebt :: old
      else old := rfl

/-- Rational complete-deviation debt along the executable group-exclusion
words. -/
def executableRationalGroupExclusionDebt
    (reward : RationalQuittingReward players) (beta M : ℚ)
    (hM : 0 < M) (hbeta : beta < 1) (time : ℕ) : ℚ :=
  rationalFiniteSourceDebt reward
    (executableRationalGroupExclusionWords reward beta M hM hbeta time)

theorem executableRationalGroupExclusionDebt_nonneg
    (reward : RationalQuittingReward players) (beta M : ℚ)
    (hM : 0 < M) (hbeta : beta < 1) (time : ℕ) :
    0 ≤ executableRationalGroupExclusionDebt
      reward beta M hM hbeta time := by
  exact rationalFiniteSourceDebt_nonneg reward _

theorem executableRationalGroupExclusionDebt_step_of_pos
    (reward : RationalQuittingReward players) (beta M : ℚ)
    (hM : 0 < M) (hbeta : beta < 1)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hexclusion : HasQuittingFiniteWordNonconcentratedGroupExclusion
      (rationalQuittingRewardToReal reward) (beta : ℝ))
    (time : ℕ)
    (hpositive : 0 < executableRationalGroupExclusionDebt
      reward beta M hM hbeta time) :
    executableRationalGroupExclusionDebt reward beta M hM hbeta (time + 1) ≤
      executableRationalGroupExclusionDebt reward beta M hM hbeta time -
        (1 - beta) ^ 2 *
          executableRationalGroupExclusionDebt reward beta M hM hbeta time ^ 2 /
          (32 * M + 8 * (1 - beta) *
            executableRationalGroupExclusionDebt reward beta M hM hbeta time) := by
  let old := executableRationalGroupExclusionWords reward beta M hM hbeta time
  have hpositiveOld : 0 < rationalFiniteSourceDebt reward old := by
    simpa only [old, executableRationalGroupExclusionDebt] using hpositive
  unfold executableRationalGroupExclusionDebt
  rw [executableRationalGroupExclusionWords_succ, dif_pos hpositiveOld]
  exact (rationalQuittingGroupExclusionRoot_absorption_and_debt
    reward old hM hbeta hreward hexclusion hpositiveOld).2

theorem executableRationalGroupExclusionDebt_step_of_nonpos
    (reward : RationalQuittingReward players) (beta M : ℚ)
    (hM : 0 < M) (hbeta : beta < 1) (time : ℕ)
    (hnonpos : ¬ 0 < executableRationalGroupExclusionDebt
      reward beta M hM hbeta time) :
    executableRationalGroupExclusionDebt reward beta M hM hbeta (time + 1) =
      executableRationalGroupExclusionDebt reward beta M hM hbeta time := by
  let old := executableRationalGroupExclusionWords reward beta M hM hbeta time
  have hnonposOld : ¬ 0 < rationalFiniteSourceDebt reward old := by
    simpa only [old, executableRationalGroupExclusionDebt] using hnonpos
  unfold executableRationalGroupExclusionDebt
  rw [executableRationalGroupExclusionWords_succ, dif_neg hnonposOld]

theorem executableRationalGroupExclusionDebt_antitone
    (reward : RationalQuittingReward players) (beta M : ℚ)
    (hM : 0 < M) (hbeta : beta < 1)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hexclusion : HasQuittingFiniteWordNonconcentratedGroupExclusion
      (rationalQuittingRewardToReal reward) (beta : ℝ)) :
    Antitone (executableRationalGroupExclusionDebt
      reward beta M hM hbeta) := by
  apply antitone_nat_of_succ_le
  intro time
  by_cases hpositive : 0 < executableRationalGroupExclusionDebt
      reward beta M hM hbeta time
  · have hstep := executableRationalGroupExclusionDebt_step_of_pos
      reward beta M hM hbeta hreward hexclusion time hpositive
    have hdrop : 0 ≤ (1 - beta) ^ 2 *
        executableRationalGroupExclusionDebt reward beta M hM hbeta time ^ 2 /
          (32 * M + 8 * (1 - beta) *
            executableRationalGroupExclusionDebt reward beta M hM hbeta time) := by
      positivity
    exact hstep.trans (sub_le_self _ hdrop)
  · rw [executableRationalGroupExclusionDebt_step_of_nonpos
      reward beta M hM hbeta time hpositive]

/-- Reciprocal-envelope constant for approximate rational group-exclusion
roots. -/
def executableRationalGroupExclusionReciprocalConstant
    (M beta initial : ℚ) : ℚ :=
  (32 * M + (8 * (1 - beta) - (1 - beta) ^ 2) * initial) /
    (1 - beta) ^ 2

private theorem beta_nonneg_of_finiteWordGroupExclusion
    (reward : RationalQuittingReward players) (beta : ℚ)
    (hexclusion : HasQuittingFiniteWordNonconcentratedGroupExclusion
      (rationalQuittingRewardToReal reward) (beta : ℝ)) :
    0 ≤ beta := by
  obtain ⟨weight, hweight, hsum, hmax, _⟩ := hexclusion []
  have hsumNe : (∑ who, weight who) ≠ 0 := by
    rw [hsum]
    norm_num
  obtain ⟨who, _, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hsumNe
  have hpositive : 0 < weight who :=
    lt_of_le_of_ne (hweight who) (Ne.symm hne)
  exact_mod_cast hpositive.le.trans (hmax who)

/-- The executable rational group-exclusion debts satisfy the packet's sharp
reciprocal envelope. -/
theorem executableRationalGroupExclusionDebt_reciprocal
    (reward : RationalQuittingReward players) (beta M : ℚ)
    (hM : 0 < M) (hbeta : beta < 1)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hexclusion : HasQuittingFiniteWordNonconcentratedGroupExclusion
      (rationalQuittingRewardToReal reward) (beta : ℝ))
    (hinitial : 0 < executableRationalGroupExclusionDebt
      reward beta M hM hbeta 0) :
    ∀ time,
      executableRationalGroupExclusionDebt reward beta M hM hbeta time ≤
        executableRationalGroupExclusionReciprocalConstant M beta
            (executableRationalGroupExclusionDebt reward beta M hM hbeta 0) *
          executableRationalGroupExclusionDebt reward beta M hM hbeta 0 /
        (executableRationalGroupExclusionReciprocalConstant M beta
            (executableRationalGroupExclusionDebt reward beta M hM hbeta 0) +
          time * executableRationalGroupExclusionDebt
            reward beta M hM hbeta 0) := by
  let debt := executableRationalGroupExclusionDebt reward beta M hM hbeta
  let initial := debt 0
  let rho := 1 - beta
  let base := 32 * M / rho ^ 2
  let slope := 8 / rho
  have hbetaNonneg : 0 ≤ beta :=
    beta_nonneg_of_finiteWordGroupExclusion reward beta hexclusion
  have hrho : 0 < rho := by dsimp only [rho]; linarith
  have hbase : 0 ≤ base := by dsimp only [base]; positivity
  have hslope : 1 ≤ slope := by
    dsimp only [slope]
    apply (le_div_iff₀ hrho).2
    dsimp only [rho]
    linarith
  have hC : 0 < base + (slope - 1) * initial := by
    dsimp only [base]
    positivity
  have hstep : ∀ time, 0 < debt time → debt (time + 1) ≤
      debt time - debt time ^ 2 / (base + slope * debt time) := by
    intro time hpositive
    have hraw := executableRationalGroupExclusionDebt_step_of_pos
      reward beta M hM hbeta hreward hexclusion time hpositive
    have hdenom : 0 < 32 * M + 8 * rho * debt time := by positivity
    have heq : debt time ^ 2 / (base + slope * debt time) =
        rho ^ 2 * debt time ^ 2 / (32 * M + 8 * rho * debt time) := by
      dsimp only [base, slope]
      field_simp [hrho.ne', hdenom.ne']
    simpa only [rho, debt, heq] using hraw
  have hrate := Math.sequence_le_reciprocal_of_variable_quadratic_step
    debt base slope initial hbase hslope hinitial hC (le_refl _)
      (executableRationalGroupExclusionDebt_nonneg
        reward beta M hM hbeta)
      (executableRationalGroupExclusionDebt_antitone
        reward beta M hM hbeta hreward hexclusion) hstep
  have hconstant : base + (slope - 1) * initial =
      executableRationalGroupExclusionReciprocalConstant M beta initial := by
    dsimp [base, slope, rho,
      executableRationalGroupExclusionReciprocalConstant]
    field_simp [show 1 - beta ≠ 0 by linarith]
  simpa only [debt, initial, hconstant] using hrate

/-- A positive rational accuracy is reached within the ceiling of the sharp
reciprocal constant divided by that accuracy. -/
theorem exists_executableRationalGroupExclusionDebt_lt
    (reward : RationalQuittingReward players) (beta M : ℚ)
    (hM : 0 < M) (hbeta : beta < 1)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hexclusion : HasQuittingFiniteWordNonconcentratedGroupExclusion
      (rationalQuittingRewardToReal reward) (beta : ℝ))
    (ε : ℚ) (hε : 0 < ε) :
    let initial := executableRationalGroupExclusionDebt
      reward beta M hM hbeta 0
    let C := executableRationalGroupExclusionReciprocalConstant M beta initial
    ∃ time ≤ Nat.ceil (C / ε),
      executableRationalGroupExclusionDebt reward beta M hM hbeta time < ε := by
  dsimp only
  let debt := executableRationalGroupExclusionDebt reward beta M hM hbeta
  let initial := debt 0
  let C := executableRationalGroupExclusionReciprocalConstant M beta initial
  by_cases hinitial : 0 < initial
  · have hrate := executableRationalGroupExclusionDebt_reciprocal
      reward beta M hM hbeta hreward hexclusion hinitial
    have hbetaNonneg : 0 ≤ beta :=
      beta_nonneg_of_finiteWordGroupExclusion reward beta hexclusion
    have hrho : 0 < 1 - beta := by linarith
    have hrhoLeOne : 1 - beta ≤ 1 := by linarith
    have hcoefficient : 0 ≤
        8 * (1 - beta) - (1 - beta) ^ 2 := by nlinarith
    have hC : 0 < C := by
      dsimp only [C, executableRationalGroupExclusionReciprocalConstant]
      apply div_pos
      · nlinarith [mul_nonneg hcoefficient hinitial.le]
      · positivity
    let horizon := Nat.ceil (C / ε)
    have hhorizon : C / ε ≤ (horizon : ℚ) := Nat.le_ceil _
    refine ⟨horizon, le_rfl, ?_⟩
    have hbound := hrate horizon
    have hdenom : 0 < C + (horizon : ℚ) * initial := by positivity
    have htarget : C * initial / (C + (horizon : ℚ) * initial) < ε := by
      apply (div_lt_iff₀ hdenom).2
      have hscaled := mul_le_mul_of_nonneg_right hhorizon hε.le
      field_simp at hscaled
      nlinarith [mul_pos hε hC]
    simpa only [debt, initial, C] using hbound.trans_lt htarget
  · have hzero : initial = 0 := le_antisymm (le_of_not_gt hinitial)
      (executableRationalGroupExclusionDebt_nonneg
        reward beta M hM hbeta 0)
    refine ⟨0, Nat.zero_le _, ?_⟩
    simpa only [debt, initial, hzero] using hε

private theorem exists_executableRationalGroupExclusionDebt_lt_unbounded
    (reward : RationalQuittingReward players) (beta M : ℚ)
    (hM : 0 < M) (hbeta : beta < 1)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hexclusion : HasQuittingFiniteWordNonconcentratedGroupExclusion
      (rationalQuittingRewardToReal reward) (beta : ℝ))
    (ε : ℚ) (hε : 0 < ε) :
    ∃ time, executableRationalGroupExclusionDebt
      reward beta M hM hbeta time < ε := by
  obtain ⟨time, _, htime⟩ := exists_executableRationalGroupExclusionDebt_lt
    reward beta M hM hbeta hreward hexclusion ε hε
  exact ⟨time, htime⟩

/-- Executable first phase whose rational complete debt is below the target. -/
def executableRationalGroupExclusionFirstPhase
    (reward : RationalQuittingReward players) (beta M : ℚ)
    (hM : 0 < M) (hbeta : beta < 1)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hexclusion : HasQuittingFiniteWordNonconcentratedGroupExclusion
      (rationalQuittingRewardToReal reward) (beta : ℝ))
    (ε : ℚ) (hε : 0 < ε) : ℕ :=
  Nat.find (exists_executableRationalGroupExclusionDebt_lt_unbounded
    reward beta M hM hbeta hreward hexclusion ε hε)

theorem executableRationalGroupExclusionFirstPhase_spec
    (reward : RationalQuittingReward players) (beta M : ℚ)
    (hM : 0 < M) (hbeta : beta < 1)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hexclusion : HasQuittingFiniteWordNonconcentratedGroupExclusion
      (rationalQuittingRewardToReal reward) (beta : ℝ))
    (ε : ℚ) (hε : 0 < ε) :
    executableRationalGroupExclusionDebt reward beta M hM hbeta
        (executableRationalGroupExclusionFirstPhase reward beta M hM hbeta
          hreward hexclusion ε hε) < ε :=
  Nat.find_spec (exists_executableRationalGroupExclusionDebt_lt_unbounded
    reward beta M hM hbeta hreward hexclusion ε hε)

theorem executableRationalGroupExclusionFirstPhase_le
    (reward : RationalQuittingReward players) (beta M : ℚ)
    (hM : 0 < M) (hbeta : beta < 1)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hexclusion : HasQuittingFiniteWordNonconcentratedGroupExclusion
      (rationalQuittingRewardToReal reward) (beta : ℝ))
    (ε : ℚ) (hε : 0 < ε) :
    let initial := executableRationalGroupExclusionDebt
      reward beta M hM hbeta 0
    let C := executableRationalGroupExclusionReciprocalConstant M beta initial
    executableRationalGroupExclusionFirstPhase reward beta M hM hbeta
        hreward hexclusion ε hε ≤ Nat.ceil (C / ε) := by
  dsimp only
  obtain ⟨time, htimeBound, htime⟩ :=
    exists_executableRationalGroupExclusionDebt_lt
      reward beta M hM hbeta hreward hexclusion ε hε
  exact (Nat.find_min'
    (exists_executableRationalGroupExclusionDebt_lt_unbounded
      reward beta M hM hbeta hreward hexclusion ε hε) htime).trans htimeBound

theorem executableRationalGroupExclusionWords_length_le
    (reward : RationalQuittingReward players) (beta M : ℚ)
    (hM : 0 < M) (hbeta : beta < 1) :
    ∀ time,
      (executableRationalGroupExclusionWords
        reward beta M hM hbeta time).length ≤ time := by
  intro time
  induction time with
  | zero => simp
  | succ time ih =>
      rw [executableRationalGroupExclusionWords_succ]
      dsimp only
      split
      · simp only [List.length_cons]
        omega
      · exact ih.trans (Nat.le_succ time)

/-- The first-hit rational word retains the same literal source for its debt,
row-count, and actual unrestricted terminal Nash guarantees. -/
theorem executableRationalGroupExclusionFirstWord_nash_and_length
    (reward : RationalQuittingReward players) (beta M : ℚ)
    (hM : 0 < M) (hbeta : beta < 1)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hexclusion : HasQuittingFiniteWordNonconcentratedGroupExclusion
      (rationalQuittingRewardToReal reward) (beta : ℝ))
    (ε : ℚ) (hε : 0 < ε) :
    let phase := executableRationalGroupExclusionFirstPhase
      reward beta M hM hbeta hreward hexclusion ε hε
    let roots := executableRationalGroupExclusionWords
      reward beta M hM hbeta phase
    let profile := quittingLiteralRootStackProfile
      (rationalQuittingRewardToReal reward)
      (roots.map RationalQuittingRoot.toPMF)
      (quittingAlwaysContinueProfile (rationalQuittingRewardToReal reward))
    rationalFiniteSourceDebt reward roots < ε ∧
      quittingTerminalSemanticDebtSum
          (quittingTerminalSemanticPair
            (rationalQuittingRewardToReal reward) profile) < (ε : ℝ) ∧
      (quittingGame (rationalQuittingRewardToReal reward)).IsεAsymptoticNash
        (quittingTerminalPayoff (rationalQuittingRewardToReal reward))
        (ε : ℝ) profile ∧
      roots.length ≤ phase := by
  dsimp only
  let phase := executableRationalGroupExclusionFirstPhase
    reward beta M hM hbeta hreward hexclusion ε hε
  let roots := executableRationalGroupExclusionWords reward beta M hM hbeta phase
  let profile := quittingLiteralRootStackProfile
    (rationalQuittingRewardToReal reward)
    (roots.map RationalQuittingRoot.toPMF)
    (quittingAlwaysContinueProfile (rationalQuittingRewardToReal reward))
  have hdebt := executableRationalGroupExclusionFirstPhase_spec
    reward beta M hM hbeta hreward hexclusion ε hε
  have hactual : quittingTerminalSemanticDebtSum
      (quittingTerminalSemanticPair
        (rationalQuittingRewardToReal reward) profile) < (ε : ℝ) := by
    change quittingTerminalSemanticDebtSum
      (quittingTerminalSemanticPair (rationalQuittingRewardToReal reward)
        (quittingLiteralRootStackProfile (rationalQuittingRewardToReal reward)
          (roots.map RationalQuittingRoot.toPMF)
          (quittingAlwaysContinueProfile
            (rationalQuittingRewardToReal reward)))) < (ε : ℝ)
    rw [quittingTerminalSemanticDebtSum_rationalFiniteWord_eq_cast]
    exact_mod_cast hdebt
  exact ⟨hdebt, hactual,
    isEpsilonAsymptoticNash_of_terminalSemanticDebtSum_le
      (rationalQuittingRewardToReal reward) profile hactual.le,
    executableRationalGroupExclusionWords_length_le
      reward beta M hM hbeta phase⟩

end GameTheory
