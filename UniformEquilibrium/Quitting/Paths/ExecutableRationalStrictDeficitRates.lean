import MathUE.GeometricMinimumRecurrence
import UniformEquilibrium.Quitting.Paths.ExecutableRationalStrictDeficitStep
import UniformEquilibrium.Quitting.Terminal.PositiveMinimumSemanticDebt

/-! # Executable rational strict-deficit words and rates

One recursive rational word fold stops adding rows at zero debt.  Its positive
steps use the strict-deficit grid root, and the shared capped-minimum recurrence
gives the packet's geometric envelope.  A `Nat.find` over rational debt selects
the first requested accuracy hit; real analysis appears only in its erased
termination proof.
-/

namespace GameTheory

open Filter
open scoped Topology

variable {players : ℕ}

/-- Literal rational words obtained by repeatedly prefixing the executable
strict-deficit auxiliary root, stopping if total debt is zero. -/
def executableRationalStrictDeficitWords
    (reward : RationalQuittingReward players) (gap : ℚ)
    (hdeficit : RationalQuittingFiniteWordStrictSingletonDeficit reward gap)
    (M : ℚ) (hM : 0 < M) (hgap : 0 < gap)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M) :
    ℕ → List (RationalQuittingRoot players)
  | 0 => []
  | time + 1 =>
      let old := executableRationalStrictDeficitWords
        reward gap hdeficit M hM hgap hreward time
      if hdebt : 0 < rationalFiniteSourceDebt reward old then
        rationalQuittingStrictDeficitRoot reward
          (rationalQuittingFiniteWordSemanticPair reward old)
          M gap hM hgap (by
            simpa only [rationalFiniteSourceDebt] using hdebt) :: old
      else old

@[simp] theorem executableRationalStrictDeficitWords_zero
    (reward : RationalQuittingReward players) (gap : ℚ)
    (hdeficit : RationalQuittingFiniteWordStrictSingletonDeficit reward gap)
    (M : ℚ) (hM : 0 < M) (hgap : 0 < gap)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M) :
    executableRationalStrictDeficitWords
      reward gap hdeficit M hM hgap hreward 0 = [] := rfl

@[simp] theorem executableRationalStrictDeficitWords_succ
    (reward : RationalQuittingReward players) (gap : ℚ)
    (hdeficit : RationalQuittingFiniteWordStrictSingletonDeficit reward gap)
    (M : ℚ) (hM : 0 < M) (hgap : 0 < gap)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (time : ℕ) :
    executableRationalStrictDeficitWords
        reward gap hdeficit M hM hgap hreward (time + 1) =
      let old := executableRationalStrictDeficitWords
        reward gap hdeficit M hM hgap hreward time
      if hdebt : 0 < rationalFiniteSourceDebt reward old then
        rationalQuittingStrictDeficitRoot reward
          (rationalQuittingFiniteWordSemanticPair reward old)
          M gap hM hgap hdebt :: old
      else old := rfl

/-- Rational complete-deviation debt along the executable strict-deficit
words. -/
def executableRationalStrictDeficitDebt
    (reward : RationalQuittingReward players) (gap : ℚ)
    (hdeficit : RationalQuittingFiniteWordStrictSingletonDeficit reward gap)
    (M : ℚ) (hM : 0 < M) (hgap : 0 < gap)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (time : ℕ) : ℚ :=
  rationalFiniteSourceDebt reward
    (executableRationalStrictDeficitWords
      reward gap hdeficit M hM hgap hreward time)

theorem executableRationalStrictDeficitDebt_nonneg
    (reward : RationalQuittingReward players) (gap : ℚ)
    (hdeficit : RationalQuittingFiniteWordStrictSingletonDeficit reward gap)
    (M : ℚ) (hM : 0 < M) (hgap : 0 < gap)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (time : ℕ) :
    0 ≤ executableRationalStrictDeficitDebt
      reward gap hdeficit M hM hgap hreward time := by
  simpa only [executableRationalStrictDeficitDebt] using
    rationalFiniteSourceDebt_nonneg reward
      (executableRationalStrictDeficitWords reward gap hdeficit M hM hgap hreward time)

theorem executableRationalStrictDeficitDebt_step_of_pos
    (reward : RationalQuittingReward players) (gap : ℚ)
    (hdeficit : RationalQuittingFiniteWordStrictSingletonDeficit reward gap)
    (M : ℚ) (hM : 0 < M) (hgap : 0 < gap)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (time : ℕ)
    (hpositive : 0 < executableRationalStrictDeficitDebt
      reward gap hdeficit M hM hgap hreward time) :
    executableRationalStrictDeficitDebt
        reward gap hdeficit M hM hgap hreward (time + 1) ≤
      executableRationalStrictDeficitDebt
          reward gap hdeficit M hM hgap hreward time -
        gap / (4 * (4 * M + gap)) *
          min (executableRationalStrictDeficitDebt
            reward gap hdeficit M hM hgap hreward time) (gap / 2) := by
  let old := executableRationalStrictDeficitWords
    reward gap hdeficit M hM hgap hreward time
  have hpositiveOld : 0 < rationalFiniteSourceDebt reward old := by
    simpa only [old, executableRationalStrictDeficitDebt] using hpositive
  unfold executableRationalStrictDeficitDebt
  rw [executableRationalStrictDeficitWords_succ, dif_pos hpositiveOld]
  exact (rationalQuittingStrictDeficitRoot_absorption_and_debt
    reward _ hM hgap hdeficit hreward hpositive).2

theorem executableRationalStrictDeficitDebt_step_of_nonpos
    (reward : RationalQuittingReward players) (gap : ℚ)
    (hdeficit : RationalQuittingFiniteWordStrictSingletonDeficit reward gap)
    (M : ℚ) (hM : 0 < M) (hgap : 0 < gap)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (time : ℕ)
    (hnonpos : ¬ 0 < executableRationalStrictDeficitDebt
      reward gap hdeficit M hM hgap hreward time) :
    executableRationalStrictDeficitDebt
        reward gap hdeficit M hM hgap hreward (time + 1) =
      executableRationalStrictDeficitDebt
        reward gap hdeficit M hM hgap hreward time := by
  let old := executableRationalStrictDeficitWords
    reward gap hdeficit M hM hgap hreward time
  have hnonposOld : ¬ 0 < rationalFiniteSourceDebt reward old := by
    simpa only [old, executableRationalStrictDeficitDebt] using hnonpos
  unfold executableRationalStrictDeficitDebt
  rw [executableRationalStrictDeficitWords_succ, dif_neg hnonposOld]

theorem executableRationalStrictDeficitDebt_antitone
    (reward : RationalQuittingReward players) (gap : ℚ)
    (hdeficit : RationalQuittingFiniteWordStrictSingletonDeficit reward gap)
    (M : ℚ) (hM : 0 < M) (hgap : 0 < gap)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M) :
    Antitone (executableRationalStrictDeficitDebt
      reward gap hdeficit M hM hgap hreward) := by
  apply antitone_nat_of_succ_le
  intro time
  by_cases hpositive : 0 < executableRationalStrictDeficitDebt
      reward gap hdeficit M hM hgap hreward time
  · have hstep := executableRationalStrictDeficitDebt_step_of_pos
      reward gap hdeficit M hM hgap hreward time hpositive
    have hcoefficient : 0 ≤ gap / (4 * (4 * M + gap)) := by positivity
    have hpaid : 0 ≤ min
        (executableRationalStrictDeficitDebt
          reward gap hdeficit M hM hgap hreward time) (gap / 2) :=
      le_min (executableRationalStrictDeficitDebt_nonneg
        reward gap hdeficit M hM hgap hreward time) (by positivity)
    exact hstep.trans (sub_le_self _ (mul_nonneg hcoefficient hpaid))
  · rw [executableRationalStrictDeficitDebt_step_of_nonpos
      reward gap hdeficit M hM hgap hreward time hpositive]

theorem gap_le_executableRationalStrictDeficitDebt_zero
    (reward : RationalQuittingReward players) (gap : ℚ)
    (hdeficit : RationalQuittingFiniteWordStrictSingletonDeficit reward gap)
    (M : ℚ) (hM : 0 < M) (hgap : 0 < gap)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M) :
    gap ≤ executableRationalStrictDeficitDebt
      reward gap hdeficit M hM hgap hreward 0 := by
  obtain ⟨who, hwho⟩ := hdeficit []
  have hsingleton : gap ≤ reward (quittingSingletonTerminal who) who := by
    simpa [rationalQuittingFiniteWordSemanticPair,
      rationalQuittingFiniteWordPayoff] using hwho
  have hcoordinate : gap ≤
      max 0 (reward (quittingSingletonTerminal who) who) :=
    hsingleton.trans (le_max_right _ _)
  unfold executableRationalStrictDeficitDebt rationalFiniteSourceDebt
    rationalQuittingSemanticDebtSum
  simp only [executableRationalStrictDeficitWords_zero,
    rationalQuittingFiniteWordSemanticPair, rationalQuittingFiniteWordPayoff,
    rationalQuittingFiniteWordCap, List.foldr_nil, Pi.zero_apply, sub_zero]
  exact hcoordinate.trans (Finset.single_le_sum
    (fun player _ => le_max_left 0
      (reward (quittingSingletonTerminal player) player))
    (Finset.mem_univ who))

/-- Packet geometric contraction ratio for the rational approximate-root
strict-deficit recurrence. -/
def executableRationalStrictDeficitGeometricRatio
    (M gap initial : ℚ) : ℚ :=
  1 - gap ^ 2 / (8 * initial * (4 * M + gap))

theorem executableRationalStrictDeficitGeometricRatio_nonneg_lt_one
    {M gap initial : ℚ} (hM : 0 < M) (hgap : 0 < gap)
    (hinitial : gap ≤ initial) :
    0 ≤ executableRationalStrictDeficitGeometricRatio M gap initial ∧
      executableRationalStrictDeficitGeometricRatio M gap initial < 1 := by
  have hinitialPos : 0 < initial := hgap.trans_le hinitial
  have hdenom : 0 < 8 * initial * (4 * M + gap) := by positivity
  have hfractionPos : 0 < gap ^ 2 / (8 * initial * (4 * M + gap)) := by
    positivity
  have hfractionLeOne : gap ^ 2 / (8 * initial * (4 * M + gap)) ≤ 1 := by
    apply (div_le_one hdenom).2
    nlinarith [mul_nonneg (sub_nonneg.mpr hinitial)
      (by positivity : 0 ≤ 32 * M + 7 * gap)]
  unfold executableRationalStrictDeficitGeometricRatio
  constructor <;> linarith

/-- The executable rational strict-deficit debts obey the packet's literal
geometric envelope. -/
theorem executableRationalStrictDeficitDebt_geometric
    (reward : RationalQuittingReward players) (gap : ℚ)
    (hdeficit : RationalQuittingFiniteWordStrictSingletonDeficit reward gap)
    (M : ℚ) (hM : 0 < M) (hgap : 0 < gap)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M) :
    let debt := executableRationalStrictDeficitDebt
      reward gap hdeficit M hM hgap hreward
    let initial := debt 0
    let ratio := executableRationalStrictDeficitGeometricRatio M gap initial
    ∀ time, debt time ≤ ratio ^ time * initial := by
  dsimp only
  let debt := executableRationalStrictDeficitDebt
    reward gap hdeficit M hM hgap hreward
  let initial := debt 0
  let ratio := executableRationalStrictDeficitGeometricRatio M gap initial
  have hinitial : gap ≤ initial :=
    gap_le_executableRationalStrictDeficitDebt_zero
      reward gap hdeficit M hM hgap hreward
  have hinitialPos : 0 < initial := hgap.trans_le hinitial
  have hratio : 0 ≤ ratio :=
    (executableRationalStrictDeficitGeometricRatio_nonneg_lt_one
      hM hgap hinitial).1
  have hbound : ∀ time, debt time ≤ initial := by
    intro time
    exact executableRationalStrictDeficitDebt_antitone
      reward gap hdeficit M hM hgap hreward (Nat.zero_le time)
  have hstep : ∀ time, debt (time + 1) ≤ ratio * debt time := by
    intro time
    have hcurrent := executableRationalStrictDeficitDebt_nonneg
      reward gap hdeficit M hM hgap hreward time
    have hscaled := Math.scaled_le_min_of_le_initial hcurrent (hbound time)
      (by positivity : (0 : ℚ) ≤ gap / 2) (by linarith : gap / 2 ≤ initial)
    by_cases hpositive : 0 < debt time
    · have hraw := executableRationalStrictDeficitDebt_step_of_pos
        reward gap hdeficit M hM hgap hreward time hpositive
      have hcoefficient : 0 ≤ gap / (4 * (4 * M + gap)) := by positivity
      have hmul := mul_le_mul_of_nonneg_left hscaled hcoefficient
      have heq : gap / (4 * (4 * M + gap)) *
            (gap / 2 * debt time / initial) =
          gap ^ 2 / (8 * initial * (4 * M + gap)) * debt time := by
        field_simp [hinitialPos.ne']
        ring
      change debt (time + 1) ≤ ratio * debt time
      calc
        debt (time + 1) ≤ debt time - gap / (4 * (4 * M + gap)) *
            min (debt time) (gap / 2) := hraw
        _ ≤ debt time - gap / (4 * (4 * M + gap)) *
            (gap / 2 * debt time / initial) := by linarith
        _ = ratio * debt time := by
          dsimp only [ratio, executableRationalStrictDeficitGeometricRatio]
          rw [heq]
          ring
    · have hzero : debt time = 0 := le_antisymm (le_of_not_gt hpositive) hcurrent
      have hsame := executableRationalStrictDeficitDebt_step_of_nonpos
        reward gap hdeficit M hM hgap hreward time hpositive
      change debt (time + 1) = debt time at hsame
      rw [hsame, hzero, mul_zero]
  exact Math.sequence_le_geometric_of_step debt initial ratio hratio (le_refl _) hstep

/-- The cast rational debts converge to zero.  Only this erased termination
proof uses real geometric convergence. -/
theorem tendsto_executableRationalStrictDeficitDebt_zero
    (reward : RationalQuittingReward players) (gap : ℚ)
    (hdeficit : RationalQuittingFiniteWordStrictSingletonDeficit reward gap)
    (M : ℚ) (hM : 0 < M) (hgap : 0 < gap)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M) :
    Tendsto (fun time => (executableRationalStrictDeficitDebt
      reward gap hdeficit M hM hgap hreward time : ℝ)) atTop (nhds 0) := by
  let debt := executableRationalStrictDeficitDebt
    reward gap hdeficit M hM hgap hreward
  let initial := debt 0
  let ratio := executableRationalStrictDeficitGeometricRatio M gap initial
  have hinitial : gap ≤ initial :=
    gap_le_executableRationalStrictDeficitDebt_zero
      reward gap hdeficit M hM hgap hreward
  have hratio := executableRationalStrictDeficitGeometricRatio_nonneg_lt_one
    hM hgap hinitial
  apply Math.tendsto_zero_of_sequence_le_geometric
    (fun time => (debt time : ℝ)) (initial : ℝ) (ratio : ℝ)
  · intro time
    exact_mod_cast (executableRationalStrictDeficitDebt_nonneg
      reward gap hdeficit M hM hgap hreward time)
  · exact_mod_cast hratio.1
  · exact_mod_cast hratio.2
  · intro time
    have henvelope := executableRationalStrictDeficitDebt_geometric
      reward gap hdeficit M hM hgap hreward time
    exact_mod_cast henvelope

private theorem exists_executableRationalStrictDeficitDebt_lt
    (reward : RationalQuittingReward players) (gap : ℚ)
    (hdeficit : RationalQuittingFiniteWordStrictSingletonDeficit reward gap)
    (M : ℚ) (hM : 0 < M) (hgap : 0 < gap)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (ε : ℚ) (hε : 0 < ε) :
    ∃ time, executableRationalStrictDeficitDebt
      reward gap hdeficit M hM hgap hreward time < ε := by
  have hlimit := tendsto_executableRationalStrictDeficitDebt_zero
    reward gap hdeficit M hM hgap hreward
  have heventually : ∀ᶠ time in atTop,
      (executableRationalStrictDeficitDebt
        reward gap hdeficit M hM hgap hreward time : ℝ) < (ε : ℝ) :=
    (tendsto_order.1 hlimit).2 _ (by exact_mod_cast hε)
  obtain ⟨time, htime⟩ := heventually.exists
  exact ⟨time, by exact_mod_cast htime⟩

/-- Executable first rational phase whose complete debt is below the requested
positive rational accuracy. -/
def executableRationalStrictDeficitFirstPhase
    (reward : RationalQuittingReward players) (gap : ℚ)
    (hdeficit : RationalQuittingFiniteWordStrictSingletonDeficit reward gap)
    (M : ℚ) (hM : 0 < M) (hgap : 0 < gap)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (ε : ℚ) (hε : 0 < ε) : ℕ :=
  Nat.find (exists_executableRationalStrictDeficitDebt_lt
    reward gap hdeficit M hM hgap hreward ε hε)

theorem executableRationalStrictDeficitFirstPhase_spec
    (reward : RationalQuittingReward players) (gap : ℚ)
    (hdeficit : RationalQuittingFiniteWordStrictSingletonDeficit reward gap)
    (M : ℚ) (hM : 0 < M) (hgap : 0 < gap)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (ε : ℚ) (hε : 0 < ε) :
    executableRationalStrictDeficitDebt reward gap hdeficit M hM hgap hreward
        (executableRationalStrictDeficitFirstPhase
          reward gap hdeficit M hM hgap hreward ε hε) < ε :=
  Nat.find_spec (exists_executableRationalStrictDeficitDebt_lt
    reward gap hdeficit M hM hgap hreward ε hε)

theorem executableRationalStrictDeficitWords_length_le
    (reward : RationalQuittingReward players) (gap : ℚ)
    (hdeficit : RationalQuittingFiniteWordStrictSingletonDeficit reward gap)
    (M : ℚ) (hM : 0 < M) (hgap : 0 < gap)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M) :
    ∀ time, (executableRationalStrictDeficitWords
      reward gap hdeficit M hM hgap hreward time).length ≤ time := by
  intro time
  induction time with
  | zero => simp
  | succ time ih =>
      rw [executableRationalStrictDeficitWords_succ]
      dsimp only
      split
      · simp only [List.length_cons]
        omega
      · exact ih.trans (Nat.le_succ time)

/-- The executable first-hit word has rational complete debt below the target,
retains its literal row count, and is approximate Nash against every actual
behavioral terminal deviation for that same word. -/
theorem executableRationalStrictDeficitFirstWord_nash_and_length
    (reward : RationalQuittingReward players) (gap : ℚ)
    (hdeficit : RationalQuittingFiniteWordStrictSingletonDeficit reward gap)
    (M : ℚ) (hM : 0 < M) (hgap : 0 < gap)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (ε : ℚ) (hε : 0 < ε) :
    let phase := executableRationalStrictDeficitFirstPhase
      reward gap hdeficit M hM hgap hreward ε hε
    let roots := executableRationalStrictDeficitWords
      reward gap hdeficit M hM hgap hreward phase
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
  let phase := executableRationalStrictDeficitFirstPhase
    reward gap hdeficit M hM hgap hreward ε hε
  let roots := executableRationalStrictDeficitWords
    reward gap hdeficit M hM hgap hreward phase
  let profile := quittingLiteralRootStackProfile
    (rationalQuittingRewardToReal reward)
    (roots.map RationalQuittingRoot.toPMF)
    (quittingAlwaysContinueProfile (rationalQuittingRewardToReal reward))
  have hdebt := executableRationalStrictDeficitFirstPhase_spec
    reward gap hdeficit M hM hgap hreward ε hε
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
    executableRationalStrictDeficitWords_length_le
      reward gap hdeficit M hM hgap hreward phase⟩

end GameTheory
