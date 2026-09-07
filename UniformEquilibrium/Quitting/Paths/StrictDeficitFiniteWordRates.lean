import MathUE.GeometricMinimumRecurrence
import UniformEquilibrium.Quitting.Paths.StrictDeficitFiniteWords
import UniformEquilibrium.Quitting.Terminal.PositiveMinimumSemanticDebt
import UniformEquilibrium.Quitting.Terminal.TailCompression.ElementaryCaps
import UniformEquilibrium.Quitting.Terminal.TargetTail.TerminalUniformPayoffSelection

/-! # Geometric convergence and full-response consumption of strict-deficit words -/

noncomputable section

namespace GameTheory

open Filter Math.Probability
open scoped Topology

variable {ι : Type} [Fintype ι] [DecidableEq ι]

def quittingStrictDeficitExactWordDebt
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (gap : ℝ)
    (time : ℕ) : ℝ :=
  quittingTerminalSemanticDebtSum <|
    quittingTerminalSemanticPair reward <|
      quittingLiteralRootStackProfile reward
        (quittingStrictDeficitExactWords reward gap time)
        (quittingAlwaysContinueProfile reward)

theorem quittingStrictDeficitExactWordDebt_nonneg
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (gap : ℝ)
    (time : ℕ) : 0 ≤ quittingStrictDeficitExactWordDebt reward gap time := by
  unfold quittingStrictDeficitExactWordDebt quittingTerminalSemanticDebtSum
  exact Finset.sum_nonneg fun who _ =>
    quittingTerminalDeviationDebt_nonneg reward _ who

theorem quittingStrictDeficitExactWordDebt_step
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    {M gap : ℝ} (hgap : 0 < gap)
    (hreward : ∀ S player, |reward S player| ≤ M)
    (hdeficit : HasQuittingFiniteWordStrictSingletonDeficit reward gap)
    (time : ℕ) :
    quittingStrictDeficitExactWordDebt reward gap (time + 1) ≤
      quittingStrictDeficitExactWordDebt reward gap time -
        gap / (4 * M + gap) *
          min (quittingStrictDeficitExactWordDebt reward gap time) (gap / 2) := by
  have hstep := quittingStrictDeficitExactWords_step
    reward hgap hreward hdeficit time
  unfold quittingStrictDeficitExactWordDebt
  rw [quittingStrictDeficitExactWords_succ]
  exact hstep.2

theorem quittingStrictDeficitExactWordDebt_antitone
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    {M gap : ℝ} (hgap : 0 < gap)
    (hreward : ∀ S player, |reward S player| ≤ M)
    (hdeficit : HasQuittingFiniteWordStrictSingletonDeficit reward gap) :
    Antitone (quittingStrictDeficitExactWordDebt reward gap) := by
  obtain ⟨who, _⟩ := hdeficit []
  have hM := quittingRewardCoordinateBound_nonneg_of_player reward who hreward
  apply antitone_nat_of_succ_le
  intro time
  have hstep := quittingStrictDeficitExactWordDebt_step
    reward hgap hreward hdeficit time
  have hcoefficient : 0 ≤ gap / (4 * M + gap) := by positivity
  have hpaid : 0 ≤ min (quittingStrictDeficitExactWordDebt reward gap time)
      (gap / 2) := le_min
    (quittingStrictDeficitExactWordDebt_nonneg reward gap time) (by positivity)
  nlinarith

theorem gap_le_quittingStrictDeficitExactWordDebt_zero
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    {gap : ℝ}
    (hdeficit : HasQuittingFiniteWordStrictSingletonDeficit reward gap) :
    gap ≤ quittingStrictDeficitExactWordDebt reward gap 0 := by
  obtain ⟨who, hwho⟩ := hdeficit []
  have hsingleton : gap ≤
      reward (quittingSingletonTerminal who) who := by
    change quittingTerminalPayoff reward
      (quittingAlwaysContinueProfile reward) who ≤ _ at hwho
    rw [quittingTerminalPayoff_quittingAlwaysContinue] at hwho
    linarith
  have hcoordinate : gap ≤ quittingTerminalDeviationDebt reward
      (quittingAlwaysContinueProfile reward) who := by
    rw [quittingTerminalDeviationDebt,
      quittingContinuationBestResponseValue_quittingAlwaysContinueProfile,
      quittingTerminalPayoff_quittingAlwaysContinue]
    simpa using hsingleton.trans (le_max_right 0
      (reward (quittingSingletonTerminal who) who))
  have hnonneg : ∀ player, 0 ≤ quittingTerminalDeviationDebt reward
      (quittingAlwaysContinueProfile reward) player :=
    fun player => quittingTerminalDeviationDebt_nonneg reward _ player
  unfold quittingStrictDeficitExactWordDebt quittingTerminalSemanticDebtSum
  simp only [quittingStrictDeficitExactWords, quittingLiteralRootStackProfile]
  exact hcoordinate.trans <|
    Finset.single_le_sum (fun player _ => hnonneg player) (Finset.mem_univ who)

/-- The literal exact words have the geometric total-debt envelope stated by
the strict-deficit construction. -/
theorem quittingStrictDeficitExactWordDebt_geometric
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    {M gap : ℝ} (hgap : 0 < gap)
    (hreward : ∀ S player, |reward S player| ≤ M)
    (hdeficit : HasQuittingFiniteWordStrictSingletonDeficit reward gap) :
    ∀ time,
      quittingStrictDeficitExactWordDebt reward gap time ≤
        (1 - gap ^ 2 /
          (2 * quittingStrictDeficitExactWordDebt reward gap 0 *
            (4 * M + gap))) ^ time *
          quittingStrictDeficitExactWordDebt reward gap 0 := by
  let debt := quittingStrictDeficitExactWordDebt reward gap
  let initial := debt 0
  let ratio := 1 - gap ^ 2 / (2 * initial * (4 * M + gap))
  obtain ⟨who, _⟩ := hdeficit []
  have hM := quittingRewardCoordinateBound_nonneg_of_player reward who hreward
  have hinitial := gap_le_quittingStrictDeficitExactWordDebt_zero reward hdeficit
  have hinitialPos : 0 < initial := hgap.trans_le hinitial
  have hdenom : 0 < 2 * initial * (4 * M + gap) := by positivity
  have hfractionNonneg : 0 ≤ gap ^ 2 /
      (2 * initial * (4 * M + gap)) := by positivity
  have hfractionLeOne : gap ^ 2 /
      (2 * initial * (4 * M + gap)) ≤ 1 := by
    apply (div_le_one hdenom).2
    nlinarith [mul_nonneg (sub_nonneg.mpr hinitial)
      (by positivity : 0 ≤ 8 * M + gap)]
  have hratio : 0 ≤ ratio := by dsimp only [ratio]; linarith
  have hbound : ∀ time, debt time ≤ initial := by
    intro time
    exact quittingStrictDeficitExactWordDebt_antitone
      reward hgap hreward hdeficit (Nat.zero_le time)
  have hstep : ∀ time, debt (time + 1) ≤ ratio * debt time := by
    intro time
    have hcurrent := quittingStrictDeficitExactWordDebt_nonneg reward gap time
    have hmin := Math.scaled_le_min_of_le_initial hcurrent (hbound time)
      (by positivity : 0 ≤ gap / 2) (by linarith : gap / 2 ≤ initial)
    have hraw := quittingStrictDeficitExactWordDebt_step
      reward hgap hreward hdeficit time
    have heq : gap / (4 * M + gap) *
          (gap / 2 * debt time / initial) =
        gap ^ 2 / (2 * initial * (4 * M + gap)) * debt time := by
      field_simp [ne_of_gt hinitialPos, ne_of_gt (by positivity : 0 < 4 * M + gap)]
    have hscaled := mul_le_mul_of_nonneg_left hmin
      (by positivity : 0 ≤ gap / (4 * M + gap))
    change debt (time + 1) ≤ ratio * debt time
    calc
      debt (time + 1) ≤ debt time - gap / (4 * M + gap) *
          min (debt time) (gap / 2) := hraw
      _ ≤ debt time - gap / (4 * M + gap) *
          (gap / 2 * debt time / initial) := by linarith
      _ = ratio * debt time := by
        dsimp only [ratio]
        rw [heq]
        ring
  simpa [debt, initial, ratio] using
    Math.sequence_le_geometric_of_step debt initial ratio hratio (le_refl _) hstep

/-- The debts of the selected literal finite words converge to zero. -/
theorem tendsto_quittingStrictDeficitExactWordDebt_zero
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    {M gap : ℝ} (hgap : 0 < gap)
    (hreward : ∀ S player, |reward S player| ≤ M)
    (hdeficit : HasQuittingFiniteWordStrictSingletonDeficit reward gap) :
    Tendsto (quittingStrictDeficitExactWordDebt reward gap) atTop (nhds 0) := by
  let debt := quittingStrictDeficitExactWordDebt reward gap
  let initial := debt 0
  let ratio := 1 - gap ^ 2 / (2 * initial * (4 * M + gap))
  obtain ⟨who, _⟩ := hdeficit []
  have hM := quittingRewardCoordinateBound_nonneg_of_player reward who hreward
  have hinitial := gap_le_quittingStrictDeficitExactWordDebt_zero reward hdeficit
  have hinitialPos : 0 < initial := hgap.trans_le hinitial
  have hdenom : 0 < 2 * initial * (4 * M + gap) := by positivity
  have hfractionPos : 0 < gap ^ 2 /
      (2 * initial * (4 * M + gap)) := by positivity
  have hfractionLeOne : gap ^ 2 /
      (2 * initial * (4 * M + gap)) ≤ 1 := by
    apply (div_le_one hdenom).2
    nlinarith [mul_nonneg (sub_nonneg.mpr hinitial)
      (by positivity : 0 ≤ 8 * M + gap)]
  have hratioNonneg : 0 ≤ ratio := by dsimp only [ratio]; linarith
  have hratioOne : ratio < 1 := by dsimp only [ratio]; linarith
  apply Math.tendsto_zero_of_sequence_le_geometric debt initial ratio
    (quittingStrictDeficitExactWordDebt_nonneg reward gap)
    hratioNonneg hratioOne
  simpa [debt, initial, ratio] using
    quittingStrictDeficitExactWordDebt_geometric reward hgap hreward hdeficit

/-- Every positive target error is reached by one actual selected finite
word. -/
theorem exists_quittingStrictDeficitExactWordDebt_lt
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    {M gap error : ℝ} (hgap : 0 < gap) (herror : 0 < error)
    (hreward : ∀ S player, |reward S player| ≤ M)
    (hdeficit : HasQuittingFiniteWordStrictSingletonDeficit reward gap) :
    ∃ time, quittingStrictDeficitExactWordDebt reward gap time < error := by
  have hlimit := tendsto_quittingStrictDeficitExactWordDebt_zero
    reward hgap hreward hdeficit
  have heventually : ∀ᶠ time in atTop,
      quittingStrictDeficitExactWordDebt reward gap time < error :=
    (tendsto_order.1 hlimit).2 _ herror
  exact heventually.exists

/-- Strict finite-word exclusion produces an actual finite root word followed
by Never that is Nash against every behavioral deviation up to the requested
terminal error. -/
theorem exists_literalFiniteWord_isEpsilonAsymptoticNash_of_strictDeficit
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    {M gap error : ℝ} (hgap : 0 < gap) (herror : 0 < error)
    (hreward : ∀ S player, |reward S player| ≤ M)
    (hdeficit : HasQuittingFiniteWordStrictSingletonDeficit reward gap) :
    ∃ roots : List (ι → PMF Bool),
      quittingTerminalSemanticDebtSum
          (quittingTerminalSemanticPair reward
            (quittingLiteralRootStackProfile reward roots
              (quittingAlwaysContinueProfile reward))) < error ∧
        (quittingGame reward).IsεAsymptoticNash
          (quittingTerminalPayoff reward) error
          (quittingLiteralRootStackProfile reward roots
            (quittingAlwaysContinueProfile reward)) := by
  obtain ⟨time, htime⟩ := exists_quittingStrictDeficitExactWordDebt_lt
    reward hgap herror hreward hdeficit
  let roots := quittingStrictDeficitExactWords reward gap time
  refine ⟨roots, ?_, ?_⟩
  · exact htime
  · apply isEpsilonAsymptoticNash_of_terminalSemanticDebtSum_le
    exact htime.le

/-- Strict finite-word singleton exclusion is sufficient for existence of one
uniform-equilibrium payoff. -/
theorem exists_uniformEquilibriumPayoff_of_finiteWordStrictSingletonDeficit
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    {gap : ℝ} (hgap : 0 < gap)
    (hdeficit : HasQuittingFiniteWordStrictSingletonDeficit reward gap) :
    ∃ payoff : Payoff ι,
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff := by
  apply (quittingGame_exists_uniformEquilibriumPayoff_iff_terminalNash_all_errors
    reward).2
  intro error herror
  obtain ⟨roots, _, hnash⟩ :=
    exists_literalFiniteWord_isEpsilonAsymptoticNash_of_strictDeficit
      reward hgap herror (abs_reward_le_quittingRewardBound reward) hdeficit
  exact ⟨quittingLiteralRootStackProfile reward roots
    (quittingAlwaysContinueProfile reward), hnash⟩

end GameTheory
