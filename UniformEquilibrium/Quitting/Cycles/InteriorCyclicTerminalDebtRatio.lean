/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Cycles.InteriorCyclicDebtEscape
import UniformEquilibrium.Quitting.Terminal.ExploitabilityGap

/-!
# Terminal-debt ratios and sequence-level cyclic escape

The unrestricted deviation estimate has two complementary sequence-level
uses.  If every player-deleted error ratio vanishes, compactness selects one
fixed payoff target and the actual periodic profiles realize it as a uniform-
equilibrium payoff.  Under a fixed positive terminal exploitability gap,
every periodic profile instead has a debtor; finite-label selection and the
same ratio estimate produce a fixed owner with vanishing opponent absorption,
followed by singleton concentration or vanishing total hazard.

These conclusions apply to any supplied family of interior cyclic blocks.
The Brouwer producer of such a block for each positive error is independent.
-/

noncomputable section

namespace GameTheory

open Filter Set StochasticGame
open scoped Topology

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Brouwer's pointwise producer selects a coherent family for any prescribed
positive error and positive-period schedule.  No source profile or carrier
point is supplied to this construction. -/
theorem nonempty_interiorApproximateNashCyclicBlockFamily
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (period : ℕ → ℕ) (error : ℕ → ℝ)
    (herror : ∀ n, 0 < error n) :
    Nonempty (∀ n, InteriorApproximateNashCyclicBlock
      reward (period n) (error n)) := by
  exact ⟨fun n ↦ Classical.choice
    (nonempty_interiorApproximateNashCyclicBlock
      (m := period n) reward (error n) (herror n))⟩

/-- The period-error bound divided by one player's opponent-absorption mass.
This is the literal upper bound on that player's unrestricted terminal debt. -/
def interiorCyclicTerminalDebtRatio
    {m : ℕ} {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {error : ℝ} (block : InteriorApproximateNashCyclicBlock reward m error)
    (who : ι) : ℝ :=
  ((m + 1 : ℕ) : ℝ) * error /
    quittingCyclicOpponentAbsorptionMass block.cycle who

/-- The largest player-deleted terminal-debt ratio in one finite-player
cyclic block. -/
def interiorCyclicMaximumTerminalDebtRatio
    [Nonempty ι]
    {m : ℕ} {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {error : ℝ} (block : InteriorApproximateNashCyclicBlock reward m error) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty fun who ↦
    interiorCyclicTerminalDebtRatio block who

/-- Nonnegative local error makes every player-deleted terminal-debt ratio
nonnegative. -/
theorem InteriorApproximateNashCyclicBlock.terminalDebtRatio_nonneg
    [Nontrivial ι]
    {m : ℕ} {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {error : ℝ} (herror : 0 ≤ error)
    (block : InteriorApproximateNashCyclicBlock reward m error)
    (who : ι) : 0 ≤ interiorCyclicTerminalDebtRatio block who := by
  unfold interiorCyclicTerminalDebtRatio
  exact div_nonneg (mul_nonneg (Nat.cast_nonneg _) herror)
    (block.opponentAbsorptionMass_pos who).le

/-- The existing unrestricted-deviation estimate is exactly the displayed
terminal-debt ratio. -/
theorem InteriorApproximateNashCyclicBlock.terminalDeviationDebt_le_ratio
    [Nontrivial ι]
    {m : ℕ} {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {error : ℝ} (herror : 0 ≤ error)
    (block : InteriorApproximateNashCyclicBlock reward m error)
    (initial : Fin (m + 1)) (who : ι) :
    quittingTerminalDeviationDebt reward
        (quittingCyclicBehaviorProfile reward block.cycle initial) who ≤
      interiorCyclicTerminalDebtRatio block who := by
  simpa [interiorCyclicTerminalDebtRatio,
    quittingCyclicOpponentAbsorptionMass] using
      block.terminalDeviationDebt_le herror initial who

/-- A strict subsequence of actual periodic profiles converging to one fixed
uniform-equilibrium payoff. -/
structure InteriorCyclicUniformPayoffSubsequence
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (period : ℕ → ℕ) (error : ℕ → ℝ)
    (block : ∀ n, InteriorApproximateNashCyclicBlock
      reward (period n) (error n))
    (initial : ∀ n, Fin (period n + 1)) where
  select : ℕ → ℕ
  select_strictMono : StrictMono select
  target : Payoff ι
  value_tendsto : Tendsto (fun n ↦
    (block (select n)).value (initial (select n))) atTop (nhds target)
  terminalDebt_tendsto_zero : ∀ who, Tendsto (fun n ↦
    quittingTerminalDeviationDebt reward
      (quittingCyclicBehaviorProfile reward
        (block (select n)).cycle (initial (select n))) who)
    atTop (nhds 0)
  target_isUniformEquilibriumPayoff :
    (quittingGame reward).IsUniformEquilibriumPayoff none target

/-- If every player-deleted terminal-debt ratio vanishes, compactness selects
one fixed payoff target and the corresponding periodic profiles prove that it
is a uniform-equilibrium payoff.  Periods may vary. -/
theorem nonempty_interiorCyclicUniformPayoffSubsequence_of_ratio_tendsto_zero
    [Nontrivial ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (period : ℕ → ℕ) (error : ℕ → ℝ) (herror : ∀ n, 0 ≤ error n)
    (block : ∀ n, InteriorApproximateNashCyclicBlock
      reward (period n) (error n))
    (initial : ∀ n, Fin (period n + 1))
    (hratio : Tendsto (fun n who ↦
      interiorCyclicTerminalDebtRatio (block n) who) atTop (nhds 0)) :
    Nonempty (InteriorCyclicUniformPayoffSubsequence
      reward period error block initial) := by
  let payoffBox : Set (Payoff ι) :=
    Icc (fun _ ↦ -quittingRewardBound reward)
      (fun _ ↦ quittingRewardBound reward)
  have hcompact : IsCompact payoffBox := isCompact_Icc
  have hvalue : ∀ n, (block n).value (initial n) ∈ payoffBox := by
    intro n
    constructor <;> intro who
    · exact (abs_le.mp ((block n).value_bound (initial n) who)).1
    · exact (abs_le.mp ((block n).value_bound (initial n) who)).2
  obtain ⟨target, _htargetMem, select, hselect, htarget⟩ :=
    hcompact.tendsto_subseq hvalue
  let selectedPeriod : ℕ → ℕ := fun n ↦ period (select n)
  let selectedError : ℕ → ℝ := fun n ↦ error (select n)
  let selectedBlock : ∀ n, InteriorApproximateNashCyclicBlock
      reward (selectedPeriod n) (selectedError n) :=
    fun n ↦ block (select n)
  let selectedInitial : ∀ n, Fin (selectedPeriod n + 1) :=
    fun n ↦ initial (select n)
  have hratioSelected : Tendsto (fun n who ↦
      interiorCyclicTerminalDebtRatio (selectedBlock n) who)
      atTop (nhds 0) :=
    hratio.comp hselect.tendsto_atTop
  have htargetSelected : Tendsto (fun n ↦
      (selectedBlock n).value (selectedInitial n)) atTop (nhds target) := by
    change Tendsto ((fun n ↦ (block n).value (initial n)) ∘ select)
      atTop (nhds target)
    exact htarget
  have hdebtSelected : ∀ who, Tendsto (fun n ↦
      quittingTerminalDeviationDebt reward
        (quittingCyclicBehaviorProfile reward
          (selectedBlock n).cycle (selectedInitial n)) who)
      atTop (nhds 0) := by
    intro who
    apply squeeze_zero
    · exact fun n ↦ quittingTerminalDeviationDebt_nonneg reward _ who
    · exact fun n ↦ (selectedBlock n).terminalDeviationDebt_le_ratio
        (herror (select n)) (selectedInitial n) who
    · exact (tendsto_pi_nhds.mp hratioSelected) who
  have huniform :=
    quittingGame_isUniformEquilibriumPayoff_of_interiorCyclicBlocks
      reward selectedPeriod selectedError
      (fun n ↦ herror (select n)) selectedBlock selectedInitial target
      (by
        simpa [interiorCyclicTerminalDebtRatio,
          quittingCyclicOpponentAbsorptionMass] using hratioSelected)
      htargetSelected
  exact ⟨{
    select := select
    select_strictMono := hselect
    target := target
    value_tendsto := by
      exact htargetSelected
    terminalDebt_tendsto_zero := by
      exact hdebtSelected
    target_isUniformEquilibriumPayoff := huniform
  }⟩

/-- Vanishing of the literal maximum player-deleted ratio implies the
coordinatewise ratio convergence consumed by the fixed-payoff theorem. -/
theorem nonempty_interiorCyclicUniformPayoffSubsequence_of_maximumRatio_tendsto_zero
    [Nontrivial ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (period : ℕ → ℕ) (error : ℕ → ℝ) (herror : ∀ n, 0 ≤ error n)
    (block : ∀ n, InteriorApproximateNashCyclicBlock
      reward (period n) (error n))
    (initial : ∀ n, Fin (period n + 1))
    (hmaximum : Tendsto (fun n ↦
      interiorCyclicMaximumTerminalDebtRatio (block n)) atTop (nhds 0)) :
    Nonempty (InteriorCyclicUniformPayoffSubsequence
      reward period error block initial) := by
  apply nonempty_interiorCyclicUniformPayoffSubsequence_of_ratio_tendsto_zero
    reward period error herror block initial
  rw [tendsto_pi_nhds]
  intro who
  apply squeeze_zero
  · exact fun n ↦ (block n).terminalDebtRatio_nonneg (herror n) who
  · intro n
    exact Finset.le_sup' (fun player ↦
      interiorCyclicTerminalDebtRatio (block n) player)
        (Finset.mem_univ who)
  · exact hmaximum

/-- A positive terminal exploitability gap makes every actual periodic
profile carry at least that much unrestricted debt in some coordinate. -/
theorem HasTerminalExploitabilityGap.exists_cyclicProfile_debtor
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {gap : ℝ} (exploit : HasTerminalExploitabilityGap reward gap)
    {m : ℕ} {error : ℝ}
    (block : InteriorApproximateNashCyclicBlock reward m error)
    (initial : Fin (m + 1)) :
    ∃ who, gap ≤ quittingTerminalDeviationDebt reward
      (quittingCyclicBehaviorProfile reward block.cycle initial) who := by
  let profile := quittingCyclicBehaviorProfile reward block.cycle initial
  obtain ⟨who, deviation, hgain⟩ := exploit profile
  refine ⟨who, ?_⟩
  have hdeviation :=
    quittingTerminalPayoff_update_le_continuationBestResponseValue
      reward profile who deviation
  unfold quittingTerminalDeviationDebt
  linarith

/-- Under a positive terminal exploitability gap and vanishing period-error,
one fixed debtor has vanishing opponent absorption and hence admits the exact
singleton-concentration-or-vanishing-hazard refinement. -/
theorem exists_interiorCyclicFixedDebtor_and_ownerEscape_of_terminalGap
    [Nontrivial ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (period : ℕ → ℕ) (error : ℕ → ℝ)
    (herror : ∀ n, 0 ≤ error n)
    (block : ∀ n, InteriorApproximateNashCyclicBlock
      reward (period n) (error n))
    (initial : ∀ n, Fin (period n + 1))
    {gap : ℝ} (hgap : 0 < gap)
    (exploit : HasTerminalExploitabilityGap reward gap)
    (hperiodError : Tendsto (fun n ↦
      ((period n + 1 : ℕ) : ℝ) * error n) atTop (nhds 0)) :
    ∃ fixed : InteriorCyclicFixedDebtorSubsequence
        reward period error block initial gap,
      Nonempty (InteriorCyclicOwnerEscapeAlternative
        reward period error block initial fixed.owner gap) := by
  let fixed := Classical.choice
    (nonempty_interiorCyclicFixedDebtorSubsequence
      reward period error herror block initial hgap
      (fun n ↦ exploit.exists_cyclicProfile_debtor (block n) (initial n))
      hperiodError)
  exact ⟨fixed, fixed.nonempty_ownerEscapeAlternative herror hperiodError⟩

end GameTheory
