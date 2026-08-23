/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Root.TerminalSemanticEqualityStratum
import UniformEquilibrium.Quitting.Terminal.TargetTail.TerminalUniformPayoffSelection

/-!
# Positive minimum terminal semantic debt

This module isolates the compact finite-dimensional obstruction behind failure
of uniform-equilibrium-payoff existence in a finite quitting game.  Total
terminal semantic debt has a global minimum on the attainable semantic carrier.
For an inhabited finite player type, that minimum is zero exactly when a
uniform-equilibrium payoff exists, and it is positive exactly when no such
payoff exists.
-/

noncomputable section

namespace GameTheory

open Filter Set QuittingBoundaryHolonomy
open scoped Topology

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The attainable terminal semantic carrier has strictly positive minimum
total debt. -/
def HasPositiveMinimumTerminalSemanticDebt
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) : Prop :=
  ∃ pair : QuittingTerminalSemanticPair ι,
    pair ∈ quittingTerminalSemanticCarrier reward ∧
    (∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum pair ≤
        quittingTerminalSemanticDebtSum candidate) ∧
    0 < quittingTerminalSemanticDebtSum pair

/-- The attained minimum of total terminal semantic debt is zero. -/
def HasZeroMinimumTerminalSemanticDebt
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) : Prop :=
  ∃ pair : QuittingTerminalSemanticPair ι,
    pair ∈ quittingTerminalSemanticCarrier reward ∧
    (∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum pair ≤
        quittingTerminalSemanticDebtSum candidate) ∧
    quittingTerminalSemanticDebtSum pair = 0

/-- A literal total-debt upper bound is a full terminal approximate-Nash
certificate. -/
theorem isEpsilonAsymptoticNash_of_terminalSemanticDebtSum_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) {ε : ℝ}
    (hdebt : quittingTerminalSemanticDebtSum
      (quittingTerminalSemanticPair reward profile) ≤ ε) :
    (quittingGame reward).IsεAsymptoticNash
      (quittingTerminalPayoff reward) ε profile := by
  intro who deviation
  have hdeviation :=
    quittingTerminalPayoff_update_le_continuationBestResponseValue
      reward profile who deviation
  have hcoordinate : quittingTerminalSemanticDebt
      (quittingTerminalSemanticPair reward profile) who ≤
      quittingTerminalSemanticDebtSum
        (quittingTerminalSemanticPair reward profile) := by
    have hnonneg : ∀ player,
        0 ≤ quittingTerminalSemanticDebt
          (quittingTerminalSemanticPair reward profile) player := by
      intro player
      exact quittingTerminalDeviationDebt_nonneg reward profile player
    unfold quittingTerminalSemanticDebtSum
    exact Finset.single_le_sum
      (fun player _ ↦ hnonneg player) (Finset.mem_univ who)
  change quittingContinuationBestResponseValue reward profile who -
      quittingTerminalPayoff reward profile who ≤
    quittingTerminalSemanticDebtSum
      (quittingTerminalSemanticPair reward profile) at hcoordinate
  linarith

/-- Terminal approximate Nash bounds literal total semantic debt by player
cardinality times the Nash error. -/
theorem terminalSemanticDebtSum_le_card_mul_of_isEpsilonAsymptoticNash
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (ε : ℝ)
    (hnash : (quittingGame reward).IsεAsymptoticNash
      (quittingTerminalPayoff reward) ε profile) :
    quittingTerminalSemanticDebtSum
      (quittingTerminalSemanticPair reward profile) ≤
        Fintype.card ι * ε := by
  have hcoordinate : ∀ who,
      quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward profile) who ≤ ε := by
    intro who
    let values : Set ℝ := Set.range fun deviation :
        (quittingGame reward).BehaviorStrategy who ↦
      quittingTerminalPayoff reward
        (Function.update profile who deviation) who
    have hvalues : values.Nonempty := by
      exact ⟨quittingTerminalPayoff reward
        (Function.update profile who (profile who)) who, profile who, rfl⟩
    have hcap : quittingContinuationBestResponseValue reward profile who ≤
        quittingTerminalPayoff reward profile who + ε := by
      unfold quittingContinuationBestResponseValue
      apply csSup_le hvalues
      rintro value ⟨deviation, rfl⟩
      exact hnash who deviation
    unfold quittingTerminalSemanticDebt quittingTerminalSemanticPair
    linarith
  unfold quittingTerminalSemanticDebtSum
  calc
    (∑ who, quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward profile) who) ≤
        ∑ _who : ι, ε := Finset.sum_le_sum fun who _ ↦ hcoordinate who
    _ = Fintype.card ι * ε := by simp

/-- A zero minimum supplies terminal approximate equilibria at every positive
error, hence one fixed uniform-equilibrium payoff. -/
theorem exists_uniformEquilibriumPayoff_of_hasZeroMinimumTerminalSemanticDebt
    [Nonempty ι] (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hzero : HasZeroMinimumTerminalSemanticDebt reward) :
    ∃ payoff : Payoff ι,
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff := by
  rcases hzero with ⟨pair, hpair, _hminimum, hsum⟩
  obtain ⟨profiles, hprofiles⟩ :=
    exists_terminalProfile_sequence_tendsto_semanticPair reward pair hpair
  apply quittingGame_exists_uniformEquilibriumPayoff_of_terminalNash_all_errors
  intro ε hε
  have hsumTendsto : Tendsto (fun n ↦ quittingTerminalSemanticDebtSum
      (quittingTerminalSemanticPair reward (profiles n))) atTop (nhds 0) := by
    have hcontinuous :=
      continuous_quittingTerminalSemanticDebtSum.continuousAt.tendsto.comp
        hprofiles
    change Tendsto (fun n ↦ quittingTerminalSemanticDebtSum
      (quittingTerminalSemanticPair reward (profiles n))) atTop
        (nhds (quittingTerminalSemanticDebtSum pair)) at hcontinuous
    rwa [hsum] at hcontinuous
  obtain ⟨threshold, hthreshold⟩ :=
    eventually_atTop.1 (hsumTendsto.eventually (Iio_mem_nhds hε))
  refine ⟨profiles threshold,
    isEpsilonAsymptoticNash_of_terminalSemanticDebtSum_le
      reward (profiles threshold) ?_⟩
  exact (hthreshold threshold le_rfl).le

/-- A uniform-equilibrium payoff forces the attained semantic-debt minimum to
be zero. -/
theorem hasZeroMinimumTerminalSemanticDebt_of_exists_uniformEquilibriumPayoff
    [Nonempty ι] (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hexists : ∃ payoff : Payoff ι,
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff) :
    HasZeroMinimumTerminalSemanticDebt reward := by
  obtain ⟨pair, hpair, hminimum⟩ :=
    exists_minimum_quittingTerminalSemanticDebtSum reward
  have hnonneg : 0 ≤ quittingTerminalSemanticDebtSum pair := by
    unfold quittingTerminalSemanticDebtSum
    exact Finset.sum_nonneg fun who _ ↦
      quittingTerminalSemanticDebt_nonneg_of_mem_carrier reward hpair who
  by_contra hnotZero
  have hsumNe : quittingTerminalSemanticDebtSum pair ≠ 0 := by
    intro hsum
    exact hnotZero ⟨pair, hpair, hminimum, hsum⟩
  have hpositive : 0 < quittingTerminalSemanticDebtSum pair :=
    lt_of_le_of_ne hnonneg (Ne.symm hsumNe)
  obtain ⟨payoff, hpayoff⟩ := hexists
  let ε := quittingTerminalSemanticDebtSum pair /
    (2 * (Fintype.card ι : ℝ))
  have hcard : 0 < (Fintype.card ι : ℝ) := by
    exact_mod_cast Fintype.card_pos
  have hε : 0 < ε := by
    dsimp only [ε]
    positivity
  obtain ⟨profile, hnash⟩ :=
    quittingGame_terminalNash_all_errors_of_isUniformEquilibriumPayoff
      reward payoff hpayoff ε hε
  have hminimumLiteral := hminimum
    (quittingTerminalSemanticPair reward profile)
    (subset_closure ⟨profile, rfl⟩)
  have hupper :=
    terminalSemanticDebtSum_le_card_mul_of_isEpsilonAsymptoticNash
      reward profile ε hnash
  dsimp only [ε] at hupper
  have hcardNe : (Fintype.card ι : ℝ) ≠ 0 := ne_of_gt hcard
  have hscale : (Fintype.card ι : ℝ) *
      (quittingTerminalSemanticDebtSum pair /
        (2 * (Fintype.card ι : ℝ))) =
      quittingTerminalSemanticDebtSum pair / 2 := by
    field_simp
  rw [hscale] at hupper
  linarith

/-- **Exact compact-carrier normalization.**  Uniform-equilibrium-payoff
existence is equivalent to zero attained minimum total terminal semantic debt.
-/
theorem exists_uniformEquilibriumPayoff_iff_hasZeroMinimumTerminalSemanticDebt
    [Nonempty ι] (reward : {S : Finset ι // S.Nonempty} → Payoff ι) :
    (∃ payoff : Payoff ι,
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff) ↔
      HasZeroMinimumTerminalSemanticDebt reward := by
  constructor
  · exact hasZeroMinimumTerminalSemanticDebt_of_exists_uniformEquilibriumPayoff
      reward
  · exact exists_uniformEquilibriumPayoff_of_hasZeroMinimumTerminalSemanticDebt
      reward

/-- Failure of uniform-equilibrium-payoff existence is exactly a strictly
positive attained minimum total terminal semantic debt. -/
theorem not_exists_uniformEquilibriumPayoff_iff_hasPositiveMinimumTerminalSemanticDebt
    [Nonempty ι] (reward : {S : Finset ι // S.Nonempty} → Payoff ι) :
    (¬ ∃ payoff : Payoff ι,
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff) ↔
      HasPositiveMinimumTerminalSemanticDebt reward := by
  constructor
  · intro hno
    obtain ⟨pair, hpair, hminimum⟩ :=
      exists_minimum_quittingTerminalSemanticDebtSum reward
    have hfloor : 0 < quittingTerminalExploitabilityInf reward :=
      quittingTerminalExploitabilityInf_pos_of_no_uniformEquilibriumPayoff
        reward hno
    have hfloorPair :=
      quittingTerminalExploitabilityInf_le_semanticCarrier reward hpair
    have hnonneg : ∀ who, 0 ≤ quittingTerminalSemanticDebt pair who :=
      quittingTerminalSemanticDebt_nonneg_of_mem_carrier reward hpair
    have hmaxSum : quittingTerminalSemanticExploitability pair ≤
        quittingTerminalSemanticDebtSum pair := by
      unfold quittingTerminalSemanticExploitability
      apply finitePlayerMax_le
      intro who
      rw [max_eq_right (hnonneg who)]
      unfold quittingTerminalSemanticDebtSum
      exact Finset.single_le_sum
        (fun player _ ↦ hnonneg player) (Finset.mem_univ who)
    exact ⟨pair, hpair, hminimum, hfloor.trans_le (hfloorPair.trans hmaxSum)⟩
  · rintro ⟨pair, hpair, hminimum, hpositive⟩ hexists
    have hzero :=
      hasZeroMinimumTerminalSemanticDebt_of_exists_uniformEquilibriumPayoff
        reward hexists
    rcases hzero with ⟨zeroPair, hzeroPair, _hzeroMinimum, hsumZero⟩
    have hle := hminimum zeroPair hzeroPair
    linarith

/-- The compact minimum cannot be simultaneously zero and positive. -/
theorem hasPositiveMinimumTerminalSemanticDebt_iff_not_hasZeroMinimumTerminalSemanticDebt
    [Nonempty ι] (reward : {S : Finset ι // S.Nonempty} → Payoff ι) :
    HasPositiveMinimumTerminalSemanticDebt reward ↔
      ¬ HasZeroMinimumTerminalSemanticDebt reward := by
  rw [← not_exists_uniformEquilibriumPayoff_iff_hasPositiveMinimumTerminalSemanticDebt,
    ← exists_uniformEquilibriumPayoff_iff_hasZeroMinimumTerminalSemanticDebt]

end GameTheory
