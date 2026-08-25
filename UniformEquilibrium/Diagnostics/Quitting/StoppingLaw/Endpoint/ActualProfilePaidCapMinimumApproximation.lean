/-
Copyright (c) 2026 UniformEquilibrium contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: UniformEquilibrium contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.StoppingLaw.Endpoint.ActualProfileTerminalGapPaidCap

/-!
# Actual paid cap ports approaching the minimum fiber

Every point of the compact terminal-semantic carrier is a sequential limit of
literal behavioral profiles.  At a positive global minimum, a terminal gap
therefore equips a sequence of actual profiles with full-gap paid cap ports.
Their source debt converges to the minimum, while the complete cap absorption
and cap displacement both converge to zero.

This makes the minimum-fiber boundary nonvacuous even when no behavioral
profile realizes the carrier minimum.  It does not produce an attained inert
source, identify the limiting carrier point with a profile, or regenerate a
paid source after a strict debt descent.
-/

noncomputable section

namespace GameTheory

open Filter Topology

variable {iota : Type} [Fintype iota] [DecidableEq iota]
variable {reward : {S : Finset iota // S.Nonempty} → Payoff iota}
variable {gamma : Real}

/-- A sequence of actual full-gap paid cap ports converging semantically to a
global minimum and becoming asymptotically inert in both absorption and cap
displacement. -/
structure QuittingActualProfilePaidCapMinimumApproximation
    (reward : {S : Finset iota // S.Nonempty} → Payoff iota)
    (minimum : QuittingTerminalSemanticPair iota) (gain : Real) where
  profile : Nat → (quittingGame reward).BehaviorProfile
  actual : ∀ n, QuittingActualProfileTerminalGapPaidCapPort
    reward minimum (profile n) gain
  semantic_tendsto : Tendsto
    (fun n ↦ quittingTerminalSemanticPair reward (profile n))
    atTop (nhds minimum)
  sourceDebt_tendsto : Tendsto
    (fun n ↦ (actual n).source.initialDebt)
    atTop (nhds (quittingTerminalSemanticDebtSum minimum))
  totalAbsorption_tendsto_zero : Tendsto
    (fun n ↦ (actual n).source.totalAbsorption)
    atTop (nhds 0)
  capDisplacement_tendsto_zero : Tendsto
    (fun n ↦ (actual n).source.capDisplacement (actual n).port)
    atTop (nhds 0)

/-- A positive terminal gap and a positive global semantic-debt minimum
produce actual full-gap paid sources whose cap lifts are asymptotically
inert. -/
theorem HasTerminalExploitabilityGap.nonempty_actualProfilePaidCapMinimumApproximation
    (hgamma : 0 < gamma)
    (exploit : HasTerminalExploitabilityGap reward gamma)
    (minimum : QuittingTerminalSemanticPair iota)
    (minimum_mem : minimum ∈ quittingTerminalSemanticCarrier reward)
    (minimum_le : ∀ candidate,
      candidate ∈ quittingTerminalSemanticCarrier reward →
        quittingTerminalSemanticDebtSum minimum ≤
          quittingTerminalSemanticDebtSum candidate)
    (minimum_pos : 0 < quittingTerminalSemanticDebtSum minimum) :
    Nonempty (QuittingActualProfilePaidCapMinimumApproximation
      reward minimum gamma) := by
  obtain ⟨profile, hsemantic⟩ :=
    exists_terminalProfile_sequence_tendsto_semanticPair
      reward minimum minimum_mem
  have hactual : ∀ n, Nonempty
      (QuittingActualProfileTerminalGapPaidCapPort
        reward minimum (profile n) gamma) := fun n ↦
    exploit.nonempty_actualProfilePaidCapPort hgamma minimum
      minimum_le minimum_pos (profile n)
  let actual : ∀ n, QuittingActualProfileTerminalGapPaidCapPort
      reward minimum (profile n) gamma := fun n ↦ Classical.choice (hactual n)
  have hsemanticDebt : Tendsto
      (fun n ↦ quittingTerminalSemanticDebtSum
        (quittingTerminalSemanticPair reward (profile n)))
      atTop (nhds (quittingTerminalSemanticDebtSum minimum)) :=
    continuous_quittingTerminalSemanticDebtSum.continuousAt.tendsto.comp
      hsemantic
  have hsourceDebt : Tendsto
      (fun n ↦ (actual n).source.initialDebt)
      atTop (nhds (quittingTerminalSemanticDebtSum minimum)) := by
    convert hsemanticDebt using 1
    funext n
    rw [QuittingPaidCapLiftedSource.initialDebt, (actual n).source_profile]
  have hexcess : Tendsto
      (fun n ↦ ((actual n).source.initialDebt -
          quittingTerminalSemanticDebtSum minimum) /
        quittingTerminalSemanticDebtSum minimum)
      atTop (nhds 0) := by
    simpa using
      (hsourceDebt.sub_const
        (quittingTerminalSemanticDebtSum minimum)).div_const
          (quittingTerminalSemanticDebtSum minimum)
  have habsorption : Tendsto
      (fun n ↦ (actual n).source.totalAbsorption)
      atTop (nhds 0) := by
    apply squeeze_zero
    · intro n
      exact (actual n).source.totalAbsorption_nonneg
    · intro n
      have hminimumDebt :
          quittingTerminalSemanticDebtSum (actual n).source.minimum =
            quittingTerminalSemanticDebtSum minimum :=
        congrArg quittingTerminalSemanticDebtSum (actual n).source_minimum
      simpa [hminimumDebt] using
        (actual n).source.totalAbsorption_le_excess_div_minimum
          (actual n).port
    · exact hexcess
  have hcapBound : Tendsto
      (fun n ↦ (2 * quittingRewardBound reward *
          ((actual n).source.initialDebt -
            quittingTerminalSemanticDebtSum minimum)) /
        quittingTerminalSemanticDebtSum minimum)
      atTop (nhds 0) := by
    have hscaled := (hsourceDebt.sub_const
      (quittingTerminalSemanticDebtSum minimum)).const_mul
        (2 * quittingRewardBound reward)
    simpa using hscaled.div_const
      (quittingTerminalSemanticDebtSum minimum)
  have hdisplacement : Tendsto
      (fun n ↦ (actual n).source.capDisplacement (actual n).port)
      atTop (nhds 0) := by
    apply squeeze_zero
    · intro n
      exact (actual n).source.capDisplacement_nonneg (actual n).port
    · intro n
      have hminimumDebt :
          quittingTerminalSemanticDebtSum (actual n).source.minimum =
            quittingTerminalSemanticDebtSum minimum :=
        congrArg quittingTerminalSemanticDebtSum (actual n).source_minimum
      simpa [hminimumDebt] using
        (actual n).source
          |>.capDisplacement_le_twoRewardBound_mul_excess_div_minimum
            (actual n).port
    · exact hcapBound
  exact ⟨{
    profile := profile
    actual := actual
    semantic_tendsto := hsemantic
    sourceDebt_tendsto := hsourceDebt
    totalAbsorption_tendsto_zero := habsorption
    capDisplacement_tendsto_zero := hdisplacement }⟩

end GameTheory
