/-
Copyright (c) 2026 UniformEquilibrium contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: UniformEquilibrium contributors
-/

import MathUE.ProbabilityMassFunction.BoundedSupportAverage
import UniformEquilibrium.Diagnostics.Quitting.StoppingLaw.Endpoint.PaidCapMinimumFiberContraction
import UniformEquilibrium.Quitting.Paths.BehaviorStoppingPayoff
import UniformEquilibrium.Quitting.Terminal.ExploitabilityGap

/-!
# Actual-profile terminal-gap paid-cap port

A positive terminal exploitability gap at an arbitrary literal behavioral
profile is a difference of two bounded stopping-law averages.  Support atoms
bracketing those averages give two pure quit times, retaining the full weak
gap.  Their first disagreement supplies the paid row required by the existing
cap-lifted summable-port construction.

The terminal gap rules out the charged near-return arm, whose checked consumer
would be a uniform-equilibrium payoff.  More strongly, if the actual profile
lies in the minimum-debt fiber, the absorption budget vanishes and the port is
literally inert without using the terminal gap again.  No observer alignment,
finite stopping date, or prescribed-payoff Bellman edge is asserted.
-/

noncomputable section

namespace GameTheory

open Math.Probability Math.ProbabilityMassFunction

/-- Retain both the profitable behavioral deviation and its supported pure-time witnesses. -/
theorem HasTerminalExploitabilityGap.exists_supported_pureTimePayoff_sub_at_with_gain
    {ι : Type} [Fintype ι] [DecidableEq ι]
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι} {gap : ℝ}
    (exploit : HasTerminalExploitabilityGap reward gap)
    (profile : (quittingGame reward).BehaviorProfile) :
    ∃ observer, ∃ deviation : (quittingGame reward).BehaviorStrategy observer,
      gap ≤ quittingTerminalPayoff reward (Function.update profile observer deviation) observer -
        quittingTerminalPayoff reward profile observer ∧
      ∃ sourceWitness receivingWitness,
        sourceWitness ∈ (quittingBehaviorStoppingLaw reward (profile observer)).support ∧
        receivingWitness ∈ (quittingBehaviorStoppingLaw reward deviation).support ∧
        gap ≤ quittingPureTimeDeviationPayoff reward profile observer receivingWitness -
          quittingPureTimeDeviationPayoff reward profile observer sourceWitness := by
  obtain ⟨observer, deviation, hgain⟩ := exploit profile
  let value : Option ℕ → ℝ := quittingPureTimeDeviationPayoff reward profile observer
  have hvalue : ∀ quitTime, |value quitTime| ≤ quittingRewardBound reward := by
    intro quitTime
    exact abs_quittingTerminalPayoff_le reward _ observer
      (abs_reward_le_quittingRewardBound reward)
  have hdeviation : quittingTerminalPayoff reward
      (Function.update profile observer deviation) observer =
      Math.Probability.expect (quittingBehaviorStoppingLaw reward deviation) value := by
    exact quittingTerminalPayoff_update_eq_expect_stoppingLaw_pureTime
      reward profile observer deviation
  have hprescribed : quittingTerminalPayoff reward profile observer =
      Math.Probability.expect (quittingBehaviorStoppingLaw reward (profile observer)) value := by
    have h := quittingTerminalPayoff_update_eq_expect_stoppingLaw_pureTime
      reward profile observer (profile observer)
    rw [Function.update_eq_self] at h
    exact h
  obtain ⟨receivingWitness, sourceWitness, hreceiving, hsource, havg⟩ :=
    exists_support_pair_expect_sub_le_sub
      (quittingBehaviorStoppingLaw reward deviation)
      (quittingBehaviorStoppingLaw reward (profile observer)) value value hvalue hvalue
  have hgain' : gap ≤ quittingTerminalPayoff reward
      (Function.update profile observer deviation) observer -
        quittingTerminalPayoff reward profile observer := by linarith
  refine ⟨observer, deviation, hgain', sourceWitness, receivingWitness,
    hsource, hreceiving, ?_⟩
  calc
    gap ≤ quittingTerminalPayoff reward
        (Function.update profile observer deviation) observer -
      quittingTerminalPayoff reward profile observer := hgain'
    _ = Math.Probability.expect (quittingBehaviorStoppingLaw reward deviation) value -
        Math.Probability.expect (quittingBehaviorStoppingLaw reward (profile observer)) value := by
      rw [hdeviation, hprescribed]
    _ ≤ value receivingWitness - value sourceWitness := havg

variable {iota : Type} [Fintype iota] [DecidableEq iota]
variable {reward : {S : Finset iota // S.Nonempty} -> Payoff iota}
variable {gamma : Real}

/-- The profitable behavioral stopping law and the prescribed stopping law
contain a pair of pure-time atoms retaining the full terminal gap. -/
theorem HasTerminalExploitabilityGap.exists_supported_pureTimePayoff_sub_at
    (exploit : HasTerminalExploitabilityGap reward gamma)
    (profile : (quittingGame reward).BehaviorProfile) :
    exists observer,
      exists deviation : (quittingGame reward).BehaviorStrategy observer,
      exists sourceWitness receivingWitness,
      sourceWitness ∈
          (quittingBehaviorStoppingLaw reward (profile observer)).support ∧
        receivingWitness ∈
          (quittingBehaviorStoppingLaw reward deviation).support ∧
        gamma <=
          quittingPureTimeDeviationPayoff reward profile observer receivingWitness -
            quittingPureTimeDeviationPayoff reward profile observer sourceWitness := by
  obtain ⟨observer, deviation, _, sourceWitness, receivingWitness, hsource, hreceiving, hgap⟩ :=
    exploit.exists_supported_pureTimePayoff_sub_at_with_gain profile
  exact ⟨observer, deviation, sourceWitness, receivingWitness, hsource, hreceiving, hgap⟩

/-- At every literal behavioral profile, a positive terminal gap supplies a
full-gap paid first-disagreement row. -/
theorem HasTerminalExploitabilityGap.exists_paidFirstDisagreementRow_at
    (hgamma : 0 < gamma)
    (exploit : HasTerminalExploitabilityGap reward gamma)
    (profile : (quittingGame reward).BehaviorProfile) :
    exists observer,
      Nonempty
        (QuittingPaidFirstDisagreementRow reward profile observer gamma) := by
  obtain ⟨observer, _deviation, sourceWitness, receivingWitness,
      _hsource, _hreceiving, hedge⟩ :=
    exploit.exists_supported_pureTimePayoff_sub_at profile
  obtain ⟨row, _hrowSource, _hrowReceiving⟩ :=
    exists_quittingPaidFirstDisagreementRow_of_pureTimePayoff_sub
      reward profile observer sourceWitness receivingWitness gamma hgamma hedge
  exact ⟨observer, ⟨row⟩⟩

/-- The data produced directly from one actual profile: a paid cap-lifted
source with the supplied minimum and gap, together with one summable port. -/
structure QuittingActualProfileTerminalGapPaidCapPort
    (reward : {S : Finset iota // S.Nonempty} -> Payoff iota)
    (minimum : QuittingTerminalSemanticPair iota)
    (profile : (quittingGame reward).BehaviorProfile) (gain : Real) where
  source : QuittingPaidCapLiftedSource reward
  source_minimum : source.minimum = minimum
  source_profile : source.profile = profile
  source_gain : source.gain = gain
  port : source.SummablePort

/-- A positive terminal gap constructs the paid cap-lifted port at every
actual profile, without a floor or stationary-profile hypothesis. -/
theorem HasTerminalExploitabilityGap.nonempty_actualProfilePaidCapPort
    (hgamma : 0 < gamma)
    (exploit : HasTerminalExploitabilityGap reward gamma)
    (minimum : QuittingTerminalSemanticPair iota)
    (minimum_le : forall candidate,
      candidate ∈ quittingTerminalSemanticCarrier reward ->
        quittingTerminalSemanticDebtSum minimum <=
          quittingTerminalSemanticDebtSum candidate)
    (minimum_pos : 0 < quittingTerminalSemanticDebtSum minimum)
    (profile : (quittingGame reward).BehaviorProfile) :
    Nonempty
      (QuittingActualProfileTerminalGapPaidCapPort
        reward minimum profile gamma) := by
  obtain ⟨observer, ⟨row⟩⟩ :=
    exploit.exists_paidFirstDisagreementRow_at hgamma profile
  let source : QuittingPaidCapLiftedSource reward := {
    minimum := minimum
    minimum_le := minimum_le
    minimum_pos := minimum_pos
    profile := profile
    observer := observer
    gain := gamma
    gain_pos := hgamma
    row := row }
  obtain ⟨port⟩ := source.nonempty_summablePort
  exact ⟨{
    source := source
    source_minimum := rfl
    source_profile := rfl
    source_gain := rfl
    port := port }⟩

namespace QuittingActualProfileTerminalGapPaidCapPort

variable {minimum : QuittingTerminalSemanticPair iota}
variable {profile : (quittingGame reward).BehaviorProfile}

/-- The checked exhaustive and pairwise-disjoint trichotomy applies directly
to the port extracted from the actual profile. -/
theorem exactTrichotomy
    (actual : QuittingActualProfileTerminalGapPaidCapPort
      reward minimum profile gamma) :
    (actual.source.ChargedNearReturn actual.port ∨
        actual.source.QuantitativeDebtDescent actual.port ∨
        actual.source.InertStall actual.port) ∧
      ¬(actual.source.ChargedNearReturn actual.port ∧
        actual.source.QuantitativeDebtDescent actual.port) ∧
      ¬(actual.source.ChargedNearReturn actual.port ∧
        actual.source.InertStall actual.port) ∧
      ¬(actual.source.QuantitativeDebtDescent actual.port ∧
        actual.source.InertStall actual.port) :=
  actual.source.exactTrichotomy actual.port

/-- Under the same terminal gap, the actual port can only descend
quantitatively or remain in the literal inert stall. -/
theorem quantitativeDebtDescent_or_inertStall
    (actual : QuittingActualProfileTerminalGapPaidCapPort
      reward minimum profile gamma)
    (hgamma : 0 < gamma)
    (exploit : HasTerminalExploitabilityGap reward gamma) :
    actual.source.QuantitativeDebtDescent actual.port ∨
      actual.source.InertStall actual.port := by
  rcases actual.exactTrichotomy.1 with hcharged | hdescent | hinert
  · exact False.elim
      ((quittingGame_not_exists_uniformEquilibriumPayoff_of_terminalExploitabilityGap
        reward hgamma exploit) hcharged.uniformEquilibriumPayoff)
  · exact Or.inl hdescent
  · exact Or.inr hinert

/-- If the actual profile has the global minimum debt, the terminal-gap port
is forced into the literal inert stall. -/
theorem inertStall_of_minimumFiber
    (actual : QuittingActualProfileTerminalGapPaidCapPort
      reward minimum profile gamma)
    (hminimumFiber :
      quittingTerminalSemanticDebtSum
          (quittingTerminalSemanticPair reward profile) =
        quittingTerminalSemanticDebtSum minimum) :
    actual.source.InertStall actual.port := by
  have hsourceDebt : actual.source.initialDebt =
      quittingTerminalSemanticDebtSum minimum := by
    rw [QuittingPaidCapLiftedSource.initialDebt, actual.source_profile,
      hminimumFiber]
  have hsourceMinimumDebt :
      quittingTerminalSemanticDebtSum actual.source.minimum =
        quittingTerminalSemanticDebtSum minimum :=
    congrArg quittingTerminalSemanticDebtSum actual.source_minimum
  exact actual.source.inertStall_of_initialDebt_eq_minimum actual.port
    (hsourceDebt.trans hsourceMinimumDebt.symm)

end QuittingActualProfileTerminalGapPaidCapPort

end GameTheory
