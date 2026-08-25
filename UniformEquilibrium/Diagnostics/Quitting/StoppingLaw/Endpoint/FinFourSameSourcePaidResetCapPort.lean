/-
Copyright (c) 2026 UniformEquilibrium contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: UniformEquilibrium contributors
-/

import
  UniformEquilibrium.Diagnostics.Quitting.Collision.SingletonPacket.PairBasePaidResetAlignment
import
  UniformEquilibrium.Diagnostics.Quitting.StoppingLaw.Endpoint.PaidCapLiftedSummablePort
import UniformEquilibrium.Quitting.Terminal.PositiveMinimumSemanticDebt

/-!
# Same-source Fin4 paid reset cap port

A four-player terminal exploitability witness supplies a positive global
minimum of terminal-semantic debt.  For any prescribed reset owner and any
disjoint two-player sure-Quit base, the pair-base construction gives one
actual stationary profile which is simultaneously a fixed-law reset target
and a full-gap paid-row source.  The generic cap lift applied to that exact
profile produces a summable marked all-Continue port.

The reset-returned semantic pair is retained as provenance, but it is not the
cap suffix or the port limit.  The cap annotations form the exact
punishment-floor orbit; the prescribed payoffs of the literal prefix profiles
are not asserted to form such an orbit.
-/

noncomputable section

namespace GameTheory

open Filter Math.Probability Math.PMFProduct

namespace FinFourPairBasePaidResetTarget

/-- Turn the paid row on the common stationary reset target directly into the
generic positive-minimum cap-lifted source. -/
noncomputable def capLiftedSource
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    {witness : QuittingTerminalExploitabilityWitness reward}
    {owner baseFirst baseSecond : Fin 4}
    (target : FinFourPairBasePaidResetTarget reward witness owner
      baseFirst baseSecond)
    (minimum : QuittingTerminalSemanticPair (Fin 4))
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum minimum ≤
        quittingTerminalSemanticDebtSum candidate)
    (hminimumPos : 0 < quittingTerminalSemanticDebtSum minimum) :
    QuittingPaidCapLiftedSource reward where
  minimum := minimum
  minimum_le := hminimum
  minimum_pos := hminimumPos
  profile := target.profile
  observer := target.localization.debtor
  gain := witness.terminalGap
  gain_pos := witness.terminalGap_pos
  row := Classical.choice target.paid_row

@[simp] theorem capLiftedSource_profile
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    {witness : QuittingTerminalExploitabilityWitness reward}
    {owner baseFirst baseSecond : Fin 4}
    (target : FinFourPairBasePaidResetTarget reward witness owner
      baseFirst baseSecond)
    (minimum : QuittingTerminalSemanticPair (Fin 4))
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum minimum ≤
        quittingTerminalSemanticDebtSum candidate)
    (hminimumPos : 0 < quittingTerminalSemanticDebtSum minimum) :
    (target.capLiftedSource minimum hminimum hminimumPos).profile =
      target.profile := rfl

@[simp] theorem capLiftedSource_observer
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    {witness : QuittingTerminalExploitabilityWitness reward}
    {owner baseFirst baseSecond : Fin 4}
    (target : FinFourPairBasePaidResetTarget reward witness owner
      baseFirst baseSecond)
    (minimum : QuittingTerminalSemanticPair (Fin 4))
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum minimum ≤
        quittingTerminalSemanticDebtSum candidate)
    (hminimumPos : 0 < quittingTerminalSemanticDebtSum minimum) :
    (target.capLiftedSource minimum hminimum hminimumPos).observer =
      target.localization.debtor := rfl

@[simp] theorem capLiftedSource_gain
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    {witness : QuittingTerminalExploitabilityWitness reward}
    {owner baseFirst baseSecond : Fin 4}
    (target : FinFourPairBasePaidResetTarget reward witness owner
      baseFirst baseSecond)
    (minimum : QuittingTerminalSemanticPair (Fin 4))
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum minimum ≤
        quittingTerminalSemanticDebtSum candidate)
    (hminimumPos : 0 < quittingTerminalSemanticDebtSum minimum) :
    (target.capLiftedSource minimum hminimum hminimumPos).gain =
      witness.terminalGap := rfl

end FinFourPairBasePaidResetTarget

/-- One actual stationary profile and terminal law carry the paid row, reset
target, and unchanged cap suffix; the positive carrier minimum and reset
return are retained separately. -/
structure FinFourSameSourcePaidResetCapPort
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (witness : QuittingTerminalExploitabilityWitness reward)
    (owner baseFirst baseSecond : Fin 4) where
  minimum : QuittingTerminalSemanticPair (Fin 4)
  minimum_mem : minimum ∈ quittingTerminalSemanticCarrier reward
  minimum_le : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
    quittingTerminalSemanticDebtSum minimum ≤
      quittingTerminalSemanticDebtSum candidate
  minimum_pos : 0 < quittingTerminalSemanticDebtSum minimum
  target : FinFourPairBasePaidResetTarget reward witness owner
    baseFirst baseSecond
  returned : QuittingTerminalSemanticPair (Fin 4)
  dispatch : QuittingFixedLawResetDispatch (reward := reward)
    minimum target.semanticPair target.mass owner baseFirst returned
  port : QuittingPaidCapLiftedSource.SummablePort
    (target.capLiftedSource minimum minimum_le minimum_pos)

namespace FinFourSameSourcePaidResetCapPort

variable
  {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
  {witness : QuittingTerminalExploitabilityWitness reward}
  {owner baseFirst baseSecond : Fin 4}

/-- The canonical cap source carried by the composite. -/
def source
    (composite : FinFourSameSourcePaidResetCapPort reward witness owner
      baseFirst baseSecond) : QuittingPaidCapLiftedSource reward :=
  composite.target.capLiftedSource composite.minimum composite.minimum_le
    composite.minimum_pos

@[simp] theorem source_minimum
    (composite : FinFourSameSourcePaidResetCapPort reward witness owner
      baseFirst baseSecond) :
    composite.source.minimum = composite.minimum := rfl

@[simp] theorem source_profile
    (composite : FinFourSameSourcePaidResetCapPort reward witness owner
      baseFirst baseSecond) :
    composite.source.profile = composite.target.profile := rfl

@[simp] theorem source_observer
    (composite : FinFourSameSourcePaidResetCapPort reward witness owner
      baseFirst baseSecond) :
    composite.source.observer = composite.target.localization.debtor := rfl

@[simp] theorem source_gain
    (composite : FinFourSameSourcePaidResetCapPort reward witness owner
      baseFirst baseSecond) :
    composite.source.gain = witness.terminalGap := rfl

/-- The selected paid observer is one of the two forced-Quit base players. -/
theorem observer_mem_base
    (composite : FinFourSameSourcePaidResetCapPort reward witness owner
      baseFirst baseSecond) :
    composite.source.observer ∈
      ({baseFirst, baseSecond} : Finset (Fin 4)) := by
  simpa using composite.target.debtor_mem_base

/-- The full summable marked port, stated using the public composite source. -/
def summablePort
    (composite : FinFourSameSourcePaidResetCapPort reward witness owner
      baseFirst baseSecond) :
    QuittingPaidCapLiftedSource.SummablePort composite.source := by
  simpa [source] using composite.port

/-- Exact one-step scaling of total debt along the composite's cap prefixes. -/
theorem debt_succ
    (composite : FinFourSameSourcePaidResetCapPort reward witness owner
      baseFirst baseSecond) (time : Nat) :
    quittingTerminalSemanticDebtSum
        (quittingTerminalSemanticPair reward
          (quittingCapLiftedPrefixProfile reward composite.source.profile
            (time + 1))) =
      quittingStationaryContinueMass
          (quittingCapLiftedPrefixRoot reward
            (quittingCapLiftedPrefixProfile reward composite.source.profile
              time)) *
        quittingTerminalSemanticDebtSum
          (quittingTerminalSemanticPair reward
            (quittingCapLiftedPrefixProfile reward composite.source.profile
              time)) :=
  quittingCapLiftedPrefixProfile_debt_succ reward composite.source.profile time

/-- Complete finite absorption/debt budget for the same-source cap port. -/
theorem partialAbsorption_budget
    (composite : FinFourSameSourcePaidResetCapPort reward witness owner
      baseFirst baseSecond) (horizon : Nat) :
    quittingTerminalSemanticDebtSum composite.minimum *
          ∑ time ∈ Finset.range horizon,
            quittingRootAbsorptionMass
              (quittingCapLiftedPrefixRoot reward
                (quittingCapLiftedPrefixProfile reward
                  composite.source.profile time)) ≤
        composite.source.initialDebt -
          quittingTerminalSemanticDebtSum
            (quittingTerminalSemanticPair reward
              (quittingCapLiftedPrefixProfile reward composite.source.profile
                horizon)) ∧
      composite.source.initialDebt -
          quittingTerminalSemanticDebtSum
            (quittingTerminalSemanticPair reward
              (quittingCapLiftedPrefixProfile reward composite.source.profile
                horizon)) ≤
        composite.source.initialDebt -
          quittingTerminalSemanticDebtSum composite.minimum :=
  composite.source.partialAbsorption_budget horizon

/-- Every finite cap prefix retains the original paid suffix with the positive
minimum-to-source debt ratio. -/
theorem reachFloor_le_suffixReach
    (composite : FinFourSameSourcePaidResetCapPort reward witness owner
      baseFirst baseSecond) (horizon : Nat) :
    composite.source.reachFloor ≤
      quittingCapLiftedSuffixReach reward composite.source.profile horizon :=
  composite.source.reachFloor_le_suffixReach horizon

/-- Every finite literal prefix carries the shifted full-gap paid row at the
uniform debt-ratio scale. -/
theorem shifted_gain_le
    (composite : FinFourSameSourcePaidResetCapPort reward witness owner
      baseFirst baseSecond) (horizon : Nat) :
    composite.source.reachFloor * witness.terminalGap ≤
      quittingPureTimeDeviationPayoff reward
          (quittingCapLiftedPrefixProfile reward composite.source.profile
            horizon)
          composite.source.observer
          (quittingCapLiftPureTimeShift horizon
            composite.source.row.receivingWitness) -
        quittingPureTimeDeviationPayoff reward
          (quittingCapLiftedPrefixProfile reward composite.source.profile
            horizon)
          composite.source.observer
          (quittingCapLiftPureTimeShift horizon
            composite.source.row.sourceWitness) := by
  simpa using composite.source.shifted_gain_le horizon

end FinFourSameSourcePaidResetCapPort

/-- Any prescribed reset owner and disjoint sure-Quit pair produce one
same-profile paid/reset target and its full cap-lifted summable port. -/
theorem QuittingTerminalExploitabilityWitness.nonempty_finFourSameSourcePaidResetCapPort
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    (witness : QuittingTerminalExploitabilityWitness reward)
    (owner baseFirst baseSecond : Fin 4)
    (hownerFirst : owner ≠ baseFirst)
    (hownerSecond : owner ≠ baseSecond)
    (hbase : baseFirst ≠ baseSecond) :
    Nonempty (FinFourSameSourcePaidResetCapPort reward witness owner
      baseFirst baseSecond) := by
  obtain ⟨minimum, hminimumMem, hminimum, hminimumPos⟩ :=
    (not_exists_uniformEquilibriumPayoff_iff_hasPositiveMinimumTerminalSemanticDebt
      reward).mp witness.not_exists_uniformEquilibriumPayoff
  obtain ⟨target, returned, dispatch⟩ :=
    witness.exists_finFour_pairBasePaidResetDispatch minimum hminimumMem
      hminimum hminimumPos owner baseFirst baseSecond hownerFirst
        hownerSecond hbase
  let source := target.capLiftedSource minimum hminimum hminimumPos
  let port := Classical.choice source.nonempty_summablePort
  exact ⟨{
    minimum := minimum
    minimum_mem := hminimumMem
    minimum_le := hminimum
    minimum_pos := hminimumPos
    target := target
    returned := returned
    dispatch := dispatch
    port := by simpa [source] using port }⟩

end GameTheory
