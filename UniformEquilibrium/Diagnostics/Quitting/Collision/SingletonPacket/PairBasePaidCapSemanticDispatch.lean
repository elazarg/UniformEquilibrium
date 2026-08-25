/-
Copyright (c) 2026 UniformEquilibrium contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: UniformEquilibrium contributors
-/

import
  UniformEquilibrium.Diagnostics.Quitting.Collision.SingletonPacket.PairBaseStationaryDebtLocalization
import
  UniformEquilibrium.Diagnostics.Quitting.Collision.SingletonPacket.FullSupportProjectiveQBarResidual
import
  UniformEquilibrium.Diagnostics.Quitting.StoppingLaw.Endpoint.PaidCapLiftedSummablePort
import UniformEquilibrium.Quitting.Terminal.PositiveMinimumSemanticDebt

/-!
# Pair-base paid cap semantic dispatch on four players

The pair-base stationary construction is available for every prescribed
cardinality-two base.  A terminal exploitability witness supplies a positive
global minimum of terminal semantic debt, so the stationary paid source can be
fed directly into the cap-lifted summable-port construction.

This removes the source-selection problem from the four-player hard residual.
The static principal, toggle, helper, and lasso selectors need not be matched to
an independently selected semantic source: after any relevant pair of labels
has been selected, this module constructs the paid source on that very pair.
Indeed, the conclusion uses only the terminal exploitability witness and is
therefore stronger than a hard-residual dispatch.

The output is still a summable all-Continue port.  No restart, cumulative-charge
near-return, or uniform-equilibrium consumer is asserted here.
-/

noncomputable section

namespace GameTheory

open Finset
open Math.Probability Math.PMFProduct

/-- One actual pair-base stationary source, its actual positive semantic
minimum, and the cap-lifted summable port obtained from the same literal paid
row. -/
structure FinFourPairBasePaidCapSemanticDispatch
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (witness : QuittingTerminalExploitabilityWitness reward)
    (base : Finset (Fin 4)) where
  localization :
    FinFourPairBaseStationaryDebtLocalization reward witness base
  source : QuittingPaidCapLiftedSource reward
  minimum_mem :
    source.minimum ∈ quittingTerminalSemanticCarrier reward
  source_profile_eq :
    source.profile =
      quittingStationaryProfile reward
        (quittingPersistentBaseRoot base
          (finFourPairBaseComplement base) localization.point)
  source_observer_eq : source.observer = localization.debtor
  source_gain_eq : source.gain = witness.terminalGap
  port : QuittingPaidCapLiftedSource.SummablePort source

namespace FinFourPairBasePaidCapSemanticDispatch

variable {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
variable {witness : QuittingTerminalExploitabilityWitness reward}
variable {base : Finset (Fin 4)}

/-- The paid observer is one of the two prescribed sure-Quit base players. -/
theorem observer_mem_base
    (dispatch : FinFourPairBasePaidCapSemanticDispatch reward witness base) :
    dispatch.source.observer ∈ base := by
  rw [dispatch.source_observer_eq]
  exact dispatch.localization.debtor_mem

/-- The shifted paid rows retain a fixed strictly positive gain, uniformly in
finite cap-prefix depth. -/
theorem shifted_gain_pos
    (dispatch : FinFourPairBasePaidCapSemanticDispatch reward witness base) :
    0 < dispatch.source.reachFloor * witness.terminalGap := by
  rw [← dispatch.source_gain_eq]
  exact mul_pos dispatch.source.reachFloor_pos dispatch.source.gain_pos

end FinFourPairBasePaidCapSemanticDispatch

/-- Every prescribed pair base in a four-player terminal-gap game produces one
literal stationary paid source and its source-matched cap-lifted summable port.
No singleton sign, hard-principal, punishment-normality, or packet-support
hypothesis is needed. -/
theorem nonempty_finFourPairBasePaidCapSemanticDispatch
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    (witness : QuittingTerminalExploitabilityWitness reward)
    (base : Finset (Fin 4)) (hbaseCard : base.card = 2) :
    Nonempty (FinFourPairBasePaidCapSemanticDispatch reward witness base) := by
  obtain ⟨localization⟩ :=
    nonempty_finFourPairBaseStationaryDebtLocalization
      witness base hbaseCard
  have hminimumData : HasPositiveMinimumTerminalSemanticDebt reward :=
    (not_exists_uniformEquilibriumPayoff_iff_hasPositiveMinimumTerminalSemanticDebt
      reward).1 witness.not_exists_uniformEquilibriumPayoff
  obtain ⟨minimum, hminimumMem, hminimum, hminimumPos⟩ := hminimumData
  let profile :=
    quittingStationaryProfile reward
      (quittingPersistentBaseRoot base
        (finFourPairBaseComplement base) localization.point)
  let row : QuittingPaidFirstDisagreementRow reward profile
      localization.debtor witness.terminalGap :=
    Classical.choice localization.paid_row
  let source : QuittingPaidCapLiftedSource reward := {
    minimum := minimum
    minimum_le := hminimum
    minimum_pos := hminimumPos
    profile := profile
    observer := localization.debtor
    gain := witness.terminalGap
    gain_pos := witness.terminalGap_pos
    row := row }
  obtain ⟨port⟩ := source.nonempty_summablePort
  exact ⟨{
    localization := localization
    source := source
    minimum_mem := hminimumMem
    source_profile_eq := rfl
    source_observer_eq := rfl
    source_gain_eq := rfl
    port := port }⟩

namespace FinFourQuantitativeFullSupportHardResidual

/-- **Four-player semantic dispatch.**  After any pair of labels has been
selected from the static hard geometry, the same-table hard residual produces
its actual paid cap source on precisely that pair.  Thus the source can be
selected after the principal/toggle labels rather than independently of them.
-/
theorem nonempty_pairBasePaidCapSemanticDispatch
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    {bound : ℝ}
    (residual : FinFourQuantitativeFullSupportHardResidual reward bound)
    (base : Finset (Fin 4)) (hbaseCard : base.card = 2) :
    Nonempty (FinFourPairBasePaidCapSemanticDispatch reward
      residual.witness base) :=
  nonempty_finFourPairBasePaidCapSemanticDispatch
    residual.witness base hbaseCard

end FinFourQuantitativeFullSupportHardResidual

/-- The hard-residual hypotheses are unnecessary for the dispatch itself:
every four-player quitting table either already has a uniform-equilibrium
payoff or, on every prescribed pair base, carries a terminal-gap witness with
a pair-base paid cap semantic dispatch. -/
theorem uniformPayoff_or_exists_pairBasePaidCapSemanticDispatch
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (base : Finset (Fin 4)) (hbaseCard : base.card = 2) :
    (∃ payoff : Payoff (Fin 4),
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff) ∨
      ∃ witness : QuittingTerminalExploitabilityWitness reward,
        Nonempty (FinFourPairBasePaidCapSemanticDispatch reward witness base) := by
  by_cases hpayoff : ∃ payoff : Payoff (Fin 4),
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff
  · exact Or.inl hpayoff
  · right
    let witness :=
      quittingTerminalExploitabilityWitnessOfNoUniformPayoff reward hpayoff
    exact ⟨witness,
      nonempty_finFourPairBasePaidCapSemanticDispatch
        witness base hbaseCard⟩

end GameTheory
