/-
Copyright (c) 2026 UniformEquilibrium contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: UniformEquilibrium contributors
-/

import
  UniformEquilibrium.Diagnostics.Quitting.Collision.SingletonPacket.PairBasePaidResetAlignment
import UniformEquilibrium.Diagnostics.Quitting.PaidFirstDisagreementPayoffNearReturn

/-!
# Payoff alignment for a fixed-law paid reset

A fixed-law reset-face minimizer and its supplied reset target carry the same
complete terminal law.  The reward moment of that law determines their
prescribed payoff vectors, so those vectors agree exactly.  For the four-player
pair-base construction, this identifies the returned reset-face payoff with
the payoff of the literal stationary profile carrying the paid row.

This exact payoff identity is not itself a chronological return.  The dynamic
reset alternative selects roots which are Nash against the returned envelope,
whereas the punishment-floor relation requires an endpoint-Nash root against
the tail payoff.  Its states must also dominate the behavioral punishment
floor.  The seam below records the exact additional edge and return path which
would turn the payoff identity into the existing fixed-edge payoff-closure
consumer.
-/

noncomputable section

namespace GameTheory

variable {iota : Type} [Fintype iota] [DecidableEq iota]
variable {reward : {S : Finset iota // S.Nonempty} → Payoff iota}

/-- Keeping one complete terminal law fixes the prescribed payoff vector of
every joint carrier point over that law. -/
theorem QuittingFixedLawResetDispatch.prescribed_eq_target
    {source target : QuittingTerminalSemanticPair iota}
    {mass : QuittingTerminalOutcome iota → ℝ}
    {owner other : iota} {returned : QuittingTerminalSemanticPair iota}
    (dispatch : QuittingFixedLawResetDispatch (reward := reward)
      source target mass owner other returned)
    (htarget : (target, mass) ∈ quittingTerminalSemanticLawCarrier reward) :
    returned.1 = target.1 := by
  have hreturnedMoment := terminalSemanticLawCarrier_rewardMoment
    reward (returned, mass) dispatch.joint
  have htargetMoment := terminalSemanticLawCarrier_rewardMoment
    reward (target, mass) htarget
  exact hreturnedMoment.symm.trans htargetMoment

/-- The precise floor-admissible chronology still needed after exact reset
payoff alignment: one positive edge leaves the returned payoff and a path
from its current state returns to the target payoff. -/
structure QuittingFixedLawResetAdmissibleClosureSeam
    (reward : {S : Finset iota // S.Nonempty} → Payoff iota)
    (target returned : QuittingTerminalSemanticPair iota) where
  edge : QuittingPunishmentFloorAdmissibleEdge reward
  charge_pos : 0 < edge.toBoxEdge.absorptionCharge
  edge_tail_payoff : edge.tail.1.1.1 = returned.1
  endpoint : QuittingPunishmentFloorAdmissibleState reward
  returnPath :
    (quittingPunishmentFloorAdmissibleChargedRelation reward).Path
      edge.current endpoint
  endpoint_payoff : endpoint.1.1.1 = target.1

namespace QuittingFixedLawResetAdmissibleClosureSeam

/-- Exact fixed-law payoff alignment closes the supplied admissible seam into
the standard fixed-edge payoff-closure certificate. -/
def toPositiveAdmissiblePayoffClosure
    {source target : QuittingTerminalSemanticPair iota}
    {mass : QuittingTerminalOutcome iota → ℝ}
    {owner other : iota} {returned : QuittingTerminalSemanticPair iota}
    (dispatch : QuittingFixedLawResetDispatch (reward := reward)
      source target mass owner other returned)
    (htarget : (target, mass) ∈ quittingTerminalSemanticLawCarrier reward)
    (seam : QuittingFixedLawResetAdmissibleClosureSeam reward target returned) :
    QuittingPositiveAdmissiblePayoffClosure reward where
  edge := seam.edge
  charge_pos := seam.charge_pos
  closure := by
    intro endpointError hendpointError
    refine ⟨seam.endpoint, seam.returnPath, ?_⟩
    intro who
    rw [seam.edge_tail_payoff, seam.endpoint_payoff,
      dispatch.prescribed_eq_target htarget]
    simpa using hendpointError.le

/-- The remaining admissible seam is sufficient for a uniform-equilibrium
payoff through the checked payoff-near-return consumer. -/
theorem exists_uniformEquilibriumPayoff
    {source target : QuittingTerminalSemanticPair iota}
    {mass : QuittingTerminalOutcome iota → ℝ}
    {owner other : iota} {returned : QuittingTerminalSemanticPair iota}
    (dispatch : QuittingFixedLawResetDispatch (reward := reward)
      source target mass owner other returned)
    (htarget : (target, mass) ∈ quittingTerminalSemanticLawCarrier reward)
    (seam : QuittingFixedLawResetAdmissibleClosureSeam reward target returned) :
    ∃ payoff : Payoff iota,
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff :=
  (seam.toPositiveAdmissiblePayoffClosure dispatch htarget).exists_uniformEquilibriumPayoff

end QuittingFixedLawResetAdmissibleClosureSeam

/-- The four-player pair-base paid reset dispatch keeps the exact prescribed
payoff of the same stationary profile which carries its paid row. -/
theorem QuittingTerminalExploitabilityWitness.exists_finFour_pairBasePaidResetDispatch_payoffAligned
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    (witness : QuittingTerminalExploitabilityWitness reward)
    (minimum : QuittingTerminalSemanticPair (Fin 4))
    (hminimumMem : minimum ∈ quittingTerminalSemanticCarrier reward)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum minimum ≤
        quittingTerminalSemanticDebtSum candidate)
    (hminimumPositive : 0 < quittingTerminalSemanticDebtSum minimum)
    (owner baseFirst baseSecond : Fin 4)
    (hownerFirst : owner ≠ baseFirst)
    (hownerSecond : owner ≠ baseSecond)
    (hbase : baseFirst ≠ baseSecond) :
    ∃ target : FinFourPairBasePaidResetTarget reward witness owner
        baseFirst baseSecond,
      ∃ returned, QuittingFixedLawResetDispatch (reward := reward)
          minimum target.semanticPair target.mass owner baseFirst returned ∧
        returned.1 = target.semanticPair.1 ∧
        Nonempty (QuittingPaidFirstDisagreementRow reward target.profile
          target.localization.debtor witness.terminalGap) := by
  obtain ⟨target, returned, dispatch⟩ :=
    witness.exists_finFour_pairBasePaidResetDispatch minimum hminimumMem
      hminimum hminimumPositive owner baseFirst baseSecond hownerFirst
        hownerSecond hbase
  refine ⟨target, returned, dispatch, ?_, target.paid_row⟩
  exact dispatch.prescribed_eq_target target.target_joint

end GameTheory
