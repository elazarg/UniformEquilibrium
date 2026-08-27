/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors.
-/

import Research.Quitting.ConcentratedCollisionThreeRoleEndpointLaw
import Research.Quitting.FinFourProducerAtlas.Source

/-!
# Regenerating a Fin4 minimum source at an actual three-role endpoint law

An actualized three-role endpoint law lies either strictly above the incoming
minimum debt or on the same minimum fibre.  In the latter case its retained
positive routed-law atom is causalized at that exact joint point, producing a
fresh `FinFourMinimumAtomProducer` with the unchanged hard residual.

This is source regeneration without an oriented rank decrease.  The new
chronology is not asserted to contain the incoming endpoint edge.
-/

noncomputable section

namespace GameTheory

open Filter Set Math.Probability Math.PMFProduct

variable
  {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
  {bound : ℝ} {source : FinFourMinimumAtomProducer reward bound}
  {profiles : ℕ → (quittingGame reward).BehaviorProfile}
  {owner : Fin 4} {marked : {S : Finset (Fin 4) // S.Nonempty}}
  {cutoff : ℕ → ℕ} {scale : ℕ → ℝ}
  {packet : QuittingReprojectionConcentratedPacket
    reward profiles owner marked cutoff scale}
  {mover recipient : Fin 4}

/-- The regenerated source at the exact endpoint semantic/law point.  The
terminal is the routed atom retained by the actual endpoint sequence. -/
structure FinFourThreeRoleMinimumTargetRegeneration
    (source : FinFourMinimumAtomProducer reward bound)
    (endpoint : ConcentratedCollisionThreeRoleEndpointLaw source.point.1 packet
      mover recipient) where
  next : FinFourMinimumAtomProducer reward bound
  next_residual_eq : next.residual = source.residual
  next_point_eq : next.point = endpoint.targetPoint
  next_terminal_eq : next.atom.terminal = endpoint.routedTerminal
  resolution_le_terminalMass : packet.resolution ≤
    next.point.2 (some next.atom.terminal)

namespace FinFourThreeRoleMinimumTargetRegeneration

/-- The regenerated source's named terminal mass is exactly the retained
endpoint-law mass, not a reselected law coordinate. -/
theorem next_terminalMass_eq_endpoint
    (endpoint : ConcentratedCollisionThreeRoleEndpointLaw source.point.1 packet
      mover recipient)
    (regeneration : FinFourThreeRoleMinimumTargetRegeneration source endpoint) :
    regeneration.next.point.2 (some regeneration.next.atom.terminal) =
      endpoint.targetPoint.2 (some endpoint.routedTerminal) := by
  rw [regeneration.next_terminal_eq]
  exact congrArg
    (fun point : QuittingTerminalSemanticLawPoint (Fin 4) ↦
      point.2 (some endpoint.routedTerminal)) regeneration.next_point_eq

end FinFourThreeRoleMinimumTargetRegeneration

/-- The strongest honest endpoint-law outcome: strict debt ascent, or an exact
same-law minimum-source regeneration. -/
structure FinFourThreeRoleRegenerationOrAscent
    (source : FinFourMinimumAtomProducer reward bound)
    {profiles : ℕ → (quittingGame reward).BehaviorProfile}
    {owner : Fin 4} {marked : {S : Finset (Fin 4) // S.Nonempty}}
    {cutoff : ℕ → ℕ} {scale : ℕ → ℝ}
    (packet : QuittingReprojectionConcentratedPacket
      reward profiles owner marked cutoff scale) where
  mover : Fin 4
  recipient : Fin 4
  endpoint : ConcentratedCollisionThreeRoleEndpointLaw source.point.1 packet
    mover recipient
  outcome :
    quittingTerminalSemanticDebtSum source.point.1 <
        quittingTerminalSemanticDebtSum endpoint.targetPoint.1 ∨
      Nonempty (FinFourThreeRoleMinimumTargetRegeneration source endpoint)

namespace ConcentratedCollisionThreeRoleEndpointLaw

/-- In Fin4 the mover loses at least the literal `rho^2 * D_* / 8`. -/
theorem finFour_mover_drop
    (endpoint : ConcentratedCollisionThreeRoleEndpointLaw source.point.1 packet
      mover recipient) :
    quittingTerminalSemanticDebt endpoint.targetPoint.1 mover ≤
      quittingTerminalSemanticDebt endpoint.sourceLimit mover -
        packet.resolution ^ 2 *
          quittingTerminalSemanticDebtSum source.point.1 / 8 := by
  convert endpoint.mover_drop using 1
  all_goals norm_num

/-- In Fin4 the recipient rises by at least the literal
`rho^2 * D_* / 64`. -/
theorem finFour_recipient_rise
    (endpoint : ConcentratedCollisionThreeRoleEndpointLaw source.point.1 packet
      mover recipient) :
    packet.resolution ^ 2 *
          quittingTerminalSemanticDebtSum source.point.1 / 64 ≤
      quittingTerminalSemanticDebtChange endpoint.sourceLimit
        endpoint.targetPoint.1 recipient := by
  convert endpoint.recipient_rise using 1
  all_goals norm_num

/-- Equality of the endpoint debt with the incoming minimum debt causalizes
the endpoint's own routed law atom at the exact same joint point. -/
theorem nonempty_finFourMinimumTargetRegeneration
    (endpoint : ConcentratedCollisionThreeRoleEndpointLaw source.point.1 packet
      mover recipient)
    (htarget : quittingTerminalSemanticDebtSum endpoint.targetPoint.1 =
      quittingTerminalSemanticDebtSum source.point.1) :
    Nonempty (FinFourThreeRoleMinimumTargetRegeneration source endpoint) := by
  have hmass : 0 <
      endpoint.targetPoint.2 (some endpoint.routedTerminal) :=
    endpoint.terminalMass_pos
  let atom : QuittingMinimumLawCausalSuffixAtom reward endpoint.targetPoint := {
    terminal := endpoint.routedTerminal
    terminalMass_pos := hmass
    chronology :=
      exists_deep_nearMinimum_capNashChronologies_with_causalSuffixAtom
        reward endpoint.targetPoint endpoint.routedTerminal endpoint.target_mem
          hmass source.inf_pos (htarget.trans source.debt_eq_inf)
  }
  let next : FinFourMinimumAtomProducer reward bound := {
    residual := source.residual
    point := endpoint.targetPoint
    point_mem := endpoint.target_mem
    semantic_mem := terminalSemanticLawCarrier_fst_mem_carrier
      endpoint.targetPoint endpoint.target_mem
    minimum := by
      intro candidate hcandidate
      rw [htarget]
      exact source.minimum candidate hcandidate
    inf_pos := source.inf_pos
    debt_eq_inf := htarget.trans source.debt_eq_inf
    atom := atom
  }
  exact ⟨{
    next := next
    next_residual_eq := rfl
    next_point_eq := rfl
    next_terminal_eq := rfl
    resolution_le_terminalMass := endpoint.terminalMass_floor
  }⟩

/-- Every actualized endpoint law gives strict ascent or exact source
regeneration; no rank orientation is asserted. -/
theorem nonempty_finFourRegenerationOrAscent
    (endpoint : ConcentratedCollisionThreeRoleEndpointLaw source.point.1 packet
      mover recipient) :
    Nonempty (FinFourThreeRoleRegenerationOrAscent source packet) := by
  refine ⟨{
    mover := mover
    recipient := recipient
    endpoint := endpoint
    outcome := ?_
  }⟩
  rcases endpoint.target_fiber_or_ascent with hminimum | hascent
  · exact Or.inr (endpoint.nonempty_finFourMinimumTargetRegeneration hminimum)
  · exact Or.inl hascent

end ConcentratedCollisionThreeRoleEndpointLaw

namespace FinFourThreeRoleRegenerationOrAscent

/-- The public semantic chord is a forgetful view of the retained endpoint
law, not an input to regeneration. -/
def toThreeRoleLimitChord
    (result : FinFourThreeRoleRegenerationOrAscent source packet) :
    ConcentratedCollisionFourRole.ThreeRoleLimitChord reward source.point.1
      owner result.mover result.recipient packet.resolution :=
  result.endpoint.toThreeRoleLimitChord

end FinFourThreeRoleRegenerationOrAscent

end GameTheory
