/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors.
-/

import Research.Quitting.FinFourProducerAtlas.MinimumResponseChordActualDecoder
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticCausalCollisionRecipientAtom

/-!
# Recipient atoms for actual Fin4 minimum response rectangles

A compiled minimum-response rectangle has two semantic endpoints on the same
global minimum fibre.  The observer has positive debt at the upper endpoint
and zero debt at the response endpoint.  Therefore the observer's complete
debt loss is transferred exactly to the other three players.

One fixed positive recipient can be selected at the compact limit.  Along the
same actual endpoint/response profiles used by the rectangle decoder, that
recipient's debt increase remains uniformly positive eventually.  The generic
endpoint-recipient decoder then attaches a literal prescribed atom or
deviation-rectangle atom to every sufficiently late actual response edge.

This is a source-faithful atom producer.  It does not identify the selected
recipient with the routed terminal, orient a regenerated source, or construct
a uniform-equilibrium payoff.
-/

noncomputable section

namespace GameTheory

open Filter Set Math.Probability Math.PMFProduct
open scoped Topology

variable
  {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
  {bound : ℝ} {source : FinFourMinimumAtomProducer reward bound}
  {origin : FinFourMinimumResponseEndpointRiseOrigin source}
  {sequence : FinFourMinimumResponseRectangleSequence origin}

namespace FinFourMinimumResponseCompiledRectangle

/-- The actual response profile on the common compactifying subsequence. -/
def actualResponseProfile
    (compiled : FinFourMinimumResponseCompiledRectangle sequence)
    (rank : ℕ) : (quittingGame reward).BehaviorProfile :=
  let index := compiled.packet.commonSubsequence rank
  Function.update (compiled.packet.endpointProfile index)
    compiled.packet.observer
    (quittingPureTimeBehaviorStrategy reward compiled.packet.observer
      (compiled.packet.responseChoice index))

/-- The two same-minimum endpoints transfer exactly the killed observer debt
to the opposite face. -/
theorem responsePoint_opponentTransfer_eq_endpointObserverDebt
    (compiled : FinFourMinimumResponseCompiledRectangle sequence) :
    (∑ recipient ∈ Finset.univ.erase compiled.packet.observer,
        quittingTerminalSemanticDebtChange
          compiled.packet.endpointPoint.1
          compiled.packet.responsePoint.1 recipient) =
      quittingTerminalSemanticDebt compiled.packet.endpointPoint.1
        compiled.packet.observer := by
  have hsplit := Finset.sum_erase_add Finset.univ
    (fun player =>
      quittingTerminalSemanticDebtChange
        compiled.packet.endpointPoint.1
        compiled.packet.responsePoint.1 player)
    (Finset.mem_univ compiled.packet.observer)
  have htotal :
      (∑ player,
          quittingTerminalSemanticDebtChange
            compiled.packet.endpointPoint.1
            compiled.packet.responsePoint.1 player) =
        quittingTerminalSemanticDebtSum compiled.packet.responsePoint.1 -
          quittingTerminalSemanticDebtSum compiled.packet.endpointPoint.1 := by
    unfold quittingTerminalSemanticDebtChange
      quittingTerminalSemanticDebtSum
    rw [Finset.sum_sub_distrib]
  have hobserver :
      quittingTerminalSemanticDebtChange
          compiled.packet.endpointPoint.1
          compiled.packet.responsePoint.1 compiled.packet.observer =
        -quittingTerminalSemanticDebt
          compiled.packet.endpointPoint.1 compiled.packet.observer := by
    unfold quittingTerminalSemanticDebtChange
    rw [compiled.responsePoint_observerDebt_eq_zero]
    ring
  rw [htotal, compiled.packet.response_debtSum_eq_source,
    compiled.packet.endpoint_debtSum_eq_source, sub_self, hobserver] at hsplit
  linarith

/-- At the compact response endpoint, one fixed nonobserver receives positive
debt. -/
theorem exists_responsePoint_positiveRecipient
    (compiled : FinFourMinimumResponseCompiledRectangle sequence) :
    ∃ recipient ∈ Finset.univ.erase compiled.packet.observer,
      0 < quittingTerminalSemanticDebtChange
        compiled.packet.endpointPoint.1
        compiled.packet.responsePoint.1 recipient := by
  have hsum :
      0 < ∑ recipient ∈ Finset.univ.erase compiled.packet.observer,
        quittingTerminalSemanticDebtChange
          compiled.packet.endpointPoint.1
          compiled.packet.responsePoint.1 recipient := by
    rw [compiled.responsePoint_opponentTransfer_eq_endpointObserverDebt]
    exact compiled.endpointPoint_observerDebt_pos
  have hzero :
      (∑ _recipient ∈ Finset.univ.erase compiled.packet.observer,
        (0 : ℝ)) = 0 := by
    simp
  obtain ⟨recipient, hrecipient, hpositive⟩ :=
    Finset.exists_lt_of_sum_lt
      (show
        (∑ _recipient ∈ Finset.univ.erase compiled.packet.observer,
            (0 : ℝ)) <
          ∑ recipient ∈ Finset.univ.erase compiled.packet.observer,
            quittingTerminalSemanticDebtChange
              compiled.packet.endpointPoint.1
              compiled.packet.responsePoint.1 recipient by
        simpa only [hzero] using hsum)
  exact ⟨recipient, hrecipient, hpositive⟩

/-- One fixed limit recipient is a source-matched positive recipient on every
sufficiently late actual response edge, and hence carries a literal endpoint
atom certificate at every such rank. -/
theorem exists_eventually_actualResponseRecipientAtom
    (compiled : FinFourMinimumResponseCompiledRectangle sequence) :
    ∃ recipient ∈ Finset.univ.erase compiled.packet.observer,
      0 < quittingTerminalSemanticDebtChange
        compiled.packet.endpointPoint.1
        compiled.packet.responsePoint.1 recipient ∧
      ∀ᶠ rank in atTop,
        quittingTerminalSemanticDebtChange
              compiled.packet.endpointPoint.1
              compiled.packet.responsePoint.1 recipient / 2 <
            quittingTerminalSemanticDebtChange
              (quittingTerminalSemanticPair reward
                (compiled.packet.endpointProfile
                  (compiled.packet.commonSubsequence rank)))
              (quittingTerminalSemanticPair reward
                (compiled.actualResponseProfile rank)) recipient ∧
          HasQuittingEndpointDebtRecipientAtom reward
            (compiled.packet.endpointProfile
              (compiled.packet.commonSubsequence rank))
            compiled.packet.observer recipient
            (quittingPureTimeBehaviorStrategy reward
              compiled.packet.observer
              (compiled.packet.responseChoice
                (compiled.packet.commonSubsequence rank))) := by
  obtain ⟨recipient, hrecipient, hpositive⟩ :=
    compiled.exists_responsePoint_positiveRecipient
  have hendpointPair :
      Tendsto
        (fun rank =>
          quittingTerminalSemanticPair reward
            (compiled.packet.endpointProfile
              (compiled.packet.commonSubsequence rank)))
        atTop (nhds compiled.packet.endpointPoint.1) := by
    have hprojection :=
      (continuous_fst.tendsto compiled.packet.endpointPoint).comp
        compiled.packet.endpoint_tendsto
    simpa only [Function.comp_def] using hprojection
  have hresponsePair :
      Tendsto
        (fun rank =>
          quittingTerminalSemanticPair reward
            (compiled.actualResponseProfile rank))
        atTop (nhds compiled.packet.responsePoint.1) := by
    have hprojection :=
      (continuous_fst.tendsto compiled.packet.responsePoint).comp
        compiled.packet.response_tendsto
    simpa only [actualResponseProfile, Function.comp_def] using hprojection
  have hendpointDebt :
      Tendsto
        (fun rank =>
          quittingTerminalSemanticDebt
            (quittingTerminalSemanticPair reward
              (compiled.packet.endpointProfile
                (compiled.packet.commonSubsequence rank))) recipient)
        atTop
        (nhds (quittingTerminalSemanticDebt
          compiled.packet.endpointPoint.1 recipient)) := by
    exact
      ((continuous_quittingTerminalSemanticDebt recipient).tendsto
        compiled.packet.endpointPoint.1).comp hendpointPair
  have hresponseDebt :
      Tendsto
        (fun rank =>
          quittingTerminalSemanticDebt
            (quittingTerminalSemanticPair reward
              (compiled.actualResponseProfile rank)) recipient)
        atTop
        (nhds (quittingTerminalSemanticDebt
          compiled.packet.responsePoint.1 recipient)) := by
    exact
      ((continuous_quittingTerminalSemanticDebt recipient).tendsto
        compiled.packet.responsePoint.1).comp hresponsePair
  have hchange :
      Tendsto
        (fun rank =>
          quittingTerminalSemanticDebtChange
            (quittingTerminalSemanticPair reward
              (compiled.packet.endpointProfile
                (compiled.packet.commonSubsequence rank)))
            (quittingTerminalSemanticPair reward
              (compiled.actualResponseProfile rank)) recipient)
        atTop
        (nhds (quittingTerminalSemanticDebtChange
          compiled.packet.endpointPoint.1
          compiled.packet.responsePoint.1 recipient)) := by
    simpa only [quittingTerminalSemanticDebtChange] using
      hresponseDebt.sub hendpointDebt
  have heventually :
      ∀ᶠ rank in atTop,
        quittingTerminalSemanticDebtChange
              compiled.packet.endpointPoint.1
              compiled.packet.responsePoint.1 recipient / 2 <
            quittingTerminalSemanticDebtChange
              (quittingTerminalSemanticPair reward
                (compiled.packet.endpointProfile
                  (compiled.packet.commonSubsequence rank)))
              (quittingTerminalSemanticPair reward
                (compiled.actualResponseProfile rank)) recipient :=
    hchange.eventually
      (Ioi_mem_nhds (half_lt_self hpositive))
  refine ⟨recipient, hrecipient, hpositive, ?_⟩
  filter_upwards [heventually] with rank hrise
  refine ⟨hrise, ?_⟩
  have hactualPositive :
      0 < quittingTerminalSemanticDebtChange
        (quittingTerminalSemanticPair reward
          (compiled.packet.endpointProfile
            (compiled.packet.commonSubsequence rank)))
        (quittingTerminalSemanticPair reward
          (compiled.actualResponseProfile rank)) recipient :=
    (half_pos hpositive).trans hrise
  simpa only [actualResponseProfile] using
    hasQuittingEndpointDebtRecipientAtom_of_pos reward
      (compiled.packet.endpointProfile
        (compiled.packet.commonSubsequence rank))
      compiled.packet.observer recipient
      (quittingPureTimeBehaviorStrategy reward compiled.packet.observer
        (compiled.packet.responseChoice
          (compiled.packet.commonSubsequence rank)))
      hactualPositive

end FinFourMinimumResponseCompiledRectangle

end GameTheory
