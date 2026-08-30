/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Research.Quitting.FinFourProducerAtlas.CanonicalPairRenewableSourceRank

/-!
# Renewable canonical Fin4 endpoint handoff

Umbrella for exact endpoint source regeneration, minimum-fibre child
regeneration, strict support descent, and the phase-tagged renewable rank.
The uncharged uniform comparison of every behavioral deviation gain across a
horizontal seam is impossible; a charged or centered compiler remains open.
Source-independent downstream conclusions do not require such a compiler.
-/

noncomputable section

namespace GameTheory

open Filter Math.Probability
open scoped Topology

variable
  {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
  {bound : ℝ}
  {source : FinFourMinimumAtomProducer reward bound}
  {returnSource :
    FinFourOwnerCompressedMinimumReturnForcedPairSource source}
  {lambda : ℝ}
  {packet : FinFourOwnerCompressedMinimumReturnForcedPairPacket
    returnSource lambda}

open FinFourOwnerCompressedMinimumReturnForcedPairPacket

namespace FinFourRenewableTrace

/-- A renewal trace exposes a terminal alternative at one of its
source-faithful descendant nodes. -/
theorem exists_terminalExit
    {node : FinFourRenewableMinimumSourceNode reward bound}
    (trace : FinFourRenewableTrace node) :
    ∃ terminalNode : FinFourRenewableMinimumSourceNode reward bound,
      FinFourRenewableTerminalExit terminalNode := by
  induction trace with
  | terminal terminalNode exit => exact ⟨terminalNode, exit⟩
  | descend _ _ _ ih => exact ih

/-- Eliminate a renewal trace into any source-independent proposition.  Since
`result` does not mention the current source node, no backward compiler across
any horizontal full-replacement seam is needed. -/
theorem consume
    {node : FinFourRenewableMinimumSourceNode reward bound}
    {result : Prop}
    (trace : FinFourRenewableTrace node)
    (consumeExit :
      ∀ terminalNode : FinFourRenewableMinimumSourceNode reward bound,
        FinFourRenewableTerminalExit terminalNode → result) :
    result := by
  obtain ⟨terminalNode, exit⟩ := trace.exists_terminalExit
  exact consumeExit terminalNode exit

end FinFourRenewableTrace

namespace FinFourOwnerCompressedMinimumReturnForcedPairPacket
namespace CanonicalPairMinimumEndpointSupportRankHandoff

/-- The original canonical endpoint itself carries the exact Fin4 horizontal
debt transfer: one nonpayer gains at least one third of the payer's positive
source debt. -/
theorem exists_other_endpointDebtIncrease_div_three
    (handoff : CanonicalPairMinimumEndpointSupportRankHandoff packet) :
    ∃ other, other ≠ packet.payer ∧
      0 < quittingTerminalSemanticDebt
          handoff.supportHandoff.sourceCluster packet.payer / 3 ∧
        quittingTerminalSemanticDebt
            handoff.supportHandoff.sourceCluster packet.payer / 3 ≤
          quittingTerminalSemanticDebtChange
            handoff.supportHandoff.sourceCluster
            handoff.supportHandoff.endpointCluster other := by
  have hsum :
      quittingTerminalSemanticDebtSum
          handoff.supportHandoff.endpointCluster =
        quittingTerminalSemanticDebtSum
          handoff.supportHandoff.sourceCluster := by
    rw [handoff.supportHandoff.endpoint_debtSum_eq_minimum,
      handoff.supportHandoff.source_debtSum_eq_minimum]
  have htransfer :=
    sum_opponent_debtChange_eq_totalChange_add_sourceDebt_of_target_zero
      handoff.supportHandoff.sourceCluster
      handoff.supportHandoff.endpointCluster packet.payer
      handoff.supportHandoff.endpoint_moverDebt_eq_zero
  rw [hsum, sub_self, zero_add] at htransfer
  obtain ⟨other, hother, hle⟩ :=
    exists_opponent_average_le_debtChange
      handoff.supportHandoff.sourceCluster
      handoff.supportHandoff.endpointCluster packet.payer
      handoff.supportHandoff.source_moverDebt_pos
      (le_of_eq htransfer.symm)
  have hcard : (((Finset.univ.erase packet.payer).card : ℕ) : ℝ) = 3 := by
    simp
  rw [hcard] at hle
  exact ⟨other, (Finset.mem_erase.mp hother).1,
    div_pos handoff.supportHandoff.source_moverDebt_pos (by norm_num), hle⟩

/-- The complete renewable construction reaches one of the three global
terminal alternatives after finitely many same-residual source regenerations. -/
theorem exists_renewalTerminalExit
    (handoff : CanonicalPairMinimumEndpointSupportRankHandoff packet) :
    ∃ terminalNode : FinFourRenewableMinimumSourceNode reward bound,
      FinFourRenewableTerminalExit terminalNode := by
  obtain ⟨certificate⟩ := handoff.nonempty_renewalCertificate
  exact certificate.trace.exists_terminalExit

/-- The terminal descendant retains the incoming canonical source's hard
residual literally. -/
theorem exists_renewalTerminalExit_sameResidual
    (handoff : CanonicalPairMinimumEndpointSupportRankHandoff packet) :
    ∃ terminalNode : FinFourRenewableMinimumSourceNode reward bound,
      FinFourRenewableTerminalExit terminalNode ∧
        terminalNode.source.residual = source.residual := by
  obtain ⟨certificate⟩ := handoff.nonempty_renewalCertificate
  exact certificate.exists_terminalExit_sameResidual

/-- A downstream conclusion that no longer mentions the local source can be
consumed at the terminal descendant.  Recursive composition therefore needs
no map transporting deviations back across earlier horizontal seams. -/
theorem consume_renewalTerminalExit
    (handoff : CanonicalPairMinimumEndpointSupportRankHandoff packet)
    {result : Prop}
    (consumeExit :
      ∀ terminalNode : FinFourRenewableMinimumSourceNode reward bound,
        FinFourRenewableTerminalExit terminalNode → result) :
    result := by
  obtain ⟨certificate⟩ := handoff.nonempty_renewalCertificate
  exact certificate.trace.consume consumeExit

/-- Route every terminal descendant through the existing global consumers.
The consumers act on a frontier of the same reward table, so this composition
uses no parent-source deviation comparison. -/
theorem exists_uniformEquilibriumPayoff_of_renewalExitConsumers
    (handoff : CanonicalPairMinimumEndpointSupportRankHandoff packet)
    (hpositiveSlope :
      ∀ (frontier : QuittingPositiveMinimumDebtTangentFamily reward),
        (∃ mover, 0 < ∑ observer, frontier.tangent mover observer) →
          ∀ eta : ℝ, 0 < eta →
            Nonempty (QuittingChronologicalDebtShadowingCertificate reward eta))
    (hsupportEntry :
      ∀ (frontier : QuittingPositiveMinimumDebtTangentFamily reward),
        HasQuittingStoppingLawFlatSupportEntry
          frontier.base frontier.positiveDebtSupport frontier.tangent →
          ∀ eta : ℝ, 0 < eta →
            Nonempty (QuittingChronologicalDebtShadowingCertificate reward eta))
    (hpaid : PaidFirstDisagreementUniformPayoffConsumer reward) :
    ∃ payoff : Payoff (Fin 4),
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff := by
  apply handoff.consume_renewalTerminalExit
  intro terminalNode exit
  rcases exit with hpositive | hentry | hpaidExit
  · exact
      quittingGame_exists_uniformEquilibriumPayoff_of_chronologicalDebtShadowing_all_errors
        reward (hpositiveSlope terminalNode.frontier hpositive)
  · exact
      quittingGame_exists_uniformEquilibriumPayoff_of_chronologicalDebtShadowing_all_errors
        reward (hsupportEntry terminalNode.frontier hentry.2)
  · obtain ⟨mover, endpoint, hseparated, observer, gain, hobserver,
        hgain, hrows⟩ := hpaidExit
    exact hpaid terminalNode.frontier mover endpoint hseparated
      observer gain hobserver hgain hrows

end CanonicalPairMinimumEndpointSupportRankHandoff
end FinFourOwnerCompressedMinimumReturnForcedPairPacket

end GameTheory
