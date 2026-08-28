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
The stronger horizontal-seam backward compiler remains an explicit open
condition, but source-independent downstream conclusions do not require it.
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

/-- The complete renewable construction reaches one of the three global
terminal alternatives after finitely many same-residual source regenerations. -/
theorem exists_renewalTerminalExit
    (handoff : CanonicalPairMinimumEndpointSupportRankHandoff packet) :
    ∃ terminalNode : FinFourRenewableMinimumSourceNode reward bound,
      FinFourRenewableTerminalExit terminalNode := by
  obtain ⟨certificate⟩ := handoff.nonempty_renewalCertificate
  exact certificate.trace.exists_terminalExit

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
