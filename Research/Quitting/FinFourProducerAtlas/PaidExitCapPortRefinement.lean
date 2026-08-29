/-
Copyright (c) 2026 UniformEquilibrium contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: UniformEquilibrium contributors.
-/

import Research.Quitting.FinFourProducerAtlas.CanonicalPairMinimumEndpointRenewal
import Research.Quitting.PaidRowCapPortDispatch

/-!
# Refined paid exit of the renewable canonical endpoint handoff

The renewal trace reaches one of three terminal alternatives.  The
positive-slope and flat-support-entry alternatives are consumed by supplied
chronological debt-shadowing producers.  The off-minimum paid
first-disagreement alternative is not a terminal uniform-payoff exit: its paid
row lifts to a cap-lifted source with a summable port and enters the checked
charged near-return, quantitative debt descent, inert stall alternative, of
which only the charged near-return arm carries a uniform-equilibrium payoff.

The finite support rank therefore proves termination of the minimum-fibre
renewal lane, not global termination.  Quantitative debt descent is a
real-valued decrease of total terminal-semantic debt, with no regenerated
source and no well-founded rank, and inert stall is a literally all-Continue
cap lift.  Both survive as residual alternatives of the conclusion below.
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

namespace FinFourOwnerCompressedMinimumReturnForcedPairPacket
namespace CanonicalPairMinimumEndpointSupportRankHandoff

/-- Route the two chronological terminal descendants through their supplied
producers and the paid terminal descendant through its cap-lifted port.  The
conclusion is a uniform-equilibrium payoff, or else a frontier carrying an
off-minimum full-replacement cluster whose paid cap dispatch lands in
quantitative debt descent or inert stall.  No producer for either residual
alternative is supplied or constructed here. -/
theorem exists_uniformEquilibriumPayoff_or_paidCapPortOpenResidual
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
            Nonempty (QuittingChronologicalDebtShadowingCertificate reward eta)) :
    (∃ payoff : Payoff (Fin 4),
        (quittingGame reward).IsUniformEquilibriumPayoff none payoff) ∨
      ∃ (frontier : QuittingPositiveMinimumDebtTangentFamily reward)
        (mover : {who // who ∈ frontier.positiveDebtSupport})
        (endpoint : frontier.FullReplacementCluster mover),
        quittingTerminalSemanticDebtSum frontier.base <
            quittingTerminalSemanticDebtSum endpoint.cluster ∧
          endpoint.PaidCapPortDispatch (fun capSource port ↦
            capSource.QuantitativeDebtDescent port ∨
              capSource.InertStall port) := by
  apply handoff.consume_renewalTerminalExit
  intro terminalNode exit
  rcases exit with hpositive | hentry | hpaidExit
  · exact Or.inl
      (quittingGame_exists_uniformEquilibriumPayoff_of_chronologicalDebtShadowing_all_errors
        reward (hpositiveSlope terminalNode.frontier hpositive))
  · exact Or.inl
      (quittingGame_exists_uniformEquilibriumPayoff_of_chronologicalDebtShadowing_all_errors
        reward (hsupportEntry terminalNode.frontier hentry.2))
  · obtain ⟨mover, endpoint, hpaid⟩ := hpaidExit
    obtain ⟨hseparated, rank, observer, gain, row, capSource, port, hobserver,
        hgain, hminimum, hprofile, hobserverEq, hgainEq, halternative⟩ :=
      endpoint.separated_and_paidCapPortDispatch_of_offMinimumPaidFirstDisagreement
        hpaid
    rcases halternative with hcharged | hresidual
    · exact Or.inl hcharged.uniformEquilibriumPayoff
    · exact Or.inr ⟨terminalNode.frontier, mover, endpoint, hseparated, rank,
        observer, gain, row, capSource, port, hobserver, hgain, hminimum,
        hprofile, hobserverEq, hgainEq, hresidual⟩

end CanonicalPairMinimumEndpointSupportRankHandoff
end FinFourOwnerCompressedMinimumReturnForcedPairPacket

end GameTheory
