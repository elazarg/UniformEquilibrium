/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.UniformExistenceBoundary
import UniformEquilibrium.Quitting.Projective.PunishmentFloorNearReturn

/-!
# Paid-row payoff-near-return consumer

The paid first-disagreement source telescope need not produce an exact return
to a complete punishment-floor state.  It is enough to fix one positive
charge threshold and, at every endpoint tolerance, produce an exact
floor-admissible path containing an edge above that threshold whose endpoint
payoffs are close.  The path, endpoints, and charged edge may vary with the
tolerance.  Stored root coordinates need not recur.

A fixed positive edge whose tail payoff lies in the payoff closure of states
reachable from its current state is retained as a stronger specialization.

This module weakens only the output expected from the paid-row producer.  It
does not construct any charged payoff near-return from a paid row.
-/

noncomputable section

namespace GameTheory

open Filter Math.Probability
open scoped Topology

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}

/-- One fixed positive admissible edge together with arbitrary-accuracy
payoff closure from its current state back toward its tail payoff. -/
structure QuittingPositiveAdmissiblePayoffClosure
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) where
  edge : QuittingPunishmentFloorAdmissibleEdge reward
  charge_pos : 0 < edge.toBoxEdge.absorptionCharge
  closure : ∀ endpointError : ℝ, 0 < endpointError →
    ∃ (target : QuittingPunishmentFloorAdmissibleState reward)
      (_path : (quittingPunishmentFloorAdmissibleChargedRelation reward).Path
        edge.current target),
      ∀ who,
        |edge.tail.1.1.1 who - target.1.1.1 who| ≤ endpointError

/-- Fixed-edge payoff closure specializes to the varying-edge near-return
family by prepending the same edge at every tolerance. -/
def QuittingPositiveAdmissiblePayoffClosure.toPayoffNearReturnFamily
    (result : QuittingPositiveAdmissiblePayoffClosure reward) :
    QuittingPositiveAdmissiblePayoffNearReturnFamily reward :=
  QuittingPositiveAdmissiblePayoffNearReturnFamily.ofPositiveEdgePayoffClosure
    result.edge result.charge_pos result.closure

/-- The checked payoff-closure consumer. -/
theorem QuittingPositiveAdmissiblePayoffClosure.exists_uniformEquilibriumPayoff
    (result : QuittingPositiveAdmissiblePayoffClosure reward) :
    ∃ payoff : Payoff ι,
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff :=
  result.toPayoffNearReturnFamily.exists_uniformEquilibriumPayoff

/-- The paid-row source telescope with the primary, varying-edge payoff
near-return output.  One positive charge threshold is fixed inside each
output family, while its source, target, path, and charged edge may depend on
the endpoint tolerance. -/
def PaidFirstDisagreementAdmissiblePayoffNearReturnConsumer
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) : Prop :=
  ∀ (frontier : QuittingPositiveMinimumDebtTangentFamily reward)
      (mover : {who // who ∈ frontier.positiveDebtSupport})
      (endpoint :
        QuittingPositiveMinimumDebtTangentFamily.FullReplacementCluster
          frontier mover),
    quittingTerminalSemanticDebtSum frontier.base <
        quittingTerminalSemanticDebtSum endpoint.cluster →
      ∀ observer gain, observer ≠ mover.1 → 0 < gain →
        (∀ᶠ rank in atTop,
          Nonempty (QuittingPaidFirstDisagreementRow reward
            (frontier.fullReplacementProfile mover (endpoint.subseq rank))
            observer gain)) →
        Nonempty (QuittingPositiveAdmissiblePayoffNearReturnFamily reward)

/-- The paid-row source quantifiers are unchanged from the exact-return
consumer, but their output is weakened to payoff closure around one fixed
positive admissible edge. -/
def PaidFirstDisagreementAdmissiblePayoffClosureConsumer
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) : Prop :=
  ∀ (frontier : QuittingPositiveMinimumDebtTangentFamily reward)
      (mover : {who // who ∈ frontier.positiveDebtSupport})
      (endpoint :
        QuittingPositiveMinimumDebtTangentFamily.FullReplacementCluster
          frontier mover),
    quittingTerminalSemanticDebtSum frontier.base <
        quittingTerminalSemanticDebtSum endpoint.cluster →
      ∀ observer gain, observer ≠ mover.1 → 0 < gain →
        (∀ᶠ rank in atTop,
          Nonempty (QuittingPaidFirstDisagreementRow reward
            (frontier.fullReplacementProfile mover (endpoint.subseq rank))
            observer gain)) →
        Nonempty (QuittingPositiveAdmissiblePayoffClosure reward)

/-- Fixed-edge payoff closure is a specialization of the primary varying-edge
paid-row output. -/
theorem paidFirstDisagreementAdmissiblePayoffNearReturnConsumer_of_payoffClosure
    (hconsumer :
      PaidFirstDisagreementAdmissiblePayoffClosureConsumer reward) :
    PaidFirstDisagreementAdmissiblePayoffNearReturnConsumer reward := by
  intro frontier mover endpoint hseparated observer gain hobserver hgain hrows
  obtain ⟨result⟩ := hconsumer frontier mover endpoint hseparated
    observer gain hobserver hgain hrows
  exact ⟨result.toPayoffNearReturnFamily⟩

/-- A paid-row varying-edge near-return consumer supplies the generic paid-row
uniform-payoff output. -/
theorem paidFirstDisagreementUniformPayoffConsumer_of_admissiblePayoffNearReturn
    (hconsumer :
      PaidFirstDisagreementAdmissiblePayoffNearReturnConsumer reward) :
    PaidFirstDisagreementUniformPayoffConsumer reward := by
  intro frontier mover endpoint hseparated observer gain hobserver hgain hrows
  obtain ⟨result⟩ := hconsumer frontier mover endpoint hseparated
    observer gain hobserver hgain hrows
  exact result.exists_uniformEquilibriumPayoff

/-- A paid-row payoff-closure consumer supplies the generic paid-row uniform
payoff output through its varying-edge specialization. -/
theorem paidFirstDisagreementUniformPayoffConsumer_of_admissiblePayoffClosure
    (hconsumer :
      PaidFirstDisagreementAdmissiblePayoffClosureConsumer reward) :
    PaidFirstDisagreementUniformPayoffConsumer reward :=
  paidFirstDisagreementUniformPayoffConsumer_of_admissiblePayoffNearReturn
    (paidFirstDisagreementAdmissiblePayoffNearReturnConsumer_of_payoffClosure
      hconsumer)

/-- **Primary four-exit payoff-near-return capstone.**  The first three
chronological hypotheses are unchanged.  In the paid branch the positive
charge threshold is fixed, but the charged edge and both endpoint states may
vary with the endpoint tolerance. -/
theorem exists_uniformEquilibriumPayoff_of_finiteSupportRankExitPayoffNearReturnConsumers
    [Nonempty ι]
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
    (hcirculation :
      ∀ (frontier : QuittingPositiveMinimumDebtTangentFamily reward),
        HasQuittingStoppingLawFlatChargedCirculation
          frontier.positiveDebtSupport frontier.tangent →
          ∀ eta : ℝ, 0 < eta →
            Nonempty (QuittingChronologicalDebtShadowingCertificate reward eta))
    (hpaid : PaidFirstDisagreementAdmissiblePayoffNearReturnConsumer reward) :
    ∃ payoff : Payoff ι,
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff := by
  exact
    exists_uniformEquilibriumPayoff_of_finiteSupportRankExitUniformPayoffConsumers
      hpositiveSlope hsupportEntry hcirculation
      (paidFirstDisagreementUniformPayoffConsumer_of_admissiblePayoffNearReturn
        hpaid)

/-- **Four-exit payoff-closure capstone.**  The first three chronological
hypotheses are unchanged.  The paid branch needs only one fixed positive edge
and arbitrary-accuracy payoff closure, rather than a return to the full tail
state. -/
theorem exists_uniformEquilibriumPayoff_of_finiteSupportRankExitPayoffClosureConsumers
    [Nonempty ι]
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
    (hcirculation :
      ∀ (frontier : QuittingPositiveMinimumDebtTangentFamily reward),
        HasQuittingStoppingLawFlatChargedCirculation
          frontier.positiveDebtSupport frontier.tangent →
          ∀ eta : ℝ, 0 < eta →
            Nonempty (QuittingChronologicalDebtShadowingCertificate reward eta))
    (hpaid : PaidFirstDisagreementAdmissiblePayoffClosureConsumer reward) :
    ∃ payoff : Payoff ι,
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff := by
  exact
    exists_uniformEquilibriumPayoff_of_finiteSupportRankExitPayoffNearReturnConsumers
      hpositiveSlope hsupportEntry hcirculation
      (paidFirstDisagreementAdmissiblePayoffNearReturnConsumer_of_payoffClosure
        hpaid)

end GameTheory
