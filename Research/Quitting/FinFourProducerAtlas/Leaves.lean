/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Research.Quitting.FinFourProducerAtlas.Source

/-!
# Finite source-distinct leaves of the exhaustive Fin4 atlas

The low-tail producer terminates in a singleton or a simple endpoint cycle.
All leaves retain the literal source path used to reach them.
-/

noncomputable section

namespace GameTheory

open Filter Math.Probability Math.PMFProduct
open MathUE.FiniteBooleanEndpointOrbit
open QuittingNonsingletonMinimumLawTransfer

/-- A singleton reached at a terminal vertex of the finite endpoint orbit. -/
structure FinFourTerminalSingletonProducer
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    {bound : ℝ} (source : FinFourMinimumAtomProducer reward bound) where
  purification : FinFourTotalPurificationProducer source
  orbit : DispatchedOrbit
    (QuittingSameStageSingletonRoute reward purification.profile
      purification.low.stage)
    (fun start target => Nonempty
      (QuittingSameStageEndpointEdge reward purification.profile
        purification.low.stage source.point.1 purification.low.lambda start target))
    purification.finalState.coalition

/-- The complete literal source of a simple same-stage endpoint cycle. -/
structure FinFourMonodromyProducer
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    {bound : ℝ} (source : FinFourMinimumAtomProducer reward bound) where
  purification : FinFourTotalPurificationProducer source
  trace : DispatchedClosedSegment
    (QuittingSameStageSingletonRoute reward purification.profile
      purification.low.stage)
    (fun start target => Nonempty
      (QuittingSameStageEndpointEdge reward purification.profile
        purification.low.stage source.point.1 purification.low.lambda start target))
    purification.finalState.coalition
  period_le_eight : trace.segment.segment.period ≤ 8
  stage_mass_floor : ∀ offset : Fin trace.segment.segment.period,
    purification.low.lambda ≤ quittingStageCoalitionMass reward
      (quittingLiteralPureRootCoalitionProfile reward purification.profile
        purification.low.stage
        (trace.orbit (trace.segment.segment.start + offset)))
      purification.low.stage
      (quittingTerminalOfNonsingletonCoalition
        (trace.orbit (trace.segment.segment.start + offset)))
  edge_certificate : ∀ offset : Fin trace.segment.segment.period,
    ∃ edge : QuittingSameStageEndpointEdge reward purification.profile
        purification.low.stage source.point.1 purification.low.lambda
        (trace.orbit (trace.segment.segment.start + offset))
        (trace.orbit (trace.segment.segment.start + offset + 1)),
      edge.action = quittingRootBestEndpointAction reward
          (quittingTerminalSemanticPair reward
            (quittingAllContinueProfileSpine reward
              (quittingLiteralPureRootCoalitionProfile reward purification.profile
                purification.low.stage
                (trace.orbit (trace.segment.segment.start + offset)))
              (purification.low.stage + 1))).1
          (quittingProfileLiveRoot reward
            (quittingLiteralPureRootCoalitionProfile reward purification.profile
              purification.low.stage
              (trace.orbit (trace.segment.segment.start + offset)))
            purification.low.stage)
          edge.who ∧
        0 < quittingSameStageCoalitionGain reward purification.profile
          purification.low.stage
          (trace.orbit (trace.segment.segment.start + offset))
          edge.who edge.action ∧
        purification.low.lambda *
              quittingTerminalSemanticDebtSum source.point.1 / 8 ≤
          quittingSameStageCoalitionGain reward purification.profile
            purification.low.stage
            (trace.orbit (trace.segment.segment.start + offset))
            edge.who edge.action

/-- Common-host geometry for a literal simple endpoint cycle. -/
structure FinFourCommonHostMonodromyProducer
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    {bound : ℝ} (source : FinFourMinimumAtomProducer reward bound) where
  monodromy : FinFourMonodromyProducer source
  host : Fin 4
  host_mem : ∀ offset : Fin monodromy.trace.segment.segment.period,
    host ∈ (monodromy.trace.orbit
      (monodromy.trace.segment.segment.start + offset)).1

/-- Complementary-pair geometry for a literal simple endpoint cycle. -/
structure FinFourComplementaryPairMonodromyProducer
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    {bound : ℝ} (source : FinFourMinimumAtomProducer reward bound) where
  monodromy : FinFourMonodromyProducer source
  first : Fin monodromy.trace.segment.segment.period
  second : Fin monodromy.trace.segment.segment.period
  first_card :
    (monodromy.trace.orbit
      (monodromy.trace.segment.segment.start + first)).1.card = 2
  second_card :
    (monodromy.trace.orbit
      (monodromy.trace.segment.segment.start + second)).1.card = 2
  disjoint : Disjoint
    (monodromy.trace.orbit
      (monodromy.trace.segment.segment.start + first)).1
    (monodromy.trace.orbit
      (monodromy.trace.segment.segment.start + second)).1
  complementary :
    (monodromy.trace.orbit
      (monodromy.trace.segment.segment.start + second)).1 =
      (monodromy.trace.orbit
        (monodromy.trace.segment.segment.start + first)).1ᶜ

/-- The finite natural producer modes.  The three ways of reaching a singleton
share one completion mode but remain separate constructors so their literal
sources are not identified. -/
inductive FinFourProducerResidual
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (bound : ℝ) : Type
  | minimumSingleton
      (source : FinFourMinimumAtomProducer reward bound)
      (terminal_card : source.atom.terminal.val.card = 1)
  | purifiedSingleton
      (source : FinFourMinimumAtomProducer reward bound)
      (producer : FinFourPurifiedSingletonProducer source)
  | terminalSingleton
      (source : FinFourMinimumAtomProducer reward bound)
      (producer : FinFourTerminalSingletonProducer source)
  | tailEscape
      (source : FinFourMinimumAtomProducer reward bound)
      (producer : TailEscapeSubsequence reward source.point source.atom)
  | commonHostMonodromy
      (source : FinFourMinimumAtomProducer reward bound)
      (producer : FinFourCommonHostMonodromyProducer source)
  | complementaryPairMonodromy
      (source : FinFourMinimumAtomProducer reward bound)
      (producer : FinFourComplementaryPairMonodromyProducer source)

/-- Four completion contracts, with all singleton origins merged only at the
obligation level. -/
inductive FinFourProducerCompletionContract
  | singletonTerminalApproximationOrRegeneration
  | escapedTailChargeOrRegeneration
  | commonHostNonlocalReturnOrRegeneration
  | complementaryPairNonlocalReturnOrRegeneration
  deriving DecidableEq

/-- Every atlas leaf has exactly one conjecture-facing completion contract. -/
def FinFourProducerResidual.completionContract
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    {bound : ℝ} : FinFourProducerResidual reward bound →
      FinFourProducerCompletionContract
  | .minimumSingleton .. => .singletonTerminalApproximationOrRegeneration
  | .purifiedSingleton .. => .singletonTerminalApproximationOrRegeneration
  | .terminalSingleton .. => .singletonTerminalApproximationOrRegeneration
  | .tailEscape .. => .escapedTailChargeOrRegeneration
  | .commonHostMonodromy .. => .commonHostNonlocalReturnOrRegeneration
  | .complementaryPairMonodromy .. =>
      .complementaryPairNonlocalReturnOrRegeneration

end GameTheory
