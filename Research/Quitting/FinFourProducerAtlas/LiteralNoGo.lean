/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Research.Quitting.FinFourProducerAtlas.Leaves
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticLiteralSourceReturnNoGo

/-!
# Literal local-exactification no-go on Fin4 monodromy leaves

Every positive same-stage edge in a monodromy leaf violates the complete
root-and-tail-preserving exact Nash--Bellman embedding contract. This is a
local obstruction on the displayed edge, not a semantic consumer of the
monodromy leaf.
-/

noncomputable section

namespace GameTheory

open Math.Probability Math.PMFProduct
open MathUE.FiniteBooleanEndpointOrbit

/-- A checked same-stage positive edge gives the literal packet consumed by
the root--tail exactification no-go. -/
def QuittingSameStageEndpointEdge.literalPositiveActualRowPacket
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    {profile : (quittingGame reward).BehaviorProfile}
    {stage : ℕ} {minimum : QuittingTerminalSemanticPair (Fin 4)}
    {lambda : ℝ} {start target : QuittingNonsingletonCoalition (Fin 4)}
    (edge : QuittingSameStageEndpointEdge reward profile stage minimum lambda
      start target)
    (mass_pos : 0 < quittingStageCoalitionMass reward
      (quittingLiteralPureRootCoalitionProfile reward profile stage start) stage
      (quittingTerminalOfNonsingletonCoalition start)) :
    QuittingLiteralPositiveActualRowPacket reward := by
  let sourceProfile :=
    quittingLiteralPureRootCoalitionProfile reward profile stage start
  refine {
    profile := sourceProfile
    stage := stage
    who := edge.who
    terminal := quittingTerminalOfNonsingletonCoalition start
    mass := quittingStageCoalitionMass reward sourceProfile stage
      (quittingTerminalOfNonsingletonCoalition start)
    mass_eq := rfl
    mass_pos := mass_pos
    gain_pos := ?_
  }
  dsimp only [quittingLiteralActualRowBestEndpointGain,
    quittingLiteralActualRowTail, quittingLiteralActualRowRoot]
  rw [← edge.action_eq_best]
  rw [← quittingTerminalPayoff_literalOneDateProfile_eq_canonical
    reward sourceProfile edge.who stage edge.action]
  simpa only [quittingSameStageCoalitionGain, sourceProfile] using edge.gain_pos

/-- Every edge of a monodromy leaf excludes the complete local
root-and-tail-preserving exact Nash--Bellman arm. -/
theorem FinFourMonodromyProducer.every_edge_no_literalExactification
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    {bound : ℝ} {source : FinFourMinimumAtomProducer reward bound}
    (producer : FinFourMonodromyProducer source)
    (offset : Fin producer.trace.segment.segment.period) :
    ∃ edge : QuittingSameStageEndpointEdge reward producer.purification.profile
        producer.purification.low.stage source.point.1
        producer.purification.low.lambda
        (producer.trace.orbit (producer.trace.segment.segment.start + offset))
        (producer.trace.orbit
          (producer.trace.segment.segment.start + offset + 1)),
      let packet := edge.literalPositiveActualRowPacket
        ((producer.purification.low.lambda_pos).trans_le
          (producer.stage_mass_floor offset))
      ¬ ∃ current tail : QuittingNashBellmanPoint (Fin 4),
        packet.IsLiteralNashBellmanEmbedding current tail := by
  obtain ⟨edge, _haction, _hgain, _hfloor⟩ := producer.edge_certificate offset
  refine ⟨edge, ?_⟩
  exact (edge.literalPositiveActualRowPacket
    ((producer.purification.low.lambda_pos).trans_le
      (producer.stage_mass_floor offset))).not_exists_literalNashBellmanEmbedding

end GameTheory
