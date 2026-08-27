/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors.
-/

import Research.Quitting.FinFourProducerAtlas.Coverage
import Research.Quitting.FinFourProducerAtlas.SemanticConnections
import
  UniformEquilibrium.Diagnostics.Quitting.Collision.SingletonPacket.PairBasePaidCapSemanticDispatch

/-!
# Semantic coverage for the Fin4 producer atlas

The six source-distinct atlas leaves first normalize to four semantically
directed nodes.  Owner-clock compression additionally merges the diffuse
minimum-singleton node into a weaker concentrated-singleton core, leaving
three directed obligations.  This is still producer coverage, not a
completion theorem for any node.

The optional complementary-pair bridge below reuses only one displayed pair as
a prescribed label for the production paid-cap dispatch.  That dispatch
reselects its semantic minimum, stationary source, paid row, and cap chronology;
it does not preserve the atlas monodromy or use its dynamic edge data.
-/

noncomputable section

namespace GameTheory

/-- Global four-player coverage: either the existing uniform-payoff arm holds,
or the same reward table produces one of the four directed atlas nodes. -/
theorem uniformPayoff_or_nonempty_finFourAtlasDirectedNode
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    {bound : ℝ} (hreward : ∀ terminal who, |reward terminal who| ≤ bound) :
    (∃ payoff : Payoff (Fin 4),
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff) ∨
      Nonempty (FinFourAtlasDirectedNode reward bound) := by
  rcases uniformPayoff_or_nonempty_finFourProducerResidual reward hreward with
    hpayoff | hresidual
  · exact Or.inl hpayoff
  · obtain ⟨residual⟩ := hresidual
    exact Or.inr residual.nonempty_directedNode

/-- Global three-obligation coverage after owner-clock compression: either
the existing uniform-payoff arm holds, or the same reward table produces a
clock-compressed concentrated singleton, a tail escape, or a monodromy node.
This does not consume any of the three obligations. -/
theorem uniformPayoff_or_nonempty_finFourAtlasClockCompressedDirectedNode
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    {bound : ℝ} (hreward : ∀ terminal who, |reward terminal who| ≤ bound) :
    (∃ payoff : Payoff (Fin 4),
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff) ∨
      Nonempty (FinFourAtlasClockCompressedDirectedNode reward bound) := by
  rcases uniformPayoff_or_nonempty_finFourProducerResidual reward hreward with
    hpayoff | hresidual
  · exact Or.inl hpayoff
  · obtain ⟨residual⟩ := hresidual
    exact Or.inr residual.nonempty_clockCompressedDirectedNode

namespace FinFourComplementaryPairMonodromyProducer

variable
  {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
  {bound : ℝ} {source : FinFourMinimumAtomProducer reward bound}

/-- Reuse the first displayed complementary-pair coalition only as the
prescribed base label of the production paid-cap dispatch.  The dispatch
freshly selects its semantic source and chronology; it neither preserves the
producer's monodromy nor consumes its edge certificates. -/
theorem nonempty_prescribedPairPaidCapSemanticDispatch_reselectingSource
    (producer : FinFourComplementaryPairMonodromyProducer source) :
    Nonempty (FinFourPairBasePaidCapSemanticDispatch reward
      source.residual.witness
      (producer.monodromy.cycleCoalition producer.first)) := by
  apply source.residual.nonempty_pairBasePaidCapSemanticDispatch
  exact producer.first_card

end FinFourComplementaryPairMonodromyProducer

end GameTheory
