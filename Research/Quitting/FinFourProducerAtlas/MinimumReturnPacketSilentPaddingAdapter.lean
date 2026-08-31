import UniformEquilibrium.Diagnostics.Quitting.MinimumTailSilentPaddingConsumer
import Research.Quitting.FinFourProducerAtlas.SourcePreservingCompletionConsumers

/-!
# Minimum-return packet adapter for literal silent-padding tails

This Research-only adapter forgets the atlas labels and retains exactly the
literal post-date profiles, their minimum-debt convergence, and the hard
residual needed by the production-shaped compactification contract.
-/

noncomputable section

namespace GameTheory

open Filter
open scoped Topology

variable {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
variable {bound : ℝ}
variable {source : FinFourMinimumAtomProducer reward bound}
variable {entrance : FinFourSourcePreservingSingletonEntrance source}
variable {parent : FinFourSourcePreservingCofinalSingletonPacket entrance}

namespace FinFourMinimumReturnPacket

/-- The literal post-date behavioral profile retained by one minimum-return
row. -/
def silentPaddingTailProfile
    (packet : FinFourMinimumReturnPacket parent) (rank : ℕ) :
    (quittingGame reward).BehaviorProfile :=
  quittingAllContinueProfileSpine reward
    (packet.stream.row rank).packet.forcedAdapter.targetProfile
      ((packet.stream.frame rank).stage + 1)

/-- The literal post-date profile has exactly the stored minimum-return tail
semantic pair. -/
theorem semanticPair_silentPaddingTailProfile_eq_tail
    (packet : FinFourMinimumReturnPacket parent) (rank : ℕ) :
    quittingTerminalSemanticPair reward
        (packet.silentPaddingTailProfile rank) = packet.stream.tail rank :=
  packet.forcedPairTail_eq_tail rank

/-- Forget the atlas labels while retaining the same literal profile sequence,
minimum provenance, and quantitative hard residual. -/
def silentPaddingTailProfileSource
    (packet : FinFourMinimumReturnPacket parent) :
    FinFourHardResidualMinimumTailProfileSource reward bound where
  residual := source.residual
  tailSource := {
    profiles := packet.silentPaddingTailProfile
    minimum := source.point.1
    minimum_mem := source.semantic_mem
    minimum_global := source.minimum
    minimumDebt_pos := source.minimumDebt_pos
    debt_tendsto := by
      apply packet.tailDebt_tendsto_minimum.congr'
      filter_upwards [] with rank
      exact congrArg quittingTerminalSemanticDebtSum
        (packet.semanticPair_silentPaddingTailProfile_eq_tail rank).symm }

/-- The literal minimum-return tail sequence has a joint compactification with
a fixed positive finite-law atom. -/
theorem nonempty_silentPaddingTailFiniteAtomCompactification
    (packet : FinFourMinimumReturnPacket parent) :
    Nonempty (FinFourMinimumTailFiniteAtomCompactification
      packet.silentPaddingTailProfileSource) :=
  packet.silentPaddingTailProfileSource.nonempty_finiteAtomCompactification

/-- One fixed positive atom of the same compactified minimum-return tail
sequence supplies the exact silent-padding block and its checked alternative
at every sufficiently late retained rank. -/
theorem exists_finiteAtomCompactification_eventually_silentPaddingTwoCutRealization
    (packet : FinFourMinimumReturnPacket parent) :
    ∃ compactification : FinFourMinimumTailFiniteAtomCompactification
        packet.silentPaddingTailProfileSource,
      ∀ᶠ rank in atTop, Nonempty (FinFourSilentPaddingTwoCutRealization
        reward (compactification.retainedProfile rank)
          compactification.terminal
          (compactification.compactification.point.2
            (some compactification.terminal) / 2)
          compactification.compactification.point.1) := by
  obtain ⟨compactification⟩ :=
    packet.nonempty_silentPaddingTailFiniteAtomCompactification
  have hthreshold : 0 < compactification.compactification.point.2
      (some compactification.terminal) / 2 := by
    linarith [compactification.terminalMass_pos]
  have hthreshold_lt : compactification.compactification.point.2
        (some compactification.terminal) / 2 <
      compactification.compactification.point.2
        (some compactification.terminal) := by
    linarith [compactification.terminalMass_pos]
  exact ⟨compactification,
    compactification.eventually_nonempty_silentPaddingTwoCutRealization
      hthreshold hthreshold_lt⟩

end FinFourMinimumReturnPacket

end GameTheory
