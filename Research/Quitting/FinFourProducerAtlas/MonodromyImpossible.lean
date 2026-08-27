/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors.
-/

import Research.Quitting.FinFourProducerAtlas.Coverage
import Research.Quitting.SameStageEndpointMonodromyImpossible

/-!
# Impossibility of the Fin4 producer-atlas monodromy leaf

The neutral same-stage module rules out every dispatched closed segment on an
effective support of at most four players.  This module applies that theorem
to the two producer-atlas monodromy tags and contracts the six-tag residual to
its four nonmonodromy constructors.  The source, reward table, minimum point,
and every surviving witness remain unchanged.
-/

noncomputable section

namespace GameTheory

open QuittingNonsingletonMinimumLawTransfer

namespace FinFourMonodromyProducer

variable
  {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
  {bound : ℝ} {source : FinFourMinimumAtomProducer reward bound}

/-- The dispatched trace stored by a Fin4 monodromy producer is internally
inconsistent.  No source property or quantitative scale field is used. -/
theorem false (producer : FinFourMonodromyProducer source) : False :=
  not_nonempty_finFourSameStageEndpointClosedSegment ⟨producer.trace⟩

end FinFourMonodromyProducer

/-- The exact source-indexed monodromy leaf is empty for arbitrary reward and
bound data. -/
theorem not_nonempty_finFourMonodromyProducer
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (bound : ℝ) (source : FinFourMinimumAtomProducer reward bound) :
    ¬Nonempty (FinFourMonodromyProducer source) := by
  rintro ⟨producer⟩
  exact producer.false

/-- The common-host refinement is empty by projection to its monodromy
producer. -/
theorem not_nonempty_finFourCommonHostMonodromyProducer
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (bound : ℝ) (source : FinFourMinimumAtomProducer reward bound) :
    ¬Nonempty (FinFourCommonHostMonodromyProducer source) := by
  rintro ⟨producer⟩
  exact producer.monodromy.false

/-- The complementary-pair refinement is empty by projection to its monodromy
producer. -/
theorem not_nonempty_finFourComplementaryPairMonodromyProducer
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (bound : ℝ) (source : FinFourMinimumAtomProducer reward bound) :
    ¬Nonempty (FinFourComplementaryPairMonodromyProducer source) := by
  rintro ⟨producer⟩
  exact producer.monodromy.false

namespace FinFourLowTailRow

variable
  {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
  {bound : ℝ} {source : FinFourMinimumAtomProducer reward bound}

/-- Eliminating both impossible monodromy refinements contracts the low-row
dispatch to its two genuine singleton outputs. -/
theorem nonempty_singleton_leaf (low : FinFourLowTailRow source) :
    Nonempty (FinFourPurifiedSingletonProducer source) ∨
      Nonempty (FinFourTerminalSingletonProducer source) := by
  rcases low.nonempty_leaf with purified | terminal | common | complementary
  · exact Or.inl purified
  · exact Or.inr terminal
  · exact False.elim
      (not_nonempty_finFourCommonHostMonodromyProducer reward bound source common)
  · exact False.elim
      (not_nonempty_finFourComplementaryPairMonodromyProducer
        reward bound source complementary)

end FinFourLowTailRow

/-- The four atlas modes left after eliminating both monodromy constructors.
This retains each original source and producer without identifying the three
ways of reaching singleton data. -/
inductive FinFourProducerResidualWithoutMonodromy
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

/-- Eliminate the impossible constructors of an existing six-tag residual,
without reselecting its source or changing any surviving witness. -/
def FinFourProducerResidual.withoutMonodromy
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    {bound : ℝ} : FinFourProducerResidual reward bound →
      FinFourProducerResidualWithoutMonodromy reward bound
  | .minimumSingleton source terminalCard =>
      .minimumSingleton source terminalCard
  | .purifiedSingleton source producer => .purifiedSingleton source producer
  | .terminalSingleton source producer => .terminalSingleton source producer
  | .tailEscape source producer => .tailEscape source producer
  | .commonHostMonodromy _ producer => False.elim producer.monodromy.false
  | .complementaryPairMonodromy _ producer =>
      False.elim producer.monodromy.false

/-- A hard residual therefore produces one of the four monodromy-free tagged
leaves. -/
theorem nonempty_finFourProducerResidualWithoutMonodromy_of_hardResidual
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (bound : ℝ)
    (residual : FinFourQuantitativeFullSupportHardResidual reward bound) :
    Nonempty (FinFourProducerResidualWithoutMonodromy reward bound) := by
  obtain ⟨producer⟩ :=
    nonempty_finFourProducerResidual_of_hardResidual reward bound residual
  exact ⟨producer.withoutMonodromy⟩

/-- Global bounded-data coverage with the two impossible monodromy tags
removed.  The uniform-payoff arm is unchanged. -/
theorem uniformPayoff_or_nonempty_finFourProducerResidualWithoutMonodromy
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    {bound : ℝ} (hreward : ∀ terminal who, |reward terminal who| ≤ bound) :
    (∃ payoff : Payoff (Fin 4),
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff) ∨
      Nonempty (FinFourProducerResidualWithoutMonodromy reward bound) := by
  rcases uniformPayoff_or_nonempty_finFourProducerResidual reward hreward with
    hpayoff | hresidual
  · exact Or.inl hpayoff
  · obtain ⟨residual⟩ := hresidual
    exact Or.inr ⟨residual.withoutMonodromy⟩

end GameTheory
