/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors.
-/

import Research.Quitting.CausalTailEscapeMaxAbsorptionCore
import Research.Quitting.FixedPairMinimumTailNormalizedReturn
import Research.Quitting.FinFourProducerAtlas.SourcePreservingCompletionAtlas
import Research.Quitting.FinFourProducerAtlas.ThreeRoleRegeneration

/-!
# Exact semantic consumers for source-preserving completion modes

Uniform escape feeds one literal retained tail to the maximal-absorption
same-tail return/undercharge theorem.  Minimum return feeds the stabilized
forced-pair rows to the source-independent decorated-family compactifier.

Both adapters retain their complete incoming packets.  In particular the
entrance, residual, source chronology, behavioral spines, semantic tails, and
outcome laws are not reconstructed from carrier membership.  Neither result
is a uniform-equilibrium theorem.
-/

noncomputable section

namespace GameTheory

open Filter Set Math.Probability Math.PMFProduct
open scoped Topology

variable {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
variable {bound : ℝ}
variable {source : FinFourMinimumAtomProducer reward bound}
variable {entrance : FinFourSourcePreservingSingletonEntrance source}
variable {parent : FinFourSourcePreservingCofinalSingletonPacket entrance}

namespace FinFourUniformEscapePacket

/-- The literal post-date continuation profile behind one semantic tail. -/
def continuationProfile
    (packet : FinFourUniformEscapePacket parent) (rank : ℕ) :
    (quittingGame reward).BehaviorProfile :=
  quittingAllContinueProfileSpine reward (packet.stream.frame rank).targetProfile
    ((packet.stream.frame rank).stage + 1)

/-- The continuation profile denotes exactly the stored collision tail. -/
theorem semanticPair_continuationProfile_eq_tail
    (packet : FinFourUniformEscapePacket parent) (rank : ℕ) :
    quittingTerminalSemanticPair reward (packet.continuationProfile rank) =
      packet.stream.tail rank :=
  (packet.stream.tail_eq_framePostDateTail rank).symm

/-- Its complete terminal outcome law remains the literal reference law. -/
theorem continuationProfile_outcomeLaw_eq_reference
    (packet : FinFourUniformEscapePacket parent) (rank : ℕ) :
    quittingTerminalOutcomeMass reward (packet.continuationProfile rank) =
      quittingTerminalOutcomeMass reward
        (quittingAllContinueProfileSpine reward
          (packet.stream.frame rank).referenceProfile
            ((packet.stream.frame rank).stage + 1)) := by
  rw [continuationProfile, (packet.stream.frame rank).postDateSpine_eq_reference]

/-- Literal one-root profile representing a returned semantic prefix. -/
def returnedProfile
    (packet : FinFourUniformEscapePacket parent) (rank : ℕ)
    (root : Fin 4 → PMF Bool) : (quittingGame reward).BehaviorProfile :=
  quittingRootThenContinuationProfile reward root
    (packet.continuationProfile rank)

/-- The returned profile realizes the exact semantic prefix at the same tail. -/
theorem semanticPair_returnedProfile_eq_prefix
    (packet : FinFourUniformEscapePacket parent) (rank : ℕ)
    (root : Fin 4 → PMF Bool) :
    quittingTerminalSemanticPair reward (packet.returnedProfile rank root) =
      quittingTerminalSemanticPrefix reward root (packet.stream.tail rank) := by
  rw [returnedProfile, quittingTerminalSemanticPair_rootThenContinuation,
    packet.semanticPair_continuationProfile_eq_tail rank]

/-- The half-floor tolerance is positive and remains strictly below the
literal escape floor. -/
theorem halfFloor_pos_and_lt
    (packet : FinFourUniformEscapePacket parent) :
    0 < packet.floor / 2 ∧ packet.floor / 2 < packet.floor := by
  constructor <;> linarith [packet.floor_pos]

/-- Every retained literal tail reaches the maximal-absorption exact cap--Nash
dispatch at half the uniform escape floor.  The result is a same-tail return
selection or universal same-tail undercharge; it is not a reset compiler. -/
theorem exists_maximalCapNash_halfFloorDispatch
    (packet : FinFourUniformEscapePacket parent) (rank : ℕ) :
    ∃ root : Fin 4 → PMF Bool,
      IsεQuittingRootNash reward (packet.stream.tail rank).2 0 root ∧
      0 < quittingStationaryContinueMass root ∧
      (∀ other : Fin 4 → PMF Bool,
        IsεQuittingRootNash reward (packet.stream.tail rank).2 0 other →
          quittingRootAbsorptionMass other ≤
            quittingRootAbsorptionMass root) ∧
      (IsQuittingCapNashResetReturnSelection
          (reward := reward) source.point.1 (packet.stream.tail rank) root
            (packet.floor / 2) ∨
        ((∀ other : Fin 4 → PMF Bool,
            IsεQuittingRootNash reward (packet.stream.tail rank).2 0 other →
              ¬ IsQuittingCapNashResetReturnSelection
                (reward := reward) source.point.1
                  (packet.stream.tail rank) other (packet.floor / 2)) ∧
          quittingTerminalSemanticDebtSum (packet.stream.tail rank) *
                quittingRootAbsorptionMass root <
            (quittingTerminalSemanticDebtSum (packet.stream.tail rank) -
                quittingTerminalSemanticDebtSum source.point.1) -
                  packet.floor / 2 ∧
          (IsεQuittingRootNash reward (packet.stream.tail rank).2 0
              (quittingAllContinueRoot : Fin 4 → PMF Bool) ∨
            ∃ blocker : Fin 4,
              let eta := reward (quittingSingletonTerminal blocker) blocker -
                (packet.stream.tail rank).2 blocker
              0 < eta ∧
                eta / (eta + 2 * quittingRewardBound reward) ≤
                  quittingRootAbsorptionMass root ∧
                ¬ IsQuittingCapNashResetReturnSelection
                  (reward := reward) source.point.1
                    (packet.stream.tail rank) root (packet.floor / 2)))) := by
  apply exists_maximalCapNash_returnSelection_or_sameTailUndercharge
    reward source.point.1 (packet.stream.tail rank) (packet.floor / 2)
      (M := quittingRewardBound reward)
  · exact abs_reward_le_quittingRewardBound reward
  · exact source.minimum
  · exact source.minimumDebt_pos
  · have hfloor := packet.tailDebt_floor rank
    linarith [packet.floor_pos]
  · exact packet.stream.tail_mem rank

/-- A selected half-floor return has the advertised literal returned-profile
debt bound.  This does not add the reset-coordinate premise required by later
reset compilers. -/
theorem returnedProfile_debt_le_minimum_add_halfFloor
    (packet : FinFourUniformEscapePacket parent) (rank : ℕ)
    (root : Fin 4 → PMF Bool)
    (hnash : IsεQuittingRootNash reward (packet.stream.tail rank).2 0 root)
    (hreturn : IsQuittingCapNashResetReturnSelection
      (reward := reward) source.point.1 (packet.stream.tail rank) root
        (packet.floor / 2)) :
    quittingTerminalSemanticDebtSum
        (quittingTerminalSemanticPair reward
          (packet.returnedProfile rank root)) ≤
      quittingTerminalSemanticDebtSum source.point.1 + packet.floor / 2 := by
  rw [packet.semanticPair_returnedProfile_eq_prefix rank root]
  exact (capNashReturnSelection_iff_tailEscape_prefix_nearMinimum
    source.point.1 (packet.stream.tail rank) root (packet.floor / 2) hnash).1
      hreturn

end FinFourUniformEscapePacket

/-! ## The stabilized fixed-pair decorated family -/

namespace FinFourMinimumReturnPacket

/-- The fixed pair terminal determined by the stabilized singleton and forced
owners. -/
def normalizedTerminal
    (packet : FinFourMinimumReturnPacket parent) :
    {S : Finset (Fin 4) // S.Nonempty} :=
  ⟨{packet.stream.singletonOwner, packet.stream.forcedOwner}, by simp⟩

/-- Every actual row routes to the displayed stabilized pair. -/
theorem row_forcedTerminal_eq_normalizedTerminal
    (packet : FinFourMinimumReturnPacket parent) (rank : ℕ) :
    (packet.stream.row rank).packet.forcedAdapter.routedTerminal =
      packet.normalizedTerminal := by
  apply Subtype.ext
  rw [(packet.stream.row rank).packet.forcedTerminal_val,
    packet.stream.row_singletonOwner rank,
    packet.stream.row_forcedOwner rank]
  rfl

/-- The forced-pair tail is exactly the collision tail stored by the same
source-preserving row. -/
theorem forcedPairTail_eq_tail
    (packet : FinFourMinimumReturnPacket parent) (rank : ℕ) :
    quittingTerminalSemanticPair reward
        (quittingAllContinueProfileSpine reward
          (packet.stream.row rank).packet.forcedAdapter.targetProfile
            ((packet.stream.frame rank).stage + 1)) =
      packet.stream.tail rank := by
  rw [packet.stream.forcedPair_postDateTail_eq_reference rank,
    packet.stream.tail_eq_framePostDateTail rank,
    (packet.stream.frame rank).postDateSpine_eq_reference]

/-- Actual comparison/forced-pair rows with one fixed terminal and owner. -/
def normalizedDecoratedFamily
    (packet : FinFourMinimumReturnPacket parent) :
    QuittingMarkedPairDecoratedFamily reward where
  sourceProfile := fun rank ↦ (packet.stream.frame rank).pureSingletonProfile
  profile := fun rank ↦
    (packet.stream.row rank).packet.forcedAdapter.targetProfile
  mark := fun rank ↦ (packet.stream.frame rank).stage
  terminal := packet.normalizedTerminal
  markedOwner := packet.stream.forcedOwner
  gainMover := packet.stream.forcedOwner
  markedMass_pos := by
    intro rank
    rw [← packet.row_forcedTerminal_eq_normalizedTerminal rank]
    exact source.minimumSingletonClockResolution_pos.trans_le
      (packet.stream.row rank).packet.resolution_le_forcedPairStageMass
  actualGain_pos := by
    intro rank
    rw [← packet.stream.row_forcedOwner rank]
    change 0 < (packet.stream.row rank).packet.forcedOwnerGain
    exact (mul_pos source.minimumSingletonClockResolution_pos
      source.residual.witness.terminalGap_pos).trans_le
        (packet.stream.row rank).packet.resolution_mul_terminalGap_le_forcedOwnerGain
  markedOwnerDefect_eq_zero := by
    intro rank
    rw [← packet.stream.row_forcedOwner rank]
    exact (packet.stream.row rank).packet.forcedOwnerDefect_eq_zero

@[simp] theorem normalizedDecoratedFamily_sourceProfile
    (packet : FinFourMinimumReturnPacket parent) (rank : ℕ) :
    packet.normalizedDecoratedFamily.sourceProfile rank =
      (packet.stream.frame rank).pureSingletonProfile := rfl

@[simp] theorem normalizedDecoratedFamily_profile
    (packet : FinFourMinimumReturnPacket parent) (rank : ℕ) :
    packet.normalizedDecoratedFamily.profile rank =
      (packet.stream.row rank).packet.forcedAdapter.targetProfile := rfl

@[simp] theorem normalizedDecoratedFamily_mark
    (packet : FinFourMinimumReturnPacket parent) (rank : ℕ) :
    packet.normalizedDecoratedFamily.mark rank =
      (packet.stream.frame rank).stage := rfl

/-- The normalized row retains the complete literal reference spine. -/
theorem normalizedDecoratedFamily_postDateSpine_eq_reference
    (packet : FinFourMinimumReturnPacket parent) (rank : ℕ) :
    quittingAllContinueProfileSpine reward
        (packet.normalizedDecoratedFamily.profile rank)
          (packet.normalizedDecoratedFamily.mark rank + 1) =
      quittingAllContinueProfileSpine reward
        (packet.stream.frame rank).referenceProfile
          ((packet.stream.frame rank).stage + 1) :=
  packet.stream.forcedPair_postDateSpine_eq_reference rank

/-- The normalized row retains the complete literal reference outcome law. -/
theorem normalizedDecoratedFamily_postDateLaw_eq_reference
    (packet : FinFourMinimumReturnPacket parent) (rank : ℕ) :
    quittingTerminalOutcomeMass reward
        (quittingAllContinueProfileSpine reward
          (packet.normalizedDecoratedFamily.profile rank)
            (packet.normalizedDecoratedFamily.mark rank + 1)) =
      quittingTerminalOutcomeMass reward
        (quittingAllContinueProfileSpine reward
          (packet.stream.frame rank).referenceProfile
            ((packet.stream.frame rank).stage + 1)) := by
  rw [packet.normalizedDecoratedFamily_postDateSpine_eq_reference rank]

/-- The stabilized exact-tail packet supplies the generic minimum-tail
decorated-family contract without changing its literal continuation. -/
def minimumTailSource
    (packet : FinFourMinimumReturnPacket parent) :
    QuittingMarkedPairMinimumTailSource packet.normalizedDecoratedFamily
      source.point.1 where
  minimum_mem := source.semantic_mem
  minimum_global := source.minimum
  minimum_pos := source.minimumDebt_pos
  markedMassFloor := source.minimumSingletonClockResolution
  markedMassFloor_pos := source.minimumSingletonClockResolution_pos
  markedMass_floor := by
    intro rank
    change source.minimumSingletonClockResolution ≤
      quittingStageCoalitionMass reward
        (packet.stream.row rank).packet.forcedAdapter.targetProfile
          (packet.stream.frame rank).stage packet.normalizedTerminal
    rw [← packet.row_forcedTerminal_eq_normalizedTerminal rank]
    exact (packet.stream.row rank).packet.resolution_le_forcedPairStageMass
  actualGainFloor := source.minimumSingletonClockResolution *
    source.residual.witness.terminalGap
  actualGainFloor_pos := mul_pos source.minimumSingletonClockResolution_pos
    source.residual.witness.terminalGap_pos
  actualGain_floor := by
    intro rank
    change source.minimumSingletonClockResolution *
        source.residual.witness.terminalGap ≤
      quittingTerminalPayoff reward
          (packet.stream.row rank).packet.forcedAdapter.targetProfile
            packet.stream.forcedOwner -
        quittingTerminalPayoff reward
          (packet.stream.frame rank).pureSingletonProfile
            packet.stream.forcedOwner
    rw [← packet.stream.row_forcedOwner rank]
    exact (packet.stream.row rank).packet.resolution_mul_terminalGap_le_forcedOwnerGain
  tailDebt_tendsto := by
    have htail := packet.tailDebt_tendsto_minimum
    apply htail.congr'
    filter_upwards [] with rank
    exact congrArg quittingTerminalSemanticDebtSum
      (packet.forcedPairTail_eq_tail rank).symm

/-- The stabilized owners are distinct, so the normalized terminal is a
genuine pair. -/
theorem normalizedTerminal_card
    (packet : FinFourMinimumReturnPacket parent) :
    packet.normalizedTerminal.val.card = 2 := by
  rw [← packet.row_forcedTerminal_eq_normalizedTerminal 0]
  exact (packet.stream.row 0).packet.forcedTerminal_card

end FinFourMinimumReturnPacket

namespace QuittingMarkedPairMinimumReturnActualizer

variable {packet : FinFourMinimumReturnPacket parent}
variable {selection : QuittingMarkedPairMinimumTailSelection
  packet.minimumTailSource}
variable {point : QuittingMarkedPairDecoration (Fin 4)}

/-- The actual stabilized stream row behind one raw-prefix actualizer row. -/
def completionOriginRank
    (actualizer : QuittingMarkedPairMinimumReturnActualizer
      selection.selectedFamily source.point.1 selection.massDensity
        selection.gainDensity point) (rank : ℕ) : ℕ :=
  selection.subsequence (actualizer.originRank rank)

/-- The literal finite root word used by the actualized completion row. -/
def completionOriginRoots
    (actualizer : QuittingMarkedPairMinimumReturnActualizer
      selection.selectedFamily source.point.1 selection.massDensity
        selection.gainDensity point) (rank : ℕ) : List (Fin 4 → PMF Bool) :=
  actualizer.originRoots rank

/-- The actualized target is the displayed root word prefixed to the actual
forced-pair endpoint row. -/
theorem completion_profile_eq_literalRootStack
    (actualizer : QuittingMarkedPairMinimumReturnActualizer
      selection.selectedFamily source.point.1 selection.massDensity
        selection.gainDensity point) (rank : ℕ) :
    actualizer.profiles rank =
      quittingLiteralRootStackProfile reward
        (actualizer.completionOriginRoots rank)
        ((packet.stream.row
          (actualizer.completionOriginRank rank)).packet.forcedAdapter.targetProfile) := by
  rfl

/-- Arbitrary prefixing preserves the full behavioral tail of the exact
selected source-preserving reference row. -/
theorem completion_postDateSpine_eq_reference
    (actualizer : QuittingMarkedPairMinimumReturnActualizer
      selection.selectedFamily source.point.1 selection.massDensity
        selection.gainDensity point) (rank : ℕ) :
    quittingAllContinueProfileSpine reward (actualizer.profiles rank)
        (actualizer.mark rank + 1) =
      quittingAllContinueProfileSpine reward
        ((packet.stream.frame
          (actualizer.completionOriginRank rank)).referenceProfile)
        ((packet.stream.frame (actualizer.completionOriginRank rank)).stage +
          1) := by
  calc
    quittingAllContinueProfileSpine reward (actualizer.profiles rank)
          (actualizer.mark rank + 1) =
        quittingAllContinueProfileSpine reward
          (selection.selectedFamily.profile (actualizer.originRank rank))
          (selection.selectedFamily.mark (actualizer.originRank rank) + 1) :=
      selection.selectedFamily.descendant_postMarkSpine_eq
        (actualizer.originRank rank) (actualizer.originRoots rank)
    _ = _ := packet.normalizedDecoratedFamily_postDateSpine_eq_reference
      (actualizer.completionOriginRank rank)

end QuittingMarkedPairMinimumReturnActualizer

/-- Source-preserving exact-tail normalized result.  The generic compactified
point is retained, while the equality arm is upgraded to the checked Fin4
regeneration-or-ascent consumer. -/
structure FinFourMinimumReturnNormalizedThreeRoleOrStrictInert
    (packet : FinFourMinimumReturnPacket parent) where
  generic : QuittingMarkedPairMinimumTailNormalizedResult
    packet.minimumTailSource
  outcome :
    (∃ actualizer : QuittingMarkedPairMinimumReturnActualizer
        generic.selection.selectedFamily source.point.1
          generic.selection.massDensity generic.selection.gainDensity
            generic.point,
      generic.point.wholeDebt =
          quittingTerminalSemanticDebtSum source.point.1 ∧
        Nonempty (FinFourThreeRoleRegenerationOrAscent source
          actualizer.packet)) ∨
    (quittingTerminalSemanticDebtSum source.point.1 < generic.point.wholeDebt ∧
      ∀ root : Fin 4 → PMF Bool,
        IsεQuittingRootNash reward generic.point.whole.1.2 0 root ↔
          root = (quittingAllContinueRoot : Fin 4 → PMF Bool))

namespace FinFourMinimumReturnPacket

/-- Exact-tail minimum return reaches actual three-role endpoint-law
regeneration/ascent or the strict normalized inert obstruction. -/
theorem nonempty_normalizedThreeRole_or_strictInert
    (packet : FinFourMinimumReturnPacket parent) :
    Nonempty (FinFourMinimumReturnNormalizedThreeRoleOrStrictInert packet) := by
  obtain ⟨generic⟩ :=
    packet.minimumTailSource.nonempty_normalizedThreeRole_or_strictInert (by
      change 1 < packet.normalizedTerminal.val.card
      rw [packet.normalizedTerminal_card]
      norm_num)
  refine ⟨{ generic := generic, outcome := ?_ }⟩
  rcases generic.outcome with hreturn | hinert
  · left
    obtain ⟨actualizer, heq, mover, recipient, ⟨endpoint⟩⟩ := hreturn
    exact ⟨actualizer, heq,
      endpoint.nonempty_finFourRegenerationOrAscent⟩
  · exact Or.inr hinert

end FinFourMinimumReturnPacket

namespace FinFourMinimumReturnNormalizedThreeRoleOrStrictInert

/-- The outer monodromy-free entrance residual remains recoverable from the
stored packet.  Equality-arm regeneration preserves only the source's
underlying quantitative hard residual; it does not reconstruct this outer
residual or preserve the entrance chronology. -/
def residual
    {packet : FinFourMinimumReturnPacket parent}
    (_result : FinFourMinimumReturnNormalizedThreeRoleOrStrictInert packet) :
    FinFourProducerResidualWithoutMonodromy reward bound :=
  parent.residual

@[simp] theorem residual_eq_entrance
    {packet : FinFourMinimumReturnPacket parent}
    (result : FinFourMinimumReturnNormalizedThreeRoleOrStrictInert packet) :
    result.residual = entrance.toResidual := rfl

end FinFourMinimumReturnNormalizedThreeRoleOrStrictInert

/-! ## One-shot dependent completion consumer -/

/-- All literal rows of one escape packet carry the checked same-tail
half-floor dispatch. -/
structure FinFourUniformEscapeConsumed
    (packet : FinFourUniformEscapePacket parent) where
  dispatch : ∀ rank,
    ∃ root : Fin 4 → PMF Bool,
      IsεQuittingRootNash reward (packet.stream.tail rank).2 0 root ∧
      0 < quittingStationaryContinueMass root ∧
      (∀ other : Fin 4 → PMF Bool,
        IsεQuittingRootNash reward (packet.stream.tail rank).2 0 other →
          quittingRootAbsorptionMass other ≤
            quittingRootAbsorptionMass root) ∧
      (IsQuittingCapNashResetReturnSelection
          (reward := reward) source.point.1 (packet.stream.tail rank) root
            (packet.floor / 2) ∨
        ((∀ other : Fin 4 → PMF Bool,
            IsεQuittingRootNash reward (packet.stream.tail rank).2 0 other →
              ¬ IsQuittingCapNashResetReturnSelection
                (reward := reward) source.point.1
                  (packet.stream.tail rank) other (packet.floor / 2)) ∧
          quittingTerminalSemanticDebtSum (packet.stream.tail rank) *
                quittingRootAbsorptionMass root <
            (quittingTerminalSemanticDebtSum (packet.stream.tail rank) -
                quittingTerminalSemanticDebtSum source.point.1) -
                  packet.floor / 2 ∧
          (IsεQuittingRootNash reward (packet.stream.tail rank).2 0
              (quittingAllContinueRoot : Fin 4 → PMF Bool) ∨
            ∃ blocker : Fin 4,
              let eta := reward (quittingSingletonTerminal blocker) blocker -
                (packet.stream.tail rank).2 blocker
              0 < eta ∧
                eta / (eta + 2 * quittingRewardBound reward) ≤
                  quittingRootAbsorptionMass root ∧
                ¬ IsQuittingCapNashResetReturnSelection
                  (reward := reward) source.point.1
                    (packet.stream.tail rank) root (packet.floor / 2))))

namespace FinFourUniformEscapePacket

/-- Bundle the independently checked dispatch at every retained row. -/
theorem nonempty_consumed (packet : FinFourUniformEscapePacket parent) :
    Nonempty (FinFourUniformEscapeConsumed packet) :=
  ⟨⟨packet.exists_maximalCapNash_halfFloorDispatch⟩⟩

end FinFourUniformEscapePacket

/-- The consumed terminal outcome, still indexed by the exact entrance
residual selected before either semantic consumer runs. -/
inductive FinFourSourcePreservingConsumedOutcome
    (residual : FinFourProducerResidualWithoutMonodromy reward bound) : Type
  | uniformEscape
      {source : FinFourMinimumAtomProducer reward bound}
      {entrance : FinFourSourcePreservingSingletonEntrance source}
      (parent : FinFourSourcePreservingCofinalSingletonPacket entrance)
      (residual_eq : parent.residual = residual)
      (packet : FinFourUniformEscapePacket parent)
      (consumed : FinFourUniformEscapeConsumed packet)
  | minimumReturn
      {source : FinFourMinimumAtomProducer reward bound}
      {entrance : FinFourSourcePreservingSingletonEntrance source}
      (parent : FinFourSourcePreservingCofinalSingletonPacket entrance)
      (residual_eq : parent.residual = residual)
      (packet : FinFourMinimumReturnPacket parent)
      (consumed : FinFourMinimumReturnNormalizedThreeRoleOrStrictInert packet)

/-- Consume either structural terminal mode without changing its exact
residual index. -/
theorem FinFourSourcePreservingCompletionOutcome.nonempty_consumed
    {residual : FinFourProducerResidualWithoutMonodromy reward bound}
    (outcome : FinFourSourcePreservingCompletionOutcome residual) :
    Nonempty (FinFourSourcePreservingConsumedOutcome residual) := by
  cases outcome with
  | @uniformEscape source entrance parent hresidual packet =>
      obtain ⟨consumed⟩ := packet.nonempty_consumed
      exact ⟨.uniformEscape parent hresidual packet consumed⟩
  | @minimumReturn source entrance parent hresidual packet =>
      obtain ⟨consumed⟩ :=
        packet.nonempty_normalizedThreeRole_or_strictInert
      exact ⟨.minimumReturn parent hresidual packet consumed⟩

/-- Reward-level exhaustive composition: a uniform payoff already exists, or
the exact entrance residual reaches one of the two checked semantic consumers.
The second arm is not itself a uniform-equilibrium conclusion. -/
theorem uniformPayoff_or_sourcePreservingConsumedOutcome
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    {bound : ℝ} (hreward : ∀ terminal who, |reward terminal who| ≤ bound) :
    FinFourCompletionTerminal reward ∨
      ∃ residual : FinFourProducerResidualWithoutMonodromy reward bound,
        Nonempty (FinFourSourcePreservingConsumedOutcome residual) := by
  rcases uniformPayoff_or_sourcePreservingCompletionOutcome reward hreward with
      hterminal | houtcome
  · exact Or.inl hterminal
  · obtain ⟨residual, ⟨outcome⟩⟩ := houtcome
    exact Or.inr ⟨residual, outcome.nonempty_consumed⟩

end GameTheory
