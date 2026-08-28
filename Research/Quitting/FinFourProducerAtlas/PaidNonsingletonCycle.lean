/-
Copyright (c) 2026 UniformEquilibrium contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: UniformEquilibrium contributors.
-/

import Research.Quitting.FinFourProducerAtlas.MinimumReturnForcedPair
import Research.Quitting.PaidNonsingletonToggleCycle
import Research.Quitting.SourceFaithfulMinimumLawCausalization

/-!
# Source-faithful paid nonsingleton cycles in the Fin4 producer atlas

The cofinal forced-pair source fixes one literal pair and one actual family of
cross-tail profiles and marked dates.  The table-level maximum-toggle orbit is
selected once from that pair.  A terminal orbit gives a paid singleton.  A
closed segment gives one fixed nonsingleton cycle, one fixed edge, and one
fixed spectator along a strict outer subsequence.  Every retained row keeps
the original source profile, date, post-date spine, and exact horizontal
sibling profiles.

The equality endpoint arm causalizes the literal retained endpoint family and
its literal dates.  The horizontal edge remains a sibling comparison: it is
not asserted to occur in the regenerated chronology.
-/

noncomputable section

namespace GameTheory

open Filter Set Math.Probability
open MathUE.FiniteBooleanEndpointOrbit

variable
  {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
  {bound : ℝ} {source : FinFourMinimumAtomProducer reward bound}
  {returnSource :
    FinFourOwnerCompressedMinimumReturnForcedPairSource source}
  {lambda : ℝ}

namespace FinFourOwnerCompressedMinimumReturnForcedPairPacket

/-- The fixed forced pair as a nonsingleton state for the table orbit. -/
def maximumToggleStart
    (packet : FinFourOwnerCompressedMinimumReturnForcedPairPacket
      returnSource lambda) : FinFourNonsingletonCoalition :=
  ⟨packet.movingTerminal.val, by
    rw [packet.movingTerminal_card]
    norm_num⟩

/-- The literal actual source profile below all maximum-toggle siblings. -/
def maximumToggleBaseProfile
    (packet : FinFourOwnerCompressedMinimumReturnForcedPairPacket
      returnSource lambda) (index : ℕ) :
    (quittingGame reward).BehaviorProfile :=
  packet.base.crossTailProfile (packet.subsequence index)

/-- The literal actual marked date below all maximum-toggle siblings. -/
def maximumToggleStage
    (packet : FinFourOwnerCompressedMinimumReturnForcedPairPacket
      returnSource lambda) (index : ℕ) : ℕ :=
  (packet.base.endpoint (packet.subsequence index)).stage

theorem lambda_lt_maximumToggleLiveMass
    (packet : FinFourOwnerCompressedMinimumReturnForcedPairPacket
      returnSource lambda) (index : ℕ) :
    lambda < quittingLiveMass reward (packet.maximumToggleBaseProfile index)
      (packet.maximumToggleStage index) := by
  have hmass := packet.lambda_lt_forcedPairStageMass index
  rw [packet.forcedPair_stageMass_eq_liveMass] at hmass
  exact hmass

/-- The original forced-pair profile is literally the initial maximum-toggle
sibling over the retained cross-tail source. -/
theorem movingProfile_eq_initialMaximumToggleSibling
    (packet : FinFourOwnerCompressedMinimumReturnForcedPairPacket
      returnSource lambda) (index : ℕ) :
    packet.movingProfiles index =
      quittingMaximumToggleSiblingProfile reward
        (packet.maximumToggleBaseProfile index)
        (packet.maximumToggleStage index) packet.maximumToggleStart := by
  rw [movingProfiles, maximumToggleBaseProfile, maximumToggleStage]
  have hpair :
      (packet.base.forcedAdapter (packet.subsequence index)).targetProfile =
        quittingLiteralPureRootProfile reward
          (packet.base.crossTailProfile (packet.subsequence index))
          (packet.base.endpoint (packet.subsequence index)).stage
          (quittingCoalitionAction packet.movingTerminal.val) := by
    rw [QuittingStageAtomConcentratedPacketAdapter.targetProfile_eq_literalOneDateProfile]
    exact quittingLiteralPureRootProfile_update_eq_routed reward
      (packet.base.crossTailProfile (packet.subsequence index))
      (packet.base.endpoint (packet.subsequence index)).stage
      source.atom.terminal.val returnSource.forcedOwner
      (packet.base.forcedAdapter (packet.subsequence index)).action
      packet.movingTerminal.val
      (packet.forcedTerminal_eq_movingTerminal index |>
        congrArg Subtype.val |>.symm)
  simpa only [quittingMaximumToggleSiblingProfile,
    quittingLiteralPureRootCoalitionProfile,
    quittingPureRootOfCoalition, maximumToggleStart] using hpair

/-- Every fixed nonsingleton sibling over one actual row has the selected
near-minimum reference profile as its full post-date spine. -/
theorem maximumToggleSibling_postDateSpine_eq_reference
    (packet : FinFourOwnerCompressedMinimumReturnForcedPairPacket
      returnSource lambda) (index : ℕ)
    (coalition : FinFourNonsingletonCoalition) :
    quittingAllContinueProfileSpine reward
        (quittingMaximumToggleSiblingProfile reward
          (packet.maximumToggleBaseProfile index)
          (packet.maximumToggleStage index) coalition)
        (packet.maximumToggleStage index + 1) =
      packet.base.referenceProfile (packet.subsequence index) := by
  rw [quittingMaximumToggleSiblingProfile_postDateSpine_eq]
  exact quittingAllContinueProfileSpine_crossTailClosure reward
    (packet.base.endpoint (packet.subsequence index)).targetProfile
    (packet.base.referenceProfile (packet.subsequence index))
    (packet.base.endpoint (packet.subsequence index)).stage

/-- The fixed table-level maximum-toggle classification selected once from
the forced pair. -/
theorem nonempty_maximumToggle_terminalOrbit_or_closedSegment
    (packet : FinFourOwnerCompressedMinimumReturnForcedPairPacket
      returnSource lambda) :
    Nonempty (DispatchedOrbit
      (fun left ↦ Nonempty
        (FinFourMaximumToggleSingletonRoute reward left))
      (fun left right ↦ Nonempty
        (FinFourMaximumNonsingletonToggleEdge reward left right))
      packet.maximumToggleStart) ∨
      Nonempty (FinFourMaximumToggleClosedSegment.Trace
        (reward := reward) (start := packet.maximumToggleStart)) :=
  exists_finFourMaximumToggle_terminalOrbit_or_closedSegment reward
    packet.maximumToggleStart

end FinFourOwnerCompressedMinimumReturnForcedPairPacket

/-! ## The paid singleton terminal arm -/

/-- The terminal maximum-toggle arm, retained over the same fixed forced-pair
source.  The table orbit is chosen once and then realized at every actual row;
it is not a chronology through those rows. -/
structure FinFourForcedPairPaidSingletonEndpoint
    (packet : FinFourOwnerCompressedMinimumReturnForcedPairPacket
      returnSource lambda) where
  orbit : FinFourMaximumToggleTerminalOrbit.Trace
    (reward := reward) (start := packet.maximumToggleStart)

namespace FinFourForcedPairPaidSingletonEndpoint

variable
  {packet : FinFourOwnerCompressedMinimumReturnForcedPairPacket
    returnSource lambda}

def mover (endpoint : FinFourForcedPairPaidSingletonEndpoint packet) : Fin 4 :=
  FinFourMaximumToggleTerminalOrbit.mover endpoint.orbit

def terminal
    (endpoint : FinFourForcedPairPaidSingletonEndpoint packet) :
    {S : Finset (Fin 4) // S.Nonempty} :=
  (FinFourMaximumToggleTerminalOrbit.route endpoint.orbit).terminal

def action (endpoint : FinFourForcedPairPaidSingletonEndpoint packet) : Bool :=
  FinFourMaximumToggleTerminalOrbit.action endpoint.orbit

/-- The exact original producer chronology rank underneath one singleton
row. -/
def sourceIndex (_endpoint : FinFourForcedPairPaidSingletonEndpoint packet)
    (rank : ℕ) : ℕ :=
  packet.subsequence rank

theorem sourceIndex_strictMono
    (endpoint : FinFourForcedPairPaidSingletonEndpoint packet) :
    StrictMono endpoint.sourceIndex :=
  packet.subsequence_strictMono

theorem terminal_card
    (endpoint : FinFourForcedPairPaidSingletonEndpoint packet) :
    endpoint.terminal.val.card = 1 :=
  (FinFourMaximumToggleTerminalOrbit.route endpoint.orbit).terminal_card

def sourceCoalition
    (endpoint : FinFourForcedPairPaidSingletonEndpoint packet) :
    FinFourNonsingletonCoalition :=
  FinFourMaximumToggleTerminalOrbit.sourceCoalition endpoint.orbit

theorem terminal_eq_routed
    (endpoint : FinFourForcedPairPaidSingletonEndpoint packet) :
    endpoint.terminal.val = quittingPureEndpointRoutedCoalition
      endpoint.sourceCoalition.1 endpoint.mover endpoint.action :=
  FinFourMaximumToggleTerminalOrbit.terminal_eq_routed endpoint.orbit

def sourceProfile
    (endpoint : FinFourForcedPairPaidSingletonEndpoint packet) (rank : ℕ) :
    (quittingGame reward).BehaviorProfile :=
  FinFourMaximumToggleTerminalOrbit.sourceProfile endpoint.orbit
    (packet.maximumToggleBaseProfile rank) (packet.maximumToggleStage rank)

def targetProfile
    (endpoint : FinFourForcedPairPaidSingletonEndpoint packet) (rank : ℕ) :
    (quittingGame reward).BehaviorProfile :=
  FinFourMaximumToggleTerminalOrbit.targetProfile endpoint.orbit
    (packet.maximumToggleBaseProfile rank) (packet.maximumToggleStage rank)

def mark (_endpoint : FinFourForcedPairPaidSingletonEndpoint packet)
    (rank : ℕ) : ℕ :=
  packet.maximumToggleStage rank

/-- The singleton endpoint is the literal complete-strategy update of its
nonsingleton sibling at the same actual marked row. -/
theorem targetProfile_eq_literalOneDateProfile
    (endpoint : FinFourForcedPairPaidSingletonEndpoint packet) (rank : ℕ) :
    endpoint.targetProfile rank =
      quittingLiteralOneDateProfile reward (endpoint.sourceProfile rank)
        endpoint.mover (endpoint.mark rank) endpoint.action :=
  FinFourMaximumToggleTerminalOrbit.targetProfile_eq_literalOneDateProfile
    endpoint.orbit _ _

theorem targetProfile_eq_update
    (endpoint : FinFourForcedPairPaidSingletonEndpoint packet) (rank : ℕ) :
    endpoint.targetProfile rank =
      Function.update (endpoint.sourceProfile rank) endpoint.mover
        (endpoint.targetProfile rank endpoint.mover) :=
  FinFourMaximumToggleTerminalOrbit.targetProfile_eq_update endpoint.orbit _ _

/-- The singleton sibling is unchanged at every off-date coordinate. -/
theorem targetProfile_at_of_ne
    (endpoint : FinFourForcedPairPaidSingletonEndpoint packet) (rank time : ℕ)
    (htime : time ≠ endpoint.mark rank) (who : Fin 4) :
    endpoint.targetProfile rank who time =
      packet.maximumToggleBaseProfile rank who time := by
  rw [endpoint.targetProfile_eq_literalOneDateProfile]
  unfold quittingLiteralOneDateProfile
  by_cases hwho : who = endpoint.mover
  · subst who
    rw [Function.update_self]
    funext history
    rw [quittingLiteralOneDateOverride_of_ne _ _ _ _ htime]
    exact congrFun
      (quittingMaximumToggleSiblingProfile_at_of_ne reward
        (packet.maximumToggleBaseProfile rank) (endpoint.mark rank) time
        endpoint.sourceCoalition htime endpoint.mover) history
  · rw [Function.update_of_ne hwho]
    exact quittingMaximumToggleSiblingProfile_at_of_ne reward
      (packet.maximumToggleBaseProfile rank) (endpoint.mark rank) time
      endpoint.sourceCoalition htime who

/-- The routed endpoint remains literally singleton-valued. -/
theorem targetStageMass_eq_liveMass
    (endpoint : FinFourForcedPairPaidSingletonEndpoint packet) (rank : ℕ) :
    quittingStageCoalitionMass reward (endpoint.targetProfile rank)
        (endpoint.mark rank) endpoint.terminal =
      quittingLiveMass reward (packet.maximumToggleBaseProfile rank)
        (endpoint.mark rank) :=
  FinFourMaximumToggleTerminalOrbit.targetStageMass_eq_liveMass
    endpoint.orbit _ _

theorem lambda_lt_targetStageMass
    (endpoint : FinFourForcedPairPaidSingletonEndpoint packet) (rank : ℕ) :
    lambda < quittingStageCoalitionMass reward (endpoint.targetProfile rank)
      (endpoint.mark rank) endpoint.terminal := by
  rw [endpoint.targetStageMass_eq_liveMass]
  exact packet.lambda_lt_maximumToggleLiveMass rank

theorem lambda_lt_targetTerminalOutcomeMass
    (endpoint : FinFourForcedPairPaidSingletonEndpoint packet) (rank : ℕ) :
    lambda < quittingTerminalOutcomeMass reward (endpoint.targetProfile rank)
      (some endpoint.terminal) :=
  (endpoint.lambda_lt_targetStageMass rank).trans_le
    (quittingStageCoalitionMass_le_terminalOutcomeMass reward
      (endpoint.targetProfile rank) (endpoint.mark rank) endpoint.terminal)

def gain (endpoint : FinFourForcedPairPaidSingletonEndpoint packet)
    (rank : ℕ) : ℝ :=
  FinFourMaximumToggleTerminalOrbit.gain endpoint.orbit
    (packet.maximumToggleBaseProfile rank) (endpoint.mark rank)

/-- Exact actual payoff gain on the final nonsingleton-to-singleton toggle. -/
theorem gain_eq_liveMass_mul_toggleGain
    (endpoint : FinFourForcedPairPaidSingletonEndpoint packet) (rank : ℕ) :
    endpoint.gain rank =
      quittingLiveMass reward (packet.maximumToggleBaseProfile rank)
          (endpoint.mark rank) *
        quittingPureToggleGain reward endpoint.sourceCoalition.1
          endpoint.mover :=
  FinFourMaximumToggleTerminalOrbit.gain_eq_liveMass_mul_toggleGain
    endpoint.orbit _ _

/-- Every actual singleton exit carries the same sharp paid floor as a closed
cycle edge. -/
theorem gain_floor
    (endpoint : FinFourForcedPairPaidSingletonEndpoint packet) (rank : ℕ) :
    lambda * quittingTerminalSemanticDebtSum source.point.1 / 4 ≤
      endpoint.gain rank :=
  FinFourMaximumToggleTerminalOrbit.gain_floor endpoint.orbit
    source.point.1 source.minimum
    source.minimumDebt_pos _ _ lambda packet.lambda_pos
      (packet.lambda_lt_maximumToggleLiveMass rank).le

/-- The routed singleton lowers its mover's unrestricted debt by exactly the
displayed paid gain. -/
theorem moverDebt_eq_sub_gain
    (endpoint : FinFourForcedPairPaidSingletonEndpoint packet) (rank : ℕ) :
    quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward (endpoint.targetProfile rank))
        endpoint.mover =
      quittingTerminalSemanticDebt
          (quittingTerminalSemanticPair reward (endpoint.sourceProfile rank))
          endpoint.mover - endpoint.gain rank :=
  FinFourMaximumToggleTerminalOrbit.moverDebt_eq_sub_gain endpoint.orbit _ _

/-- The terminal toggle changes only its marked row and therefore retains the
same complete near-minimum post-date spine. -/
theorem targetProfile_postDateSpine_eq_reference
    (endpoint : FinFourForcedPairPaidSingletonEndpoint packet) (rank : ℕ) :
    quittingAllContinueProfileSpine reward (endpoint.targetProfile rank)
        (endpoint.mark rank + 1) =
      packet.base.referenceProfile (endpoint.sourceIndex rank) := by
  unfold targetProfile mark sourceIndex
    FinFourOwnerCompressedMinimumReturnForcedPairPacket.maximumToggleBaseProfile
    FinFourOwnerCompressedMinimumReturnForcedPairPacket.maximumToggleStage
  calc
    quittingAllContinueProfileSpine reward
        (FinFourMaximumToggleTerminalOrbit.targetProfile endpoint.orbit
          (packet.base.crossTailProfile (packet.subsequence rank))
          (packet.base.endpoint (packet.subsequence rank)).stage)
        ((packet.base.endpoint (packet.subsequence rank)).stage + 1) =
      quittingAllContinueProfileSpine reward
        (packet.base.crossTailProfile (packet.subsequence rank))
        ((packet.base.endpoint (packet.subsequence rank)).stage + 1) :=
      FinFourMaximumToggleTerminalOrbit.targetProfile_postDateSpine_eq
        endpoint.orbit _ _
    _ = packet.base.referenceProfile (packet.subsequence rank) :=
      quittingAllContinueProfileSpine_crossTailClosure reward
        (packet.base.endpoint (packet.subsequence rank)).targetProfile
        (packet.base.referenceProfile (packet.subsequence rank))
        (packet.base.endpoint (packet.subsequence rank)).stage

end FinFourForcedPairPaidSingletonEndpoint

/-! ## The paid cycle with fixed spectator labels -/

/-- One fixed table cycle, one fixed edge, and one fixed observer along a
strict subsequence of the actual forced-pair family. -/
structure FinFourForcedPairPaidNonsingletonCycle
    (packet : FinFourOwnerCompressedMinimumReturnForcedPairPacket
      returnSource lambda) where
  trace : FinFourMaximumToggleClosedSegment.Trace
    (reward := reward) (start := packet.maximumToggleStart)
  outerSubsequence : ℕ → ℕ
  outerSubsequence_strictMono : StrictMono outerSubsequence
  edgeOffset : Fin trace.segment.segment.period
  observer : Fin 4
  observer_ne_mover : observer ≠
    FinFourMaximumToggleClosedSegment.moverAt trace edgeOffset
  spectatorRise : ∀ rank,
    lambda * quittingTerminalSemanticDebtSum source.point.1 / 12 ≤
      quittingTerminalSemanticDebt
          (quittingTerminalSemanticPair reward
            (FinFourMaximumToggleClosedSegment.profileAt trace
              (packet.maximumToggleBaseProfile (outerSubsequence rank))
              (packet.maximumToggleStage (outerSubsequence rank))
              (edgeOffset + 1))) observer -
        quittingTerminalSemanticDebt
          (quittingTerminalSemanticPair reward
            (FinFourMaximumToggleClosedSegment.profileAt trace
              (packet.maximumToggleBaseProfile (outerSubsequence rank))
              (packet.maximumToggleStage (outerSubsequence rank)) edgeOffset))
          observer

namespace FinFourForcedPairPaidNonsingletonCycle

variable
  {packet : FinFourOwnerCompressedMinimumReturnForcedPairPacket
    returnSource lambda}

def mover (cycle : FinFourForcedPairPaidNonsingletonCycle packet) : Fin 4 :=
  FinFourMaximumToggleClosedSegment.moverAt cycle.trace cycle.edgeOffset

/-- The exact original producer chronology rank used by one retained cycle
row. -/
def sourceIndex (cycle : FinFourForcedPairPaidNonsingletonCycle packet)
    (rank : ℕ) : ℕ :=
  packet.subsequence (cycle.outerSubsequence rank)

theorem sourceIndex_strictMono
    (cycle : FinFourForcedPairPaidNonsingletonCycle packet) :
    StrictMono cycle.sourceIndex :=
  packet.subsequence_strictMono.comp cycle.outerSubsequence_strictMono

def sourceCoalition
    (cycle : FinFourForcedPairPaidNonsingletonCycle packet) :
    FinFourNonsingletonCoalition :=
  cycle.trace.orbit
    (cycle.trace.segment.segment.start + cycle.edgeOffset)

def targetCoalition
    (cycle : FinFourForcedPairPaidNonsingletonCycle packet) :
    FinFourNonsingletonCoalition :=
  cycle.trace.orbit
    (cycle.trace.segment.segment.start + cycle.edgeOffset + 1)

def sourceProfile (cycle : FinFourForcedPairPaidNonsingletonCycle packet)
    (rank : ℕ) : (quittingGame reward).BehaviorProfile :=
  FinFourMaximumToggleClosedSegment.profileAt cycle.trace
    (packet.maximumToggleBaseProfile (cycle.outerSubsequence rank))
    (packet.maximumToggleStage (cycle.outerSubsequence rank)) cycle.edgeOffset

def targetProfile (cycle : FinFourForcedPairPaidNonsingletonCycle packet)
    (rank : ℕ) : (quittingGame reward).BehaviorProfile :=
  FinFourMaximumToggleClosedSegment.profileAt cycle.trace
    (packet.maximumToggleBaseProfile (cycle.outerSubsequence rank))
    (packet.maximumToggleStage (cycle.outerSubsequence rank))
    (cycle.edgeOffset + 1)

def mark (cycle : FinFourForcedPairPaidNonsingletonCycle packet)
    (rank : ℕ) : ℕ :=
  packet.maximumToggleStage (cycle.outerSubsequence rank)

def targetTerminal
    (cycle : FinFourForcedPairPaidNonsingletonCycle packet) :
    {S : Finset (Fin 4) // S.Nonempty} :=
  quittingTerminalOfNonsingletonCoalition cycle.targetCoalition

def action (cycle : FinFourForcedPairPaidNonsingletonCycle packet) : Bool :=
  quittingCoalitionAction cycle.targetCoalition.1 cycle.mover

/-- The fixed table cycle has period exactly `4`, `6`, or `8`. -/
theorem period_eq_four_or_six_or_eight
    (cycle : FinFourForcedPairPaidNonsingletonCycle packet) :
    cycle.trace.segment.segment.period = 4 ∨
      cycle.trace.segment.segment.period = 6 ∨
        cycle.trace.segment.segment.period = 8 :=
  FinFourMaximumToggleClosedSegment.period_eq_four_or_six_or_eight cycle.trace
    source.point.1 source.minimum source.minimumDebt_pos

theorem sourceProfile_eq_literalSibling
    (cycle : FinFourForcedPairPaidNonsingletonCycle packet) (rank : ℕ) :
    cycle.sourceProfile rank =
      quittingMaximumToggleSiblingProfile reward
        (packet.maximumToggleBaseProfile (cycle.outerSubsequence rank))
        (cycle.mark rank) cycle.sourceCoalition := rfl

theorem targetProfile_eq_literalSibling
    (cycle : FinFourForcedPairPaidNonsingletonCycle packet) (rank : ℕ) :
    cycle.targetProfile rank =
      quittingMaximumToggleSiblingProfile reward
        (packet.maximumToggleBaseProfile (cycle.outerSubsequence rank))
        (cycle.mark rank) cycle.targetCoalition := rfl

/-- Both horizontal siblings retain every complete strategy away from their
one common marked date. -/
theorem sourceProfile_at_of_ne
    (cycle : FinFourForcedPairPaidNonsingletonCycle packet) (rank time : ℕ)
    (htime : time ≠ cycle.mark rank) (who : Fin 4) :
    cycle.sourceProfile rank who time =
      packet.maximumToggleBaseProfile (cycle.outerSubsequence rank) who time :=
  quittingMaximumToggleSiblingProfile_at_of_ne reward _ _ _ _ htime who

theorem targetProfile_at_of_ne
    (cycle : FinFourForcedPairPaidNonsingletonCycle packet) (rank time : ℕ)
    (htime : time ≠ cycle.mark rank) (who : Fin 4) :
    cycle.targetProfile rank who time =
      packet.maximumToggleBaseProfile (cycle.outerSubsequence rank) who time :=
  quittingMaximumToggleSiblingProfile_at_of_ne reward _ _ _ _ htime who

/-- The selected horizontal source sibling keeps the full selected reference
profile after the marked date. -/
theorem sourceProfile_postDateSpine_eq_reference
    (cycle : FinFourForcedPairPaidNonsingletonCycle packet) (rank : ℕ) :
    quittingAllContinueProfileSpine reward (cycle.sourceProfile rank)
        (cycle.mark rank + 1) =
      packet.base.referenceProfile
        (packet.subsequence (cycle.outerSubsequence rank)) :=
  packet.maximumToggleSibling_postDateSpine_eq_reference
    (cycle.outerSubsequence rank) cycle.sourceCoalition

/-- The selected horizontal target sibling has the identical full post-date
reference spine. -/
theorem targetProfile_postDateSpine_eq_reference
    (cycle : FinFourForcedPairPaidNonsingletonCycle packet) (rank : ℕ) :
    quittingAllContinueProfileSpine reward (cycle.targetProfile rank)
        (cycle.mark rank + 1) =
      packet.base.referenceProfile
        (packet.subsequence (cycle.outerSubsequence rank)) :=
  packet.maximumToggleSibling_postDateSpine_eq_reference
    (cycle.outerSubsequence rank) cycle.targetCoalition

/-- The horizontal endpoint is literally one complete-strategy update. -/
theorem targetProfile_eq_literalOneDateProfile
    (cycle : FinFourForcedPairPaidNonsingletonCycle packet) (rank : ℕ) :
    cycle.targetProfile rank = quittingLiteralOneDateProfile reward
      (cycle.sourceProfile rank) cycle.mover (cycle.mark rank) cycle.action :=
  quittingMaximumToggleSiblingProfile_target_eq_literalOneDateProfile
    reward _ _ _ _
      (FinFourMaximumToggleClosedSegment.edge cycle.trace cycle.edgeOffset)

theorem targetProfile_eq_update
    (cycle : FinFourForcedPairPaidNonsingletonCycle packet) (rank : ℕ) :
    cycle.targetProfile rank =
      Function.update (cycle.sourceProfile rank) cycle.mover
        (cycle.targetProfile rank cycle.mover) :=
  FinFourMaximumToggleClosedSegment.profileAt_succ_eq_update
    cycle.trace _ _ cycle.edgeOffset

/-- Every retained target sibling puts the full reached mass on its displayed
nonsingleton coalition at the marked row. -/
theorem targetStageMass_eq_liveMass
    (cycle : FinFourForcedPairPaidNonsingletonCycle packet) (rank : ℕ) :
    quittingStageCoalitionMass reward (cycle.targetProfile rank)
        (cycle.mark rank) cycle.targetTerminal =
      quittingLiveMass reward
        (packet.maximumToggleBaseProfile (cycle.outerSubsequence rank))
        (cycle.mark rank) := by
  rw [cycle.targetProfile_eq_literalSibling]
  exact quittingStageCoalitionMass_literalPureRootCoalitionProfile_eq_liveMass
    reward _ _ _

theorem lambda_lt_targetStageMass
    (cycle : FinFourForcedPairPaidNonsingletonCycle packet) (rank : ℕ) :
    lambda < quittingStageCoalitionMass reward (cycle.targetProfile rank)
      (cycle.mark rank) cycle.targetTerminal := by
  rw [cycle.targetStageMass_eq_liveMass]
  exact packet.lambda_lt_maximumToggleLiveMass (cycle.outerSubsequence rank)

theorem lambda_lt_targetTerminalOutcomeMass
    (cycle : FinFourForcedPairPaidNonsingletonCycle packet) (rank : ℕ) :
    lambda < quittingTerminalOutcomeMass reward (cycle.targetProfile rank)
      (some cycle.targetTerminal) :=
  (cycle.lambda_lt_targetStageMass rank).trans_le
    (quittingStageCoalitionMass_le_terminalOutcomeMass reward
      (cycle.targetProfile rank) (cycle.mark rank) cycle.targetTerminal)

/-- The selected edge has the exact actual gain formula. -/
theorem gain_eq_liveMass_mul_toggleGain
    (cycle : FinFourForcedPairPaidNonsingletonCycle packet) (rank : ℕ) :
    quittingTerminalPayoff reward (cycle.targetProfile rank) cycle.mover -
        quittingTerminalPayoff reward (cycle.sourceProfile rank) cycle.mover =
      quittingLiveMass reward
          (packet.maximumToggleBaseProfile (cycle.outerSubsequence rank))
          (cycle.mark rank) *
        quittingPureToggleGain reward cycle.sourceCoalition.1 cycle.mover :=
  FinFourMaximumToggleClosedSegment.gainAt_eq_liveMass_mul
    cycle.trace _ _ cycle.edgeOffset

/-- Every retained edge has the sharp paid floor `lambda * D_* / 4`. -/
theorem gain_floor
    (cycle : FinFourForcedPairPaidNonsingletonCycle packet) (rank : ℕ) :
    lambda * quittingTerminalSemanticDebtSum source.point.1 / 4 ≤
      quittingTerminalPayoff reward (cycle.targetProfile rank) cycle.mover -
        quittingTerminalPayoff reward (cycle.sourceProfile rank) cycle.mover :=
  FinFourMaximumToggleClosedSegment.gainAt_floor cycle.trace
    source.point.1 source.minimum
    source.minimumDebt_pos _ _ lambda packet.lambda_pos
      (packet.lambda_lt_maximumToggleLiveMass
        (cycle.outerSubsequence rank)).le cycle.edgeOffset

/-- Exact mover-debt subtraction on every retained actual sibling edge. -/
theorem moverDebt_eq_sub_gain
    (cycle : FinFourForcedPairPaidNonsingletonCycle packet) (rank : ℕ) :
    quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward (cycle.targetProfile rank))
        cycle.mover =
      quittingTerminalSemanticDebt
          (quittingTerminalSemanticPair reward (cycle.sourceProfile rank))
          cycle.mover -
        (quittingTerminalPayoff reward (cycle.targetProfile rank) cycle.mover -
          quittingTerminalPayoff reward (cycle.sourceProfile rank) cycle.mover) :=
  FinFourMaximumToggleClosedSegment.moverDebt_succ_eq_sub_gain
    cycle.trace _ _ cycle.edgeOffset

/-- The fixed spectator receives the exact `lambda * D_* / 12` recharge. -/
theorem observerDebtRise_floor
    (cycle : FinFourForcedPairPaidNonsingletonCycle packet) (rank : ℕ) :
    lambda * quittingTerminalSemanticDebtSum source.point.1 / 12 ≤
      quittingTerminalSemanticDebt
          (quittingTerminalSemanticPair reward (cycle.targetProfile rank))
          cycle.observer -
        quittingTerminalSemanticDebt
          (quittingTerminalSemanticPair reward (cycle.sourceProfile rank))
          cycle.observer :=
  cycle.spectatorRise rank

/-- The actual selected target strategy passed to the atom decoder. -/
def targetStrategy
    (cycle : FinFourForcedPairPaidNonsingletonCycle packet) (rank : ℕ) :
    (quittingGame reward).BehaviorStrategy cycle.mover :=
  cycle.targetProfile rank cycle.mover

/-- The packet's exact fixed atom charge `7 * lambda * D_* / 96`. -/
def atomCharge
    (_cycle : FinFourForcedPairPaidNonsingletonCycle packet) : ℝ :=
  7 * lambda * quittingTerminalSemanticDebtSum source.point.1 / 96

/-- Reciprocal vanishing response error used by the atom decoder. -/
def atomError
    (cycle : FinFourForcedPairPaidNonsingletonCycle packet) (rank : ℕ) : ℝ :=
  (cycle.atomCharge / 8) / (rank + 1)

theorem atomCharge_pos
    (cycle : FinFourForcedPairPaidNonsingletonCycle packet) :
    0 < cycle.atomCharge := by
  unfold atomCharge
  exact div_pos
    (mul_pos (mul_pos (by norm_num) packet.lambda_pos) source.minimumDebt_pos)
    (by norm_num)

theorem atomError_pos
    (cycle : FinFourForcedPairPaidNonsingletonCycle packet) (rank : ℕ) :
    0 < cycle.atomError rank := by
  unfold atomError
  exact div_pos (div_pos cycle.atomCharge_pos (by norm_num)) (by positivity)

theorem atomError_tendsto_zero
    (cycle : FinFourForcedPairPaidNonsingletonCycle packet) :
    Tendsto cycle.atomError atTop (nhds 0) := by
  unfold atomError
  simpa [div_eq_mul_inv, mul_assoc] using
    (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul
      (cycle.atomCharge / 8)

/-- Every retained row has the checked fixed-charge stopping-law atom
alternative. -/
theorem atomAlternative
    (cycle : FinFourForcedPairPaidNonsingletonCycle packet) (rank : ℕ) :
    HasQuittingStoppingLawVanishingDebtAtomAlternative reward
      (cycle.sourceProfile rank) cycle.mover cycle.observer
      (cycle.targetStrategy rank) cycle.atomCharge (cycle.atomError rank) := by
  let charge := lambda * quittingTerminalSemanticDebtSum source.point.1 / 12
  have hcharge : 0 < charge := by
    unfold charge
    exact div_pos (mul_pos packet.lambda_pos source.minimumDebt_pos) (by norm_num)
  have herrorLe : cycle.atomError rank ≤ charge / 8 := by
    have hdenom : (0 : ℝ) < rank + 1 := by positivity
    have hdivide : cycle.atomError rank ≤ cycle.atomCharge / 8 := by
      unfold atomError
      rw [div_le_iff₀ hdenom]
      have hone : (1 : ℝ) ≤ rank + 1 := by norm_num
      have hnonneg : 0 ≤ cycle.atomCharge / 8 :=
        (div_pos cycle.atomCharge_pos (by norm_num)).le
      nlinarith
    have hchargeCompare : cycle.atomCharge / 8 ≤ charge / 8 := by
      unfold atomCharge charge
      have hpositive : 0 < lambda *
          quittingTerminalSemanticDebtSum source.point.1 :=
        mul_pos packet.lambda_pos source.minimumDebt_pos
      nlinarith
    exact hdivide.trans hchargeCompare
  have hdispatch :=
    FinFourMaximumToggleClosedSegment.hasVanishingDebtAtomAlternative cycle.trace
    (packet.maximumToggleBaseProfile (cycle.outerSubsequence rank))
    (cycle.mark rank) cycle.edgeOffset cycle.observer charge
    (cycle.atomError rank) hcharge (cycle.atomError_pos rank) herrorLe
    (cycle.observerDebtRise_floor rank)
  have hchargeEq : cycle.atomCharge = 7 * charge / 8 := by
    unfold atomCharge charge
    ring
  rw [hchargeEq]
  simpa only [sourceProfile, mover, targetStrategy, targetProfile, mark] using
    hdispatch

end FinFourForcedPairPaidNonsingletonCycle

private theorem exists_fixed_strictMono_subsequence
    {Label : Type} [Fintype Label] (label : ℕ → Label) :
    ∃ fixed : Label, ∃ subsequence : ℕ → ℕ,
      StrictMono subsequence ∧ ∀ rank, label (subsequence rank) = fixed := by
  have hfrequent : ∃ fixed : Label, ∃ᶠ rank in atTop,
      label rank = fixed := by
    by_contra hnone
    push Not at hnone
    have hall : ∀ᶠ rank in atTop, ∀ fixed : Label,
        label rank ≠ fixed := by
      rw [eventually_all]
      exact hnone
    obtain ⟨rank, hrank⟩ := hall.exists
    exact hrank (label rank) rfl
  obtain ⟨fixed, hfixed⟩ := hfrequent
  obtain ⟨subsequence, hmono, hlabel⟩ :=
    extraction_of_frequently_atTop hfixed
  exact ⟨fixed, subsequence, hmono, hlabel⟩

/-- Freeze one spectator-edge label on a strict subsequence of all actual
forced-pair rows.  No profile or marked date is reselected before this
finite-label extraction. -/
theorem nonempty_forcedPairPaidNonsingletonCycle
    (packet : FinFourOwnerCompressedMinimumReturnForcedPairPacket
      returnSource lambda)
    (trace : FinFourMaximumToggleClosedSegment.Trace
      (reward := reward) (start := packet.maximumToggleStart)) :
    Nonempty (FinFourForcedPairPaidNonsingletonCycle packet) := by
  have hrow : ∀ index : ℕ,
      ∃ offset : Fin trace.segment.segment.period, ∃ observer : Fin 4,
        observer ≠ FinFourMaximumToggleClosedSegment.moverAt trace offset ∧
          lambda * quittingTerminalSemanticDebtSum source.point.1 / 12 ≤
            quittingTerminalSemanticDebt
                (quittingTerminalSemanticPair reward
                  (FinFourMaximumToggleClosedSegment.profileAt trace
                    (packet.maximumToggleBaseProfile index)
                    (packet.maximumToggleStage index) (offset + 1))) observer -
              quittingTerminalSemanticDebt
                (quittingTerminalSemanticPair reward
                  (FinFourMaximumToggleClosedSegment.profileAt trace
                    (packet.maximumToggleBaseProfile index)
                    (packet.maximumToggleStage index) offset)) observer := by
    intro index
    exact FinFourMaximumToggleClosedSegment.exists_spectatorDebtRise trace
      source.point.1 source.minimum
      source.minimumDebt_pos (packet.maximumToggleBaseProfile index)
      (packet.maximumToggleStage index) lambda packet.lambda_pos
      (packet.lambda_lt_maximumToggleLiveMass index).le
  choose offset observer hobserver hrise using hrow
  let label : ℕ → Fin trace.segment.segment.period × Fin 4 :=
    fun index ↦ (offset index, observer index)
  obtain ⟨fixed, subsequence, hsubsequence, hlabel⟩ :=
    exists_fixed_strictMono_subsequence label
  refine ⟨{
    trace := trace
    outerSubsequence := subsequence
    outerSubsequence_strictMono := hsubsequence
    edgeOffset := fixed.1
    observer := fixed.2
    observer_ne_mover := ?_
    spectatorRise := ?_
  }⟩
  · have heq := hlabel 0
    change (offset (subsequence 0), observer (subsequence 0)) = fixed at heq
    have hoffset := congrArg Prod.fst heq
    have hobserverEq := congrArg Prod.snd heq
    simpa [← hoffset, ← hobserverEq] using hobserver (subsequence 0)
  · intro rank
    have heq := hlabel rank
    change (offset (subsequence rank), observer (subsequence rank)) = fixed at heq
    have hoffset := congrArg Prod.fst heq
    have hobserverEq := congrArg Prod.snd heq
    simpa [← hoffset, ← hobserverEq] using hrise (subsequence rank)

/-! ## Actual joint-law endpoint and source-faithful regeneration -/

/-- One common compactification of the literal source and endpoint sibling
profiles on the already frozen spectator subsequence. -/
structure FinFourPaidNonsingletonCycleEndpointLaw
    (packet : FinFourOwnerCompressedMinimumReturnForcedPairPacket
      returnSource lambda)
    (cycle : FinFourForcedPairPaidNonsingletonCycle packet) where
  compactRefinement : ℕ → ℕ
  compactRefinement_strictMono : StrictMono compactRefinement
  sourcePoint : QuittingTerminalSemanticLawPoint (Fin 4)
  targetPoint : QuittingTerminalSemanticLawPoint (Fin 4)
  source_mem : sourcePoint ∈ quittingTerminalSemanticLawCarrier reward
  target_mem : targetPoint ∈ quittingTerminalSemanticLawCarrier reward
  source_tendsto : Tendsto (fun rank ↦
    let index := compactRefinement rank
    (quittingTerminalSemanticPair reward (cycle.sourceProfile index),
      quittingTerminalOutcomeMass reward (cycle.sourceProfile index)))
    atTop (nhds sourcePoint)
  target_tendsto : Tendsto (fun rank ↦
    let index := compactRefinement rank
    (quittingTerminalSemanticPair reward (cycle.targetProfile index),
      quittingTerminalOutcomeMass reward (cycle.targetProfile index)))
    atTop (nhds targetPoint)
  observerRise : lambda * quittingTerminalSemanticDebtSum source.point.1 / 12 ≤
    quittingTerminalSemanticDebt targetPoint.1 cycle.observer -
      quittingTerminalSemanticDebt sourcePoint.1 cycle.observer
  targetMass_floor : lambda ≤ targetPoint.2 (some cycle.targetTerminal)
  targetDebt_floor : quittingTerminalSemanticDebtSum source.point.1 ≤
    quittingTerminalSemanticDebtSum targetPoint.1

namespace FinFourPaidNonsingletonCycleEndpointLaw

variable
  {packet : FinFourOwnerCompressedMinimumReturnForcedPairPacket
    returnSource lambda}
  {cycle : FinFourForcedPairPaidNonsingletonCycle packet}

def selectedOuterIndex
    (endpoint : FinFourPaidNonsingletonCycleEndpointLaw packet cycle)
    (rank : ℕ) : ℕ :=
  cycle.outerSubsequence (endpoint.compactRefinement rank)

/-- The exact original producer chronology rank after both cycle and compact
refinements. -/
def selectedSourceIndex
    (endpoint : FinFourPaidNonsingletonCycleEndpointLaw packet cycle)
    (rank : ℕ) : ℕ :=
  cycle.sourceIndex (endpoint.compactRefinement rank)

theorem selectedSourceIndex_strictMono
    (endpoint : FinFourPaidNonsingletonCycleEndpointLaw packet cycle) :
    StrictMono endpoint.selectedSourceIndex :=
  cycle.sourceIndex_strictMono.comp endpoint.compactRefinement_strictMono

def selectedMark
    (endpoint : FinFourPaidNonsingletonCycleEndpointLaw packet cycle)
    (rank : ℕ) : ℕ := cycle.mark (endpoint.compactRefinement rank)

def selectedSourceProfile
    (endpoint : FinFourPaidNonsingletonCycleEndpointLaw packet cycle)
    (rank : ℕ) : (quittingGame reward).BehaviorProfile :=
  cycle.sourceProfile (endpoint.compactRefinement rank)

def selectedTargetProfile
    (endpoint : FinFourPaidNonsingletonCycleEndpointLaw packet cycle)
    (rank : ℕ) : (quittingGame reward).BehaviorProfile :=
  cycle.targetProfile (endpoint.compactRefinement rank)

theorem targetDebt_eq_minimum_or_strict
    (endpoint : FinFourPaidNonsingletonCycleEndpointLaw packet cycle) :
    quittingTerminalSemanticDebtSum endpoint.targetPoint.1 =
        quittingTerminalSemanticDebtSum source.point.1 ∨
      quittingTerminalSemanticDebtSum source.point.1 <
        quittingTerminalSemanticDebtSum endpoint.targetPoint.1 := by
  rcases endpoint.targetDebt_floor.eq_or_lt with heq | hstrict
  · exact Or.inl heq.symm
  · exact Or.inr hstrict

theorem targetMass_pos
    (endpoint : FinFourPaidNonsingletonCycleEndpointLaw packet cycle) :
    0 < endpoint.targetPoint.2 (some cycle.targetTerminal) :=
  packet.lambda_pos.trans_le endpoint.targetMass_floor

end FinFourPaidNonsingletonCycleEndpointLaw

/-- Equality-arm source regeneration retaining the literal endpoint sibling
family, literal marked dates, fixed routed terminal, and unchanged hard
residual. -/
structure FinFourPaidCycleMinimumRegeneration
    (packet : FinFourOwnerCompressedMinimumReturnForcedPairPacket
      returnSource lambda)
    (cycle : FinFourForcedPairPaidNonsingletonCycle packet)
    (endpoint : FinFourPaidNonsingletonCycleEndpointLaw packet cycle) where
  targetDebt_eq : quittingTerminalSemanticDebtSum endpoint.targetPoint.1 =
    quittingTerminalSemanticDebtSum source.point.1
  causalization : QuittingSourceFaithfulMinimumCausalization
    endpoint.targetPoint cycle.targetTerminal endpoint.selectedTargetProfile
      endpoint.selectedMark lambda

namespace FinFourPaidCycleMinimumRegeneration

variable
  {packet : FinFourOwnerCompressedMinimumReturnForcedPairPacket
    returnSource lambda}
  {cycle : FinFourForcedPairPaidNonsingletonCycle packet}
  {endpoint : FinFourPaidNonsingletonCycleEndpointLaw packet cycle}

def atom
    (regeneration : FinFourPaidCycleMinimumRegeneration packet cycle endpoint) :
    QuittingMinimumLawCausalSuffixAtom reward endpoint.targetPoint where
  terminal := cycle.targetTerminal
  terminalMass_pos := endpoint.targetMass_pos
  chronology := ⟨endpoint.selectedTargetProfile,
    regeneration.causalization.cutoff, endpoint.selectedMark,
    regeneration.causalization.roots,
    regeneration.causalization.profiles_tendsto,
    regeneration.causalization.roots_length,
    regeneration.causalization.roots_nash,
    regeneration.causalization.prefix_debt_tendsto,
    regeneration.causalization.causal⟩

/-- Fresh minimum source at the endpoint's actual joint semantic/law point. -/
def next
    (regeneration : FinFourPaidCycleMinimumRegeneration packet cycle endpoint) :
    FinFourMinimumAtomProducer reward bound where
  residual := source.residual
  point := endpoint.targetPoint
  point_mem := endpoint.target_mem
  semantic_mem := terminalSemanticLawCarrier_fst_mem_carrier
    endpoint.targetPoint endpoint.target_mem
  minimum := by
    intro candidate hcandidate
    rw [regeneration.targetDebt_eq]
    exact source.minimum candidate hcandidate
  inf_pos := source.inf_pos
  debt_eq_inf := regeneration.targetDebt_eq.trans source.debt_eq_inf
  atom := regeneration.atom

theorem next_residual_eq
    (regeneration : FinFourPaidCycleMinimumRegeneration packet cycle endpoint) :
    regeneration.next.residual = source.residual := rfl

theorem next_point_eq
    (regeneration : FinFourPaidCycleMinimumRegeneration packet cycle endpoint) :
    regeneration.next.point = endpoint.targetPoint := rfl

theorem next_terminal_eq
    (regeneration : FinFourPaidCycleMinimumRegeneration packet cycle endpoint) :
    regeneration.next.atom.terminal = cycle.targetTerminal := rfl

/-- The literal endpoint profiles retained by the regenerated minimum source.
These are the witnesses placed inside `next.atom.chronology`; the existential
chronology field itself is intentionally not treated as a data projection. -/
def chronologyProfile
    (_regeneration : FinFourPaidCycleMinimumRegeneration packet cycle endpoint)
    (rank : ℕ) : (quittingGame reward).BehaviorProfile :=
  endpoint.selectedTargetProfile rank

/-- The original marked dates paired with `chronologyProfile`. -/
def chronologyMark
    (_regeneration : FinFourPaidCycleMinimumRegeneration packet cycle endpoint)
    (rank : ℕ) : ℕ :=
  endpoint.selectedMark rank

theorem chronology_profile_eq
    (regeneration : FinFourPaidCycleMinimumRegeneration packet cycle endpoint)
    (rank : ℕ) :
    regeneration.chronologyProfile rank =
      cycle.targetProfile (endpoint.compactRefinement rank) := rfl

theorem chronology_mark_eq
    (regeneration : FinFourPaidCycleMinimumRegeneration packet cycle endpoint)
    (rank : ℕ) :
    regeneration.chronologyMark rank =
      cycle.mark (endpoint.compactRefinement rank) := rfl

/-- Exact original producer chronology rank underneath the regenerated row. -/
def chronologySourceIndex
    (_regeneration : FinFourPaidCycleMinimumRegeneration packet cycle endpoint)
    (rank : ℕ) : ℕ :=
  endpoint.selectedSourceIndex rank

theorem chronologySourceIndex_strictMono
    (regeneration : FinFourPaidCycleMinimumRegeneration packet cycle endpoint) :
    StrictMono regeneration.chronologySourceIndex :=
  endpoint.selectedSourceIndex_strictMono

/-- The regenerated chronology is actualized by the same endpoint joint laws
used to define its minimum point. -/
theorem chronology_jointLaw_tendsto
    (regeneration : FinFourPaidCycleMinimumRegeneration packet cycle endpoint) :
    Tendsto (fun rank ↦
      (quittingTerminalSemanticPair reward
          (regeneration.chronologyProfile rank),
        quittingTerminalOutcomeMass reward
          (regeneration.chronologyProfile rank)))
      atTop (nhds regeneration.next.point) := by
  simpa only [regeneration.chronology_profile_eq,
    regeneration.next_point_eq,
    FinFourPaidNonsingletonCycleEndpointLaw.selectedTargetProfile] using
      endpoint.target_tendsto

/-- Every regenerated row keeps the exact selected near-minimum reference
spine of its original source rank. -/
theorem chronology_postDateSpine_eq_reference
    (regeneration : FinFourPaidCycleMinimumRegeneration packet cycle endpoint)
    (rank : ℕ) :
    quittingAllContinueProfileSpine reward
        (regeneration.chronologyProfile rank)
        (regeneration.chronologyMark rank + 1) =
      packet.base.referenceProfile (regeneration.chronologySourceIndex rank) :=
  cycle.targetProfile_postDateSpine_eq_reference
    (endpoint.compactRefinement rank)

end FinFourPaidCycleMinimumRegeneration

/-! The existence proofs for the joint compactification and equality-arm
causalization are kept at this source-facing layer. -/

theorem nonempty_paidCycleEndpointLaw
    (packet : FinFourOwnerCompressedMinimumReturnForcedPairPacket
      returnSource lambda)
    (cycle : FinFourForcedPairPaidNonsingletonCycle packet) :
    Nonempty (FinFourPaidNonsingletonCycleEndpointLaw packet cycle) := by
  let joint : ℕ → QuittingTerminalSemanticLawPoint (Fin 4) ×
      QuittingTerminalSemanticLawPoint (Fin 4) := fun rank ↦
    ((quittingTerminalSemanticPair reward (cycle.sourceProfile rank),
        quittingTerminalOutcomeMass reward (cycle.sourceProfile rank)),
      (quittingTerminalSemanticPair reward (cycle.targetProfile rank),
        quittingTerminalOutcomeMass reward (cycle.targetProfile rank)))
  have hjointMem : ∀ rank, joint rank ∈
      quittingTerminalSemanticLawCarrier reward ×ˢ
        quittingTerminalSemanticLawCarrier reward := by
    intro rank
    exact ⟨quittingTerminalSemanticLawPoint_mem_carrier reward _,
      quittingTerminalSemanticLawPoint_mem_carrier reward _⟩
  obtain ⟨limit, hlimitMem, refinement, hrefinement, hlimit⟩ :=
    ((quittingTerminalSemanticLawCarrier_isCompact reward).prod
      (quittingTerminalSemanticLawCarrier_isCompact reward)).tendsto_subseq
      hjointMem
  have hsource : Tendsto (fun rank ↦
      (quittingTerminalSemanticPair reward
          (cycle.sourceProfile (refinement rank)),
        quittingTerminalOutcomeMass reward
          (cycle.sourceProfile (refinement rank))))
      atTop (nhds limit.1) := by
    simpa [joint, Function.comp_def] using
      (continuous_fst.tendsto limit).comp hlimit
  have htarget : Tendsto (fun rank ↦
      (quittingTerminalSemanticPair reward
          (cycle.targetProfile (refinement rank)),
        quittingTerminalOutcomeMass reward
          (cycle.targetProfile (refinement rank))))
      atTop (nhds limit.2) := by
    simpa [joint, Function.comp_def] using
      (continuous_snd.tendsto limit).comp hlimit
  have hobserverSource : Tendsto (fun rank ↦
      quittingTerminalSemanticDebt (joint (refinement rank)).1.1
        cycle.observer) atTop
      (nhds (quittingTerminalSemanticDebt limit.1.1 cycle.observer)) :=
    (((continuous_quittingTerminalSemanticDebt cycle.observer).comp
      continuous_fst).comp
      continuous_fst).tendsto limit |>.comp hlimit
  have hobserverTarget : Tendsto (fun rank ↦
      quittingTerminalSemanticDebt (joint (refinement rank)).2.1
        cycle.observer) atTop
      (nhds (quittingTerminalSemanticDebt limit.2.1 cycle.observer)) :=
    (((continuous_quittingTerminalSemanticDebt cycle.observer).comp
      continuous_fst).comp
      continuous_snd).tendsto limit |>.comp hlimit
  have hrise : lambda * quittingTerminalSemanticDebtSum source.point.1 / 12 ≤
      quittingTerminalSemanticDebt limit.2.1 cycle.observer -
        quittingTerminalSemanticDebt limit.1.1 cycle.observer := by
    apply ge_of_tendsto (hobserverTarget.sub hobserverSource)
    exact Eventually.of_forall fun rank ↦ cycle.observerDebtRise_floor _
  have hlaw :=
    (((continuous_apply (some cycle.targetTerminal)).comp continuous_snd).comp
      continuous_snd).tendsto limit |>.comp hlimit
  have hmass : lambda ≤ limit.2.2 (some cycle.targetTerminal) := by
    apply ge_of_tendsto hlaw
    exact Eventually.of_forall fun rank ↦ by
      have hstage : lambda ≤ quittingStageCoalitionMass reward
          (cycle.targetProfile (refinement rank))
          (cycle.mark (refinement rank)) cycle.targetTerminal :=
        (cycle.lambda_lt_targetStageMass (refinement rank)).le
      exact hstage.trans
        (quittingStageCoalitionMass_le_terminalOutcomeMass reward _ _ _)
  have htargetDebt : quittingTerminalSemanticDebtSum source.point.1 ≤
      quittingTerminalSemanticDebtSum limit.2.1 := by
    exact source.minimum _
      (terminalSemanticLawCarrier_fst_mem_carrier limit.2 hlimitMem.2)
  exact ⟨{
    compactRefinement := refinement
    compactRefinement_strictMono := hrefinement
    sourcePoint := limit.1
    targetPoint := limit.2
    source_mem := hlimitMem.1
    target_mem := hlimitMem.2
    source_tendsto := hsource
    target_tendsto := htarget
    observerRise := hrise
    targetMass_floor := hmass
    targetDebt_floor := htargetDebt
  }⟩

theorem nonempty_paidCycleMinimumRegeneration
    (packet : FinFourOwnerCompressedMinimumReturnForcedPairPacket
      returnSource lambda)
    (cycle : FinFourForcedPairPaidNonsingletonCycle packet)
    (endpoint : FinFourPaidNonsingletonCycleEndpointLaw packet cycle)
    (heq : quittingTerminalSemanticDebtSum endpoint.targetPoint.1 =
      quittingTerminalSemanticDebtSum source.point.1) :
    Nonempty (FinFourPaidCycleMinimumRegeneration packet cycle endpoint) := by
  have hmark : ∀ rank, lambda ≤ quittingStageCoalitionMass reward
      (endpoint.selectedTargetProfile rank) (endpoint.selectedMark rank)
      cycle.targetTerminal := by
    intro rank
    unfold FinFourPaidNonsingletonCycleEndpointLaw.selectedTargetProfile
      FinFourPaidNonsingletonCycleEndpointLaw.selectedMark
    exact (cycle.lambda_lt_targetStageMass
      (endpoint.compactRefinement rank)).le
  obtain ⟨causalization⟩ := nonempty_sourceFaithfulMinimumCausalization
    endpoint.targetPoint cycle.targetTerminal endpoint.selectedTargetProfile
    endpoint.selectedMark lambda endpoint.target_mem
    (by simpa only [FinFourPaidNonsingletonCycleEndpointLaw.selectedTargetProfile]
      using endpoint.target_tendsto)
    (by
      intro candidate hcandidate
      rw [heq]
      exact source.minimum candidate hcandidate)
    (heq.trans source.debt_eq_inf) source.inf_pos packet.lambda_pos hmark
  exact ⟨⟨heq, causalization⟩⟩

/-! ## Exhaustive source-attached capstone -/

/-- The complete result of the fixed maximum-toggle dispatch on one actual
cofinal forced-pair source.  The singleton branch is already a paid literal
endpoint.  A closed cycle supplies either a genuinely off-minimum compact
endpoint or a regenerated minimum source carrying the same hard residual.

This classification does not say that any horizontal sibling edge occurs in
the regenerated chronology, and it supplies no return, rank-descent, or
uniform-equilibrium consumer. -/
inductive FinFourPaidNonsingletonCycleOutcome
    (packet : FinFourOwnerCompressedMinimumReturnForcedPairPacket
      returnSource lambda) : Type
  | paidSingleton : FinFourForcedPairPaidSingletonEndpoint packet →
      FinFourPaidNonsingletonCycleOutcome packet
  | offMinimumEndpoint :
      (cycle : FinFourForcedPairPaidNonsingletonCycle packet) →
      (endpoint : FinFourPaidNonsingletonCycleEndpointLaw packet cycle) →
      quittingTerminalSemanticDebtSum source.point.1 <
        quittingTerminalSemanticDebtSum endpoint.targetPoint.1 →
      FinFourPaidNonsingletonCycleOutcome packet
  | minimumRegeneration :
      (cycle : FinFourForcedPairPaidNonsingletonCycle packet) →
      (endpoint : FinFourPaidNonsingletonCycleEndpointLaw packet cycle) →
      FinFourPaidCycleMinimumRegeneration packet cycle endpoint →
      FinFourPaidNonsingletonCycleOutcome packet

/-- Literal disjunctive form of the source-attached result. -/
theorem nonempty_paidSingleton_or_cycleEndpoint
    (packet : FinFourOwnerCompressedMinimumReturnForcedPairPacket
      returnSource lambda) :
    Nonempty (FinFourForcedPairPaidSingletonEndpoint packet) ∨
      ∃ cycle : FinFourForcedPairPaidNonsingletonCycle packet,
        ∃ endpoint : FinFourPaidNonsingletonCycleEndpointLaw packet cycle,
          quittingTerminalSemanticDebtSum source.point.1 <
              quittingTerminalSemanticDebtSum endpoint.targetPoint.1 ∨
            Nonempty
              (FinFourPaidCycleMinimumRegeneration packet cycle endpoint) := by
  rcases packet.nonempty_maximumToggle_terminalOrbit_or_closedSegment with
    horbit | htrace
  · rcases horbit with ⟨orbit⟩
    exact Or.inl ⟨⟨orbit⟩⟩
  · rcases htrace with ⟨trace⟩
    obtain ⟨cycle⟩ := nonempty_forcedPairPaidNonsingletonCycle packet trace
    obtain ⟨endpoint⟩ := nonempty_paidCycleEndpointLaw packet cycle
    refine Or.inr ⟨cycle, endpoint, ?_⟩
    rcases endpoint.targetDebt_eq_minimum_or_strict with heq | hstrict
    · exact Or.inr
        (nonempty_paidCycleMinimumRegeneration packet cycle endpoint heq)
    · exact Or.inl hstrict

/-- Exhaustive producer-facing capstone for the fixed forced-pair source. -/
theorem nonempty_paidNonsingletonCycleOutcome
    (packet : FinFourOwnerCompressedMinimumReturnForcedPairPacket
      returnSource lambda) :
    Nonempty (FinFourPaidNonsingletonCycleOutcome packet) := by
  rcases nonempty_paidSingleton_or_cycleEndpoint packet with
    hsingleton | ⟨cycle, endpoint, hendpoint⟩
  · rcases hsingleton with ⟨singleton⟩
    exact ⟨FinFourPaidNonsingletonCycleOutcome.paidSingleton singleton⟩
  · rcases hendpoint with hstrict | hregeneration
    · exact ⟨FinFourPaidNonsingletonCycleOutcome.offMinimumEndpoint
        cycle endpoint hstrict⟩
    · rcases hregeneration with ⟨regeneration⟩
      exact ⟨FinFourPaidNonsingletonCycleOutcome.minimumRegeneration
        cycle endpoint regeneration⟩

end GameTheory
