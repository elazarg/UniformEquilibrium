/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import MathUE.Probability.DiscreteHazardConditionalMixture
import UniformEquilibrium.Diagnostics.Quitting.Frozen.ActualProfilePacket

/-!
# Conditioning literal frozen radial packets

The all-Continue successor of a literal packet is not a new independently
selected state: its live hazards are the exact shifts of the source profile's
hazards.  For every active radial coordinate, posterior conditioning then
rewrites that actual shifted hazard as a mixture of the shifted frozen source
and shifted inner-reset endpoints.

This is a source-matched conditioning connector.  If both endpoint components
survive the packet cutoff and the outer radial weight is strict, the reached
mixture retains a positive two-sided availability radius.  The posterior loss
has the sharp survival-denominator estimate from stopping-law conditioning.

This is not yet a restart at another frozen rank.  Nothing checked here
identifies either conditioned endpoint with the source or replacement chosen
by the frontier at a later rank.  Nor does the frozen packet theorem guarantee
positive component survival at its selected cutoff.  Those are the exact two
remaining premises needed before this connector can be iterated.
-/

noncomputable section

namespace GameTheory

open Math.Probability DiscreteHazard

variable {iota : Type} [Fintype iota] [DecidableEq iota]
variable {reward : {S : Finset iota // S.Nonempty} -> Payoff iota}

omit [DecidableEq iota] in
/-- The live hazard of the actual all-Continue successor is the literal shift
of the original live hazard. -/
theorem quittingBehaviorLiveHazard_allContinueProfileSpine_eq_shift
    (profile : (quittingGame reward).BehaviorProfile)
    (who : iota) (cutoff : Nat) :
    quittingBehaviorLiveHazard reward
        ((quittingAllContinueProfileSpine reward profile cutoff) who) =
      BooleanHazard.shift
        (quittingBehaviorLiveHazard reward (profile who)) cutoff := by
  funext time
  unfold quittingBehaviorLiveHazard BooleanHazard.shift
  exact quittingAllContinueProfileSpine_apply_liveHist
    reward profile cutoff who time

omit [DecidableEq iota] in
/-- A reached coordinate which was a stopping-law mixture remains exactly a
mixture of the two shifted component hazards, with posterior weight. -/
theorem quittingBehaviorLiveHazard_spine_stoppingLawMixture_eq_posteriorMix
    (profile : (quittingGame reward).BehaviorProfile) (who : iota)
    (source target : (quittingGame reward).BehaviorStrategy who)
    (lambda : Real) (hlambda0 : 0 <= lambda) (hlambda1 : lambda <= 1)
    (cutoff : Nat)
    (hcoordinate : profile who =
      quittingStoppingLawMixtureBehaviorStrategy reward who source target
        lambda hlambda0 hlambda1)
    (hpositive : 0 < ScalarHazard.mixedSurvival
      (BooleanHazard.toScalar (quittingBehaviorLiveHazard reward source))
      (BooleanHazard.toScalar (quittingBehaviorLiveHazard reward target))
      lambda cutoff) :
    quittingBehaviorLiveHazard reward
        ((quittingAllContinueProfileSpine reward profile cutoff) who) =
      BooleanHazard.convexMix
        (BooleanHazard.shift (quittingBehaviorLiveHazard reward source) cutoff)
        (BooleanHazard.shift (quittingBehaviorLiveHazard reward target) cutoff)
        (ScalarHazard.posteriorTargetWeight
          (BooleanHazard.toScalar (quittingBehaviorLiveHazard reward source))
          (BooleanHazard.toScalar (quittingBehaviorLiveHazard reward target))
          lambda cutoff)
        (ScalarHazard.posteriorTargetWeight_nonneg
          (BooleanHazard.toScalar (quittingBehaviorLiveHazard reward source))
          (BooleanHazard.toScalar (quittingBehaviorLiveHazard reward target))
          lambda
          hlambda0 hlambda1 cutoff)
        (ScalarHazard.posteriorTargetWeight_le_one
          (BooleanHazard.toScalar (quittingBehaviorLiveHazard reward source))
          (BooleanHazard.toScalar (quittingBehaviorLiveHazard reward target))
          lambda
          hlambda1 cutoff hpositive) := by
  rw [quittingBehaviorLiveHazard_allContinueProfileSpine_eq_shift,
    hcoordinate, quittingBehaviorLiveHazard_stoppingLawMixture]
  exact BooleanHazard.shift_convexMix _ _ lambda hlambda0 hlambda1 cutoff
    hpositive

namespace QuittingPositiveMinimumDebtTangentFamily

variable {witness : QuittingTerminalExploitabilityWitness reward}

/-- Live hazard of the frozen source component in one active radial
coordinate. -/
def frozenRadialOuterSourceHazard
    (frontier : QuittingPositiveMinimumDebtTangentFamily reward)
    (rank : Nat)
    (mover : {who // who ∈ frontier.positiveDebtSupport}) : BooleanHazard :=
  quittingBehaviorLiveHazard reward (frontier.source rank mover.1)

/-- Live hazard of the full inner reset component in one active radial
coordinate. -/
def frozenRadialOuterTargetHazard
    (frontier : QuittingPositiveMinimumDebtTangentFamily reward)
    (rank : Nat)
    (mover : {who // who ∈ frontier.positiveDebtSupport}) : BooleanHazard :=
  quittingBehaviorLiveHazard reward
    (frontier.frozenRadialInnerResetStrategy rank mover)

/-- Scalar view of the frozen source component hazard. -/
def frozenRadialOuterSourceScalarHazard
    (frontier : QuittingPositiveMinimumDebtTangentFamily reward)
    (rank : Nat)
    (mover : {who // who ∈ frontier.positiveDebtSupport}) : ScalarHazard :=
  BooleanHazard.toScalar (frontier.frozenRadialOuterSourceHazard rank mover)

/-- Scalar view of the inner reset component hazard. -/
def frozenRadialOuterTargetScalarHazard
    (frontier : QuittingPositiveMinimumDebtTangentFamily reward)
    (rank : Nat)
    (mover : {who // who ∈ frontier.positiveDebtSupport}) : ScalarHazard :=
  BooleanHazard.toScalar (frontier.frozenRadialOuterTargetHazard rank mover)

/-- Posterior outer radial weight after the displayed finite cutoff. -/
def frozenRadialReachedWeight
    (frontier : QuittingPositiveMinimumDebtTangentFamily reward)
    (rank : Nat)
    (weight : {who // who ∈ frontier.positiveDebtSupport} -> Real)
    (mover : {who // who ∈ frontier.positiveDebtSupport})
    (cutoff : Nat) : Real :=
  ScalarHazard.posteriorTargetWeight
    (frontier.frozenRadialOuterSourceScalarHazard rank mover)
    (frontier.frozenRadialOuterTargetScalarHazard rank mover)
    (weight mover) cutoff

/-- Two-sided component availability of a conditioned radial coordinate. -/
def frozenRadialReachedAvailabilityRadius
    (frontier : QuittingPositiveMinimumDebtTangentFamily reward)
    (rank : Nat)
    (weight : {who // who ∈ frontier.positiveDebtSupport} -> Real)
    (mover : {who // who ∈ frontier.positiveDebtSupport})
    (cutoff : Nat) : Real :=
  min (frontier.frozenRadialReachedWeight rank weight mover cutoff)
    (1 - frontier.frozenRadialReachedWeight rank weight mover cutoff)

/-- Strict prior weights and positive component survival give a positive
reached availability radius. -/
theorem frozenRadialReachedAvailabilityRadius_pos
    (frontier : QuittingPositiveMinimumDebtTangentFamily reward)
    (rank : Nat)
    (weight : {who // who ∈ frontier.positiveDebtSupport} -> Real)
    (mover : {who // who ∈ frontier.positiveDebtSupport})
    (cutoff : Nat)
    (hweight0 : 0 < weight mover) (hweight1 : weight mover < 1)
    (hsource : 0 <
      (frontier.frozenRadialOuterSourceScalarHazard rank mover).survival
        0 cutoff)
    (htarget : 0 <
      (frontier.frozenRadialOuterTargetScalarHazard rank mover).survival
        0 cutoff) :
    0 < frontier.frozenRadialReachedAvailabilityRadius
      rank weight mover cutoff := by
  have hposterior := ScalarHazard.posteriorTargetWeight_mem_Ioo
    (frontier.frozenRadialOuterSourceScalarHazard rank mover)
    (frontier.frozenRadialOuterTargetScalarHazard rank mover)
    (weight mover) hweight0 hweight1 cutoff hsource htarget
  exact lt_min hposterior.1 (sub_pos.mpr hposterior.2)

/-- Quantitative posterior loss at a reached radial coordinate.  The estimate
shows exactly why a lower survival denominator is needed for stable restart. -/
theorem abs_frozenRadialReachedWeight_sub_le
    (frontier : QuittingPositiveMinimumDebtTangentFamily reward)
    (rank : Nat)
    (weight : {who // who ∈ frontier.positiveDebtSupport} -> Real)
    (hweight0 : forall mover, 0 <= weight mover)
    (hweight1 : forall mover, weight mover <= 1)
    (mover : {who // who ∈ frontier.positiveDebtSupport})
    (cutoff : Nat) (lower : Real) (hlower : 0 < lower)
    (hmixed : lower <= ScalarHazard.mixedSurvival
      (frontier.frozenRadialOuterSourceScalarHazard rank mover)
      (frontier.frozenRadialOuterTargetScalarHazard rank mover)
      (weight mover) cutoff) :
    |frontier.frozenRadialReachedWeight rank weight mover cutoff -
        weight mover| <=
      weight mover * (1 - weight mover) / lower *
        |(frontier.frozenRadialOuterTargetScalarHazard rank mover).survival
            0 cutoff -
          (frontier.frozenRadialOuterSourceScalarHazard rank mover).survival
            0 cutoff| := by
  exact ScalarHazard.abs_posteriorTargetWeight_sub_le_of_mixedSurvival_lower
    (frontier.frozenRadialOuterSourceScalarHazard rank mover)
    (frontier.frozenRadialOuterTargetScalarHazard rank mover)
    (weight mover) (hweight0 mover) (hweight1 mover) cutoff hlower hmixed

/-- The exact posterior mixture hazard at a reached active coordinate. -/
def frozenRadialConditionedOuterHazard
    (frontier : QuittingPositiveMinimumDebtTangentFamily reward)
    (rank : Nat)
    (weight : {who // who ∈ frontier.positiveDebtSupport} -> Real)
    (hweight0 : forall mover, 0 <= weight mover)
    (hweight1 : forall mover, weight mover <= 1)
    (mover : {who // who ∈ frontier.positiveDebtSupport})
    (cutoff : Nat)
    (hpositive : 0 < ScalarHazard.mixedSurvival
      (frontier.frozenRadialOuterSourceScalarHazard rank mover)
      (frontier.frozenRadialOuterTargetScalarHazard rank mover)
      (weight mover) cutoff) : BooleanHazard :=
  BooleanHazard.convexMix
    (BooleanHazard.shift
      (frontier.frozenRadialOuterSourceHazard rank mover) cutoff)
    (BooleanHazard.shift
      (frontier.frozenRadialOuterTargetHazard rank mover) cutoff)
    (frontier.frozenRadialReachedWeight rank weight mover cutoff)
    (ScalarHazard.posteriorTargetWeight_nonneg
      (frontier.frozenRadialOuterSourceScalarHazard rank mover)
      (frontier.frozenRadialOuterTargetScalarHazard rank mover)
      (weight mover) (hweight0 mover) (hweight1 mover) cutoff)
    (ScalarHazard.posteriorTargetWeight_le_one
      (frontier.frozenRadialOuterSourceScalarHazard rank mover)
      (frontier.frozenRadialOuterTargetScalarHazard rank mover)
      (weight mover) (hweight1 mover) cutoff hpositive)

/-- Exact conditioning of one active coordinate at the actual literal packet
successor.  The source profile, cutoff, and successor are those stored by the
packet; no semantic source substitution occurs. -/
theorem frozenRadialLiteralPacket_successor_liveHazard_eq
    (frontier : QuittingPositiveMinimumDebtTangentFamily reward)
    (rank : Nat)
    (weight : {who // who ∈ frontier.positiveDebtSupport} -> Real)
    (hweight0 : forall mover, 0 <= weight mover)
    (hweight1 : forall mover, weight mover <= 1)
    (mover : {who // who ∈ frontier.positiveDebtSupport})
    {orientation : Finset iota} {first second : iota}
    {scale coefficient : Real}
    (packet : QuittingLiteralFiniteProfilePacket reward
      (frontier.frozenRadialPacketProfile rank weight hweight0 hweight1)
      orientation first second scale coefficient)
    (hpositive : 0 < ScalarHazard.mixedSurvival
      (frontier.frozenRadialOuterSourceScalarHazard rank mover)
      (frontier.frozenRadialOuterTargetScalarHazard rank mover)
      (weight mover) packet.length) :
    quittingBehaviorLiveHazard reward (packet.successorProfile mover.1) =
      frontier.frozenRadialConditionedOuterHazard rank weight
        hweight0 hweight1 mover packet.length hpositive := by
  apply quittingBehaviorLiveHazard_spine_stoppingLawMixture_eq_posteriorMix
    (profile := frontier.frozenRadialPacketProfile rank weight
      hweight0 hweight1)
    (who := mover.1)
    (source := frontier.source rank mover.1)
    (target := frontier.frozenRadialInnerResetStrategy rank mover)
    (lambda := weight mover) (hweight0 mover) (hweight1 mover)
    packet.length
  · exact frontier.frozenRadialPacketProfile_apply rank weight
      hweight0 hweight1 mover |>.trans (by
        simp [frozenRadialResetProfile])
  · exact hpositive

/-- Two fixed active labels survive conditioning at the same actual packet
successor.  This retains the packet's literal source and successor provenance;
the result intentionally stops before identifying a later frozen rank. -/
theorem frozenRadialLiteralPacket_twoLabel_conditionedKernel
    (frontier : QuittingPositiveMinimumDebtTangentFamily reward)
    (rank : Nat)
    (weight : {who // who ∈ frontier.positiveDebtSupport} -> Real)
    (hweight0 : forall mover, 0 <= weight mover)
    (hweight1 : forall mover, weight mover <= 1)
    (first second : {who // who ∈ frontier.positiveDebtSupport})
    {orientation : Finset iota} {scale coefficient : Real}
    (packet : QuittingLiteralFiniteProfilePacket reward
      (frontier.frozenRadialPacketProfile rank weight hweight0 hweight1)
      orientation first.1 second.1 scale coefficient)
    (hfirstPositive : 0 < ScalarHazard.mixedSurvival
      (frontier.frozenRadialOuterSourceScalarHazard rank first)
      (frontier.frozenRadialOuterTargetScalarHazard rank first)
      (weight first) packet.length)
    (hsecondPositive : 0 < ScalarHazard.mixedSurvival
      (frontier.frozenRadialOuterSourceScalarHazard rank second)
      (frontier.frozenRadialOuterTargetScalarHazard rank second)
      (weight second) packet.length) :
    first.1 ≠ second.1 ∧
      quittingBehaviorLiveHazard reward (packet.successorProfile first.1) =
        frontier.frozenRadialConditionedOuterHazard rank weight
          hweight0 hweight1 first packet.length hfirstPositive ∧
      quittingBehaviorLiveHazard reward (packet.successorProfile second.1) =
        frontier.frozenRadialConditionedOuterHazard rank weight
          hweight0 hweight1 second packet.length hsecondPositive := by
  exact ⟨packet.labels_ne,
    frozenRadialLiteralPacket_successor_liveHazard_eq
      frontier rank weight hweight0 hweight1 first packet hfirstPositive,
    frozenRadialLiteralPacket_successor_liveHazard_eq
      frontier rank weight hweight0 hweight1 second packet hsecondPositive⟩

/-- Component survival upgrades the exact two-label conditioning identity to
a positive two-sided availability statement at the actual successor. -/
theorem frozenRadialLiteralPacket_twoLabel_availableConditionedKernel
    (frontier : QuittingPositiveMinimumDebtTangentFamily reward)
    (rank : Nat)
    (weight : {who // who ∈ frontier.positiveDebtSupport} -> Real)
    (hweight0 : forall mover, 0 <= weight mover)
    (hweight1 : forall mover, weight mover <= 1)
    (first second : {who // who ∈ frontier.positiveDebtSupport})
    {orientation : Finset iota} {scale coefficient : Real}
    (packet : QuittingLiteralFiniteProfilePacket reward
      (frontier.frozenRadialPacketProfile rank weight hweight0 hweight1)
      orientation first.1 second.1 scale coefficient)
    (hfirstWeight0 : 0 < weight first) (hfirstWeight1 : weight first < 1)
    (hsecondWeight0 : 0 < weight second) (hsecondWeight1 : weight second < 1)
    (hfirstSource : 0 <
      (frontier.frozenRadialOuterSourceScalarHazard rank first).survival
        0 packet.length)
    (hfirstTarget : 0 <
      (frontier.frozenRadialOuterTargetScalarHazard rank first).survival
        0 packet.length)
    (hsecondSource : 0 <
      (frontier.frozenRadialOuterSourceScalarHazard rank second).survival
        0 packet.length)
    (hsecondTarget : 0 <
      (frontier.frozenRadialOuterTargetScalarHazard rank second).survival
        0 packet.length) :
    ∃ hfirstPositive : 0 < ScalarHazard.mixedSurvival
        (frontier.frozenRadialOuterSourceScalarHazard rank first)
        (frontier.frozenRadialOuterTargetScalarHazard rank first)
        (weight first) packet.length,
      ∃ hsecondPositive : 0 < ScalarHazard.mixedSurvival
          (frontier.frozenRadialOuterSourceScalarHazard rank second)
          (frontier.frozenRadialOuterTargetScalarHazard rank second)
          (weight second) packet.length,
        0 < frontier.frozenRadialReachedAvailabilityRadius
            rank weight first packet.length ∧
          0 < frontier.frozenRadialReachedAvailabilityRadius
            rank weight second packet.length ∧
          first.1 ≠ second.1 ∧
          quittingBehaviorLiveHazard reward
              (packet.successorProfile first.1) =
            frontier.frozenRadialConditionedOuterHazard rank weight
              hweight0 hweight1 first packet.length hfirstPositive ∧
          quittingBehaviorLiveHazard reward
              (packet.successorProfile second.1) =
            frontier.frozenRadialConditionedOuterHazard rank weight
              hweight0 hweight1 second packet.length hsecondPositive := by
  have hfirstPositive : 0 < ScalarHazard.mixedSurvival
      (frontier.frozenRadialOuterSourceScalarHazard rank first)
      (frontier.frozenRadialOuterTargetScalarHazard rank first)
      (weight first) packet.length := by
    unfold ScalarHazard.mixedSurvival
    exact add_pos
      (mul_pos (sub_pos.mpr hfirstWeight1) hfirstSource)
      (mul_pos hfirstWeight0 hfirstTarget)
  have hsecondPositive : 0 < ScalarHazard.mixedSurvival
      (frontier.frozenRadialOuterSourceScalarHazard rank second)
      (frontier.frozenRadialOuterTargetScalarHazard rank second)
      (weight second) packet.length := by
    unfold ScalarHazard.mixedSurvival
    exact add_pos
      (mul_pos (sub_pos.mpr hsecondWeight1) hsecondSource)
      (mul_pos hsecondWeight0 hsecondTarget)
  have hfirstRadius := frontier.frozenRadialReachedAvailabilityRadius_pos
    rank weight first packet.length hfirstWeight0 hfirstWeight1
    hfirstSource hfirstTarget
  have hsecondRadius := frontier.frozenRadialReachedAvailabilityRadius_pos
    rank weight second packet.length hsecondWeight0 hsecondWeight1
    hsecondSource hsecondTarget
  have hkernel := frozenRadialLiteralPacket_twoLabel_conditionedKernel
    frontier rank weight hweight0 hweight1 first second packet
    hfirstPositive hsecondPositive
  exact ⟨hfirstPositive, hsecondPositive, hfirstRadius, hsecondRadius,
    hkernel⟩

end QuittingPositiveMinimumDebtTangentFamily

end GameTheory
