/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.Frozen.ConditionedActualProfilePacket

/-!
# The exact component-survival barrier for frozen packet restart

At a sufficiently late frozen rank, survival of the original source component
through a packet cutoff automatically implies survival of the inner reset
component: the latter retains the strictly positive `1 - scale` share of the
source stopping law.  Thus the four component-survival premises in the raw
two-label conditioning theorem reduce to two source-survival premises.

This reduction is sharp.  If a source component has zero survival while the
inner component survives, posterior conditioning assigns full weight to the
inner component and the two-sided availability radius is exactly zero.  If the
inner component also has zero survival, the conditioning event itself has zero
mass.  Consequently the frozen tangent-family data give the exact alternative
proved below: an available two-label conditioned kernel, or a killed source
component at one of the two labels.  The latter branch cannot be turned into a
restart without additional chronological source data.
-/

noncomputable section

namespace GameTheory

open Math.Probability DiscreteHazard

variable {iota : Type} [Fintype iota] [DecidableEq iota]
variable {reward : {S : Finset iota // S.Nonempty} -> Payoff iota}
variable {witness : QuittingTerminalExploitabilityWitness reward}

namespace QuittingPositiveMinimumDebtTangentFamily

/-- The circulation weights may be chosen strictly below one.  This removes
outer-weight saturation as a genuine restart obstruction; halving preserves
balance and keeps strictly positive aggregate charge. -/
theorem exists_frozenRadialStrictCirculationWeights
    (frontier : QuittingPositiveMinimumDebtTangentFamily reward)
    (hcirculation : HasQuittingStoppingLawFlatChargedCirculation
      frontier.positiveDebtSupport frontier.tangent) :
    ∃ weight : {who // who ∈ frontier.positiveDebtSupport} -> Real,
      (forall mover, 0 <= weight mover) ∧
      (forall mover, weight mover < 1) ∧
      (forall observer,
        ∑ mover, weight mover * frontier.tangent mover observer = 0) ∧
      0 < ∑ mover,
        weight mover * (-frontier.tangent mover mover.1) := by
  obtain ⟨raw, hraw0, hraw1, hbalance, hcharge⟩ :=
    frontier.exists_frozenRadialBoundedCirculationWeights hcirculation
  let weight : {who // who ∈ frontier.positiveDebtSupport} -> Real :=
    fun mover => raw mover / 2
  refine ⟨weight, ?_, ?_, ?_, ?_⟩
  · intro mover
    exact div_nonneg (hraw0 mover) (by norm_num)
  · intro mover
    dsimp only [weight]
    linarith [hraw1 mover]
  · intro observer
    calc
      (∑ mover, weight mover * frontier.tangent mover observer) =
          (∑ mover, raw mover * frontier.tangent mover observer) / 2 := by
        dsimp only [weight]
        simp only [div_mul_eq_mul_div]
        rw [Finset.sum_div]
      _ = 0 := by rw [hbalance observer, zero_div]
  · have hhalf : 0 <
        (∑ mover, raw mover * (-frontier.tangent mover mover.1)) / 2 :=
      div_pos hcharge (by norm_num)
    convert hhalf using 1
    dsimp only [weight]
    simp only [div_mul_eq_mul_div]
    rw [Finset.sum_div]

/-- Any bounded balanced weight family with positive diagonal charge yields
literal two-label packets.  Exposing the weights as inputs lets the strict
weights above, rather than an independently reselected bounded family, feed
the chronological packet construction. -/
theorem exists_frozenRadialLiteralFiniteProfilePackets_of_weights
    (frontier : QuittingPositiveMinimumDebtTangentFamily reward)
    (weight : {who // who ∈ frontier.positiveDebtSupport} -> Real)
    (hweight0 : forall mover, 0 <= weight mover)
    (hweight1 : forall mover, weight mover <= 1)
    (hbalance : forall observer,
      ∑ mover, weight mover * frontier.tangent mover observer = 0)
    (hcharge : 0 < ∑ mover,
      weight mover * (-frontier.tangent mover mover.1)) :
    ∃ first second : {who // who ∈ frontier.positiveDebtSupport},
      first ≠ second ∧ 0 < weight first ∧ 0 < weight second ∧
        ∃ kappa : Real, 0 < kappa ∧
          ∀ᶠ rank in Filter.atTop,
            Nonempty (QuittingLiteralFiniteProfilePacket reward
              (frontier.frozenRadialPacketProfile rank weight
                hweight0 hweight1)
              frontier.positiveDebtSupport first.1 second.1
              (frontier.scale rank) kappa) := by
  obtain ⟨first, second, hne, hfirstWeight, hsecondWeight⟩ :=
    frontier.exists_two_positive_frozenRadialCirculationWeights
      weight hweight0 hbalance hcharge
  obtain ⟨bound, hbound0, hreward⟩ := exists_quittingRewardBound reward
  let M := bound + 1
  let firstGain := -frontier.tangent first first.1 / 2
  let secondGain := -frontier.tangent second second.1 / 2
  let kappa := min (weight first * firstGain / (4 * M))
    (weight second * secondGain / (4 * M))
  have hM : 0 < M := by
    dsimp only [M]
    linarith
  have hrewardM : forall terminal player, |reward terminal player| <= M := by
    intro terminal player
    exact (hreward terminal player).trans (by dsimp only [M]; linarith)
  have hfirstGain : 0 < firstGain := by
    dsimp only [firstGain]
    linarith [frontier.frozenRadialTangentOwnerCharge_pos first]
  have hsecondGain : 0 < secondGain := by
    dsimp only [secondGain]
    linarith [frontier.frozenRadialTangentOwnerCharge_pos second]
  have hkappa : 0 < kappa := by
    dsimp only [kappa]
    exact lt_min
      (div_pos (mul_pos hfirstWeight hfirstGain) (by positivity))
      (div_pos (mul_pos hsecondWeight hsecondGain) (by positivity))
  refine ⟨first, second, hne, hfirstWeight, hsecondWeight,
    kappa, hkappa, ?_⟩
  have hlambdaEventually : ∀ᶠ rank in Filter.atTop,
      frontier.scale rank < 1 / 2 :=
    (tendsto_order.1 frontier.scale_tendsto_zero).2 (1 / 2) (by norm_num)
  have hfirstGainEventually : ∀ᶠ rank in Filter.atTop,
      firstGain < frontier.frozenGain rank first :=
    (tendsto_order.1 (frontier.frozenRadialGain_tendsto first)).1 firstGain
      (by
        dsimp only [firstGain]
        linarith [frontier.frozenRadialTangentOwnerCharge_pos first])
  have hsecondGainEventually : ∀ᶠ rank in Filter.atTop,
      secondGain < frontier.frozenGain rank second :=
    (tendsto_order.1 (frontier.frozenRadialGain_tendsto second)).1 secondGain
      (by
        dsimp only [secondGain]
        linarith [frontier.frozenRadialTangentOwnerCharge_pos second])
  filter_upwards [hlambdaEventually, hfirstGainEventually,
    hsecondGainEventually] with rank hlambdaHalf hfirstActual hsecondActual
  let packetProfile := frontier.frozenRadialPacketProfile rank weight
    hweight0 hweight1
  have hlambda0 : 0 <= frontier.scale rank := (frontier.scale_pos rank).le
  have hfirstEffective : weight first * frontier.scale rank <= 1 / 2 := by
    have hle := mul_le_mul_of_nonneg_right (hweight1 first) hlambda0
    linarith
  have hsecondEffective : weight second * frontier.scale rank <= 1 / 2 := by
    have hle := mul_le_mul_of_nonneg_right (hweight1 second) hlambda0
    linarith
  have hfirstMass := frontier.frozenRadialPacket_everQuitMass_ge
    rank weight hweight0 hweight1 first firstGain M hM hrewardM
      hfirstActual.le hfirstEffective
  have hsecondMass := frontier.frozenRadialPacket_everQuitMass_ge
    rank weight hweight0 hweight1 second secondGain M hM hrewardM
      hsecondActual.le hsecondEffective
  have hkappaFirst : kappa <= weight first * firstGain / (4 * M) :=
    min_le_left _ _
  have hkappaSecond : kappa <= weight second * secondGain / (4 * M) :=
    min_le_right _ _
  have hfirstExposure :
      2 * (kappa * frontier.scale rank) <=
        quittingBehaviorEverQuitMass reward (packetProfile first.1) := by
    apply le_trans _ hfirstMass
    calc
      2 * (kappa * frontier.scale rank) <=
          2 * ((weight first * firstGain / (4 * M)) *
            frontier.scale rank) := by
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right hkappaFirst hlambda0) (by norm_num)
      _ = weight first * frontier.scale rank * firstGain / (2 * M) := by
        field_simp [ne_of_gt hM]
        ring
  have hsecondExposure :
      2 * (kappa * frontier.scale rank) <=
        quittingBehaviorEverQuitMass reward (packetProfile second.1) := by
    apply le_trans _ hsecondMass
    calc
      2 * (kappa * frontier.scale rank) <=
          2 * ((weight second * secondGain / (4 * M)) *
            frontier.scale rank) := by
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right hkappaSecond hlambda0) (by norm_num)
      _ = weight second * frontier.scale rank * secondGain / (2 * M) := by
        field_simp [ne_of_gt hM]
        ring
  have hexposure : 0 < kappa * frontier.scale rank :=
    mul_pos hkappa (frontier.scale_pos rank)
  obtain ⟨cutoff, hcutoff, hfirstHazard, hsecondHazard⟩ :=
    exists_finiteCutoff_two_marginalHazardSums packetProfile
      first.1 second.1 (kappa * frontier.scale rank) hexposure
      hfirstExposure hsecondExposure
  exact ⟨{
    labels_ne := Subtype.coe_ne_coe.mpr hne
    first_mem := first.property
    second_mem := second.property
    scale_pos := frontier.scale_pos rank
    coefficient_pos := hkappa
    length := cutoff
    length_pos := hcutoff
    first_hazard := hfirstHazard
    second_hazard := hsecondHazard }⟩

/-- A charged circulation therefore produces literal packets whose outer
weights are strict at every coordinate. -/
theorem exists_frozenRadialStrictLiteralFiniteProfilePackets
    (frontier : QuittingPositiveMinimumDebtTangentFamily reward)
    (hcirculation : HasQuittingStoppingLawFlatChargedCirculation
      frontier.positiveDebtSupport frontier.tangent) :
    ∃ weight : {who // who ∈ frontier.positiveDebtSupport} -> Real,
      ∃ hweight0 : forall mover, 0 <= weight mover,
      ∃ hweightLt : forall mover, weight mover < 1,
      ∃ first second : {who // who ∈ frontier.positiveDebtSupport},
        first ≠ second ∧ 0 < weight first ∧ 0 < weight second ∧
          ∃ kappa : Real, 0 < kappa ∧
            ∀ᶠ rank in Filter.atTop,
              Nonempty (QuittingLiteralFiniteProfilePacket reward
                (frontier.frozenRadialPacketProfile rank weight hweight0
                  (fun mover => (hweightLt mover).le))
                frontier.positiveDebtSupport first.1 second.1
                (frontier.scale rank) kappa) := by
  obtain ⟨weight, hweight0, hweightLt, hbalance, hcharge⟩ :=
    frontier.exists_frozenRadialStrictCirculationWeights hcirculation
  let hweight1 : forall mover, weight mover <= 1 :=
    fun mover => (hweightLt mover).le
  obtain ⟨first, second, hne, hfirst, hsecond, kappa, hkappa, hpackets⟩ :=
    frontier.exists_frozenRadialLiteralFiniteProfilePackets_of_weights
      weight hweight0 hweight1 hbalance hcharge
  exact ⟨weight, hweight0, hweightLt, first, second, hne,
    hfirst, hsecond, kappa, hkappa, hpackets⟩

/-- Scalar live hazard of the unscaled replacement endpoint. -/
def frozenRadialReplacementScalarHazard
    (frontier : QuittingPositiveMinimumDebtTangentFamily reward)
    (rank : Nat)
    (mover : {who // who ∈ frontier.positiveDebtSupport}) : ScalarHazard :=
  BooleanHazard.toScalar
    (quittingBehaviorLiveHazard reward (frontier.replacement mover rank))

/-- The inner endpoint's finite survival is exactly the stopping-law mixture
of the source and the unscaled replacement survivals. -/
theorem frozenRadialOuterTargetScalarHazard_survival_eq
    (frontier : QuittingPositiveMinimumDebtTangentFamily reward)
    (rank : Nat)
    (mover : {who // who ∈ frontier.positiveDebtSupport})
    (cutoff : Nat) :
    (frontier.frozenRadialOuterTargetScalarHazard rank mover).survival
        0 cutoff =
      ScalarHazard.mixedSurvival
        (frontier.frozenRadialOuterSourceScalarHazard rank mover)
        (frontier.frozenRadialReplacementScalarHazard rank mover)
        (frontier.scale rank) cutoff := by
  unfold frozenRadialOuterTargetScalarHazard frozenRadialOuterTargetHazard
    frozenRadialInnerResetStrategy frozenRadialOuterSourceScalarHazard
    frozenRadialOuterSourceHazard frozenRadialReplacementScalarHazard
  rw [quittingBehaviorLiveHazard_stoppingLawMixture,
    BooleanHazard.toScalar_convexMix, ScalarHazard.convexMix_survival]

/-- Before the reset scale reaches one, source survival forces survival of the
inner reset component at the same finite cutoff. -/
theorem frozenRadialOuterTargetScalarHazard_survival_pos_of_source
    (frontier : QuittingPositiveMinimumDebtTangentFamily reward)
    (rank : Nat)
    (mover : {who // who ∈ frontier.positiveDebtSupport})
    (cutoff : Nat) (hscale : frontier.scale rank < 1)
    (hsource : 0 <
      (frontier.frozenRadialOuterSourceScalarHazard rank mover).survival
        0 cutoff) :
    0 < (frontier.frozenRadialOuterTargetScalarHazard rank mover).survival
      0 cutoff := by
  rw [frontier.frozenRadialOuterTargetScalarHazard_survival_eq]
  unfold ScalarHazard.mixedSurvival
  have hreplacement : 0 <=
      (frontier.frozenRadialReplacementScalarHazard rank mover).survival
        0 cutoff :=
    ScalarHazard.survival_nonneg _ 0 cutoff
  exact add_pos_of_pos_of_nonneg
    (mul_pos (sub_pos.mpr hscale) hsource)
    (mul_nonneg (frontier.scale_pos rank).le hreplacement)

/-- A killed source component and a surviving inner component collapse the
posterior outer coordinate to the inner endpoint.  Its two-sided availability
radius is therefore exactly zero. -/
theorem frozenRadialReachedAvailabilityRadius_eq_zero_of_sourceSurvival_eq_zero
    (frontier : QuittingPositiveMinimumDebtTangentFamily reward)
    (rank : Nat)
    (weight : {who // who ∈ frontier.positiveDebtSupport} -> Real)
    (mover : {who // who ∈ frontier.positiveDebtSupport})
    (cutoff : Nat)
    (hweight : 0 < weight mover)
    (hsource :
      (frontier.frozenRadialOuterSourceScalarHazard rank mover).survival
        0 cutoff = 0)
    (htarget : 0 <
      (frontier.frozenRadialOuterTargetScalarHazard rank mover).survival
        0 cutoff) :
    frontier.frozenRadialReachedAvailabilityRadius
      rank weight mover cutoff = 0 := by
  have hdenominator : ScalarHazard.mixedSurvival
      (frontier.frozenRadialOuterSourceScalarHazard rank mover)
      (frontier.frozenRadialOuterTargetScalarHazard rank mover)
      (weight mover) cutoff =
        weight mover *
          (frontier.frozenRadialOuterTargetScalarHazard rank mover).survival
            0 cutoff := by
    unfold ScalarHazard.mixedSurvival
    rw [hsource]
    ring
  have hdenominatorPos : 0 < ScalarHazard.mixedSurvival
      (frontier.frozenRadialOuterSourceScalarHazard rank mover)
      (frontier.frozenRadialOuterTargetScalarHazard rank mover)
      (weight mover) cutoff := by
    rw [hdenominator]
    exact mul_pos hweight htarget
  have hposterior : frontier.frozenRadialReachedWeight
      rank weight mover cutoff = 1 := by
    unfold frozenRadialReachedWeight ScalarHazard.posteriorTargetWeight
    rw [hdenominator]
    exact div_self (ne_of_gt (mul_pos hweight htarget))
  unfold frozenRadialReachedAvailabilityRadius
  rw [hposterior]
  norm_num

/-- The executable, positive-radius branch of a conditioned two-label packet. -/
def HasFrozenRadialTwoLabelAvailableConditionedKernel
    (frontier : QuittingPositiveMinimumDebtTangentFamily reward)
    (rank : Nat)
    (weight : {who // who ∈ frontier.positiveDebtSupport} -> Real)
    (hweight0 : forall mover, 0 <= weight mover)
    (hweight1 : forall mover, weight mover <= 1)
    (first second : {who // who ∈ frontier.positiveDebtSupport})
    {orientation : Finset iota} {scale coefficient : Real}
    (packet : QuittingLiteralFiniteProfilePacket reward
      (frontier.frozenRadialPacketProfile rank weight hweight0 hweight1)
      orientation first.1 second.1 scale coefficient) : Prop :=
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
        quittingBehaviorLiveHazard reward (packet.successorProfile first.1) =
          frontier.frozenRadialConditionedOuterHazard rank weight
            hweight0 hweight1 first packet.length hfirstPositive ∧
        quittingBehaviorLiveHazard reward (packet.successorProfile second.1) =
          frontier.frozenRadialConditionedOuterHazard rank weight
            hweight0 hweight1 second packet.length hsecondPositive

/-- The sole component-survival obstruction after strict scaling: one of the
two frozen source marginals is killed before the packet endpoint. -/
def HasFrozenRadialTwoLabelKilledSource
    (frontier : QuittingPositiveMinimumDebtTangentFamily reward)
    (rank : Nat)
    (first second : {who // who ∈ frontier.positiveDebtSupport})
    (cutoff : Nat) : Prop :=
  (frontier.frozenRadialOuterSourceScalarHazard rank first).survival
      0 cutoff = 0 ∨
    (frontier.frozenRadialOuterSourceScalarHazard rank second).survival
      0 cutoff = 0

/-- At a late rank, strict outer weights leave exactly one obstruction to a
two-label available conditioned kernel: one of the two original source
components has zero survival through the literal packet cutoff. -/
theorem frozenRadialLiteralPacket_twoLabel_available_or_sourceKilled
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
    (hscale : frontier.scale rank < 1)
    (hfirstWeight0 : 0 < weight first)
    (hfirstWeight1 : weight first < 1)
    (hsecondWeight0 : 0 < weight second)
    (hsecondWeight1 : weight second < 1) :
    (∃ hfirstPositive : 0 < ScalarHazard.mixedSurvival
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
              hweight0 hweight1 second packet.length hsecondPositive) ∨
      (frontier.frozenRadialOuterSourceScalarHazard rank first).survival
          0 packet.length = 0 ∨
        (frontier.frozenRadialOuterSourceScalarHazard rank second).survival
          0 packet.length = 0 := by
  have hfirstNonneg := ScalarHazard.survival_nonneg
    (frontier.frozenRadialOuterSourceScalarHazard rank first)
    0 packet.length
  have hsecondNonneg := ScalarHazard.survival_nonneg
    (frontier.frozenRadialOuterSourceScalarHazard rank second)
    0 packet.length
  rcases hfirstNonneg.eq_or_lt with hfirstZero | hfirstSource
  · exact Or.inr (Or.inl hfirstZero.symm)
  rcases hsecondNonneg.eq_or_lt with hsecondZero | hsecondSource
  · exact Or.inr (Or.inr hsecondZero.symm)
  have hfirstTarget :=
    frontier.frozenRadialOuterTargetScalarHazard_survival_pos_of_source
      rank first packet.length hscale hfirstSource
  have hsecondTarget :=
    frontier.frozenRadialOuterTargetScalarHazard_survival_pos_of_source
      rank second packet.length hscale hsecondSource
  exact Or.inl
    (frontier.frozenRadialLiteralPacket_twoLabel_availableConditionedKernel
      rank weight hweight0 hweight1 first second packet
      hfirstWeight0 hfirstWeight1 hsecondWeight0 hsecondWeight1
      hfirstSource hfirstTarget hsecondSource hsecondTarget)

/-- **Strict frozen packets reach the exact restart frontier.**

Every flat charged circulation produces, at all sufficiently late ranks, one
literal actual-source packet satisfying exactly one useful disjunction: its
two conditioned labels retain positive availability, or an original source
component has already been killed by the chosen cutoff.  No replacement or
artificial candidate is substituted for the packet successor. -/
theorem exists_frozenRadialStrictPackets_available_or_sourceKilled
    (frontier : QuittingPositiveMinimumDebtTangentFamily reward)
    (hcirculation : HasQuittingStoppingLawFlatChargedCirculation
      frontier.positiveDebtSupport frontier.tangent) :
    ∃ weight : {who // who ∈ frontier.positiveDebtSupport} -> Real,
      ∃ hweight0 : forall mover, 0 <= weight mover,
      ∃ hweightLt : forall mover, weight mover < 1,
      ∃ first second : {who // who ∈ frontier.positiveDebtSupport},
        first ≠ second ∧ 0 < weight first ∧ 0 < weight second ∧
          ∃ kappa : Real, 0 < kappa ∧
            ∀ᶠ rank in Filter.atTop,
              ∃ packet : QuittingLiteralFiniteProfilePacket reward
                  (frontier.frozenRadialPacketProfile rank weight hweight0
                    (fun mover => (hweightLt mover).le))
                  frontier.positiveDebtSupport first.1 second.1
                  (frontier.scale rank) kappa,
                HasFrozenRadialTwoLabelAvailableConditionedKernel frontier
                    rank weight hweight0 (fun mover => (hweightLt mover).le)
                    first second packet ∨
                  HasFrozenRadialTwoLabelKilledSource frontier rank first
                    second packet.length := by
  obtain ⟨weight, hweight0, hweightLt, first, second, hne,
      hfirst, hsecond, kappa, hkappa, hpackets⟩ :=
    frontier.exists_frozenRadialStrictLiteralFiniteProfilePackets hcirculation
  refine ⟨weight, hweight0, hweightLt, first, second, hne,
    hfirst, hsecond, kappa, hkappa, ?_⟩
  have hscale : ∀ᶠ rank in Filter.atTop, frontier.scale rank < 1 :=
    (tendsto_order.1 frontier.scale_tendsto_zero).2 1 zero_lt_one
  filter_upwards [hpackets, hscale] with rank hpacket hscaleRank
  obtain ⟨packet⟩ := hpacket
  refine ⟨packet, ?_⟩
  simpa [HasFrozenRadialTwoLabelAvailableConditionedKernel,
    HasFrozenRadialTwoLabelKilledSource] using
    (frontier.frozenRadialLiteralPacket_twoLabel_available_or_sourceKilled
      rank weight hweight0 (fun mover => (hweightLt mover).le)
      first second packet hscaleRank hfirst (hweightLt first)
      hsecond (hweightLt second))

end QuittingPositiveMinimumDebtTangentFamily

end GameTheory
