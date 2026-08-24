/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.Frozen.RadialPacketExposure
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticPlateauIncidence
import UniformEquilibrium.Quitting.Paths.PersistentDeletedClockTwoLabel

/-!
# Literal finite packets from frozen radial profiles

This module records the executable part of the flat charged-circulation
construction without adding an artificial candidate anchor.  A packet is one
actual behavior profile, its literal live-root word through a finite cutoff,
and its actual all-Continue successor.  Two fixed active mover labels each
contribute a uniform positive multiple of the genuine frontier scale to that
finite word.  Every semantic candidate is the terminal semantic pair of the
corresponding actual profile spine, so source, successor, and internal Bellman
provenance are exact.

The result is deliberately frozen-source and branch-local.  It does not give
a positive availability radius at the successor, reproject another frozen
packet to that successor, or identify the two active circulation movers with
the mover/observer labels of `QuittingVanishingDebtAtomAccess`.  Those are
additional source-matching assertions, not fields of the checked radial
packet.  No small-debt seed or artificial candidate annotation is introduced.
-/

noncomputable section

namespace GameTheory

open Filter Math Math.Probability
open scoped BigOperators Topology

variable {iota : Type} [Fintype iota] [DecidableEq iota]
variable {reward : {S : Finset iota // S.Nonempty} -> Payoff iota}
variable {witness : QuittingTerminalExploitabilityWitness reward}

/-- One actual finite root word cut from a literal behavior profile.  The
orientation is an active player face; both persistent labels remain in that
face. -/
structure QuittingLiteralFiniteProfilePacket
    (reward : {S : Finset iota // S.Nonempty} -> Payoff iota)
    (profile : (quittingGame reward).BehaviorProfile)
    (orientation : Finset iota) (first second : iota)
    (scale coefficient : Real) where
  labels_ne : first ≠ second
  first_mem : first ∈ orientation
  second_mem : second ∈ orientation
  scale_pos : 0 < scale
  coefficient_pos : 0 < coefficient
  length : Nat
  length_pos : 0 < length
  first_hazard : coefficient * scale <=
    ∑ offset ∈ Finset.range length,
      quittingMarginalQuitHazard
        (quittingProfileLiveRoot reward profile) first offset
  second_hazard : coefficient * scale <=
    ∑ offset ∈ Finset.range length,
      quittingMarginalQuitHazard
        (quittingProfileLiveRoot reward profile) second offset

namespace QuittingLiteralFiniteProfilePacket

variable {profile : (quittingGame reward).BehaviorProfile}
  {orientation : Finset iota} {first second : iota}
  {scale coefficient : Real}

/-- The packet word consists of the literal roots reached along the source
profile's all-Continue spine. -/
def roots
    (_packet : QuittingLiteralFiniteProfilePacket reward profile orientation
      first second scale coefficient) : Nat -> iota -> PMF Bool :=
  quittingProfileLiveRoot reward profile

/-- Every packet candidate is the complete terminal semantic pair of the
actual profile reached at that offset. -/
def candidate
    (_packet : QuittingLiteralFiniteProfilePacket reward profile orientation
      first second scale coefficient) (offset : Nat) :
    QuittingTerminalSemanticPair iota :=
  quittingTerminalSemanticPair reward
    (quittingAllContinueProfileSpine reward profile offset)

/-- The actual behavior profile reached after the packet's all-Continue
word. -/
def successorProfile
    (packet : QuittingLiteralFiniteProfilePacket reward profile orientation
      first second scale coefficient) :
    (quittingGame reward).BehaviorProfile :=
  quittingAllContinueProfileSpine reward profile packet.length

@[simp] theorem candidate_zero
    (packet : QuittingLiteralFiniteProfilePacket reward profile orientation
      first second scale coefficient) :
    packet.candidate 0 = quittingTerminalSemanticPair reward profile := by
  rfl

@[simp] theorem candidate_length
    (packet : QuittingLiteralFiniteProfilePacket reward profile orientation
      first second scale coefficient) :
    packet.candidate packet.length =
      quittingTerminalSemanticPair reward packet.successorProfile := by
  rfl

/-- Every internal row is the exact semantic prefix of its literal reached
successor. -/
theorem exact_step
    (packet : QuittingLiteralFiniteProfilePacket reward profile orientation
      first second scale coefficient) (offset : Nat) :
    packet.candidate offset =
      quittingTerminalSemanticPrefix reward (packet.roots offset)
        (packet.candidate (offset + 1)) := by
  exact quittingTerminalSemanticPair_spine_eq_prefix reward profile offset

/-- Every literal packet candidate lies in the actual terminal semantic
carrier. -/
theorem candidate_mem_carrier
    (packet : QuittingLiteralFiniteProfilePacket reward profile orientation
      first second scale coefficient) (offset : Nat) :
    packet.candidate offset ∈ quittingTerminalSemanticCarrier reward := by
  exact quittingTerminalSemanticPair_mem_carrier reward
    (quittingAllContinueProfileSpine reward profile offset)

/-- Literal packet debt is coordinatewise nonnegative. -/
theorem debt_nonneg
    (packet : QuittingLiteralFiniteProfilePacket reward profile orientation
      first second scale coefficient) (offset : Nat) (who : iota) :
    0 <= quittingTerminalSemanticDebt (packet.candidate offset) who :=
  quittingTerminalSemanticDebt_nonneg_of_mem_carrier reward
    (packet.candidate_mem_carrier offset) who

/-- One reward-table bound controls every prescribed candidate coordinate in
every literal packet, independently of the frontier rank and cutoff. -/
theorem prescribed_le_globalBound
    (packet : QuittingLiteralFiniteProfilePacket reward profile orientation
      first second scale coefficient) (offset : Nat) (who : iota) :
    |(packet.candidate offset).1 who| <=
      2 * quittingRewardBound reward := by
  have hpayoff := abs_quittingTerminalPayoff_le reward
    (quittingAllContinueProfileSpine reward profile offset) who
    (abs_reward_le_quittingRewardBound reward)
  change |quittingTerminalPayoff reward
      (quittingAllContinueProfileSpine reward profile offset) who| <= _
  exact hpayoff.trans (by linarith [quittingRewardBound_nonneg reward])

/-- The same global bound controls every literal candidate debt coordinate. -/
theorem debt_le_globalBound
    (packet : QuittingLiteralFiniteProfilePacket reward profile orientation
      first second scale coefficient) (offset : Nat) (who : iota) :
    |quittingTerminalSemanticDebt (packet.candidate offset) who| <=
      2 * quittingRewardBound reward := by
  let reached := quittingAllContinueProfileSpine reward profile offset
  have hpayoff := abs_quittingTerminalPayoff_le reward reached who
    (abs_reward_le_quittingRewardBound reward)
  have hcap := abs_quittingContinuationBestResponseValue_le reward reached who
    (abs_reward_le_quittingRewardBound reward)
  unfold quittingTerminalSemanticDebt candidate quittingTerminalSemanticPair
  exact (abs_sub _ _).trans ((add_le_add hcap hpayoff).trans_eq (by ring))

end QuittingLiteralFiniteProfilePacket

omit [Fintype iota] [DecidableEq iota] in
/-- Finite union bound for one Boolean hazard: absorption by the cutoff is at
most the sum of the displayed Quit marginals. -/
theorem one_sub_quittingHazardSurvival_le_sum_marginal
    (hazard : Nat -> PMF Bool) (cutoff : Nat) :
    1 - quittingHazardSurvival hazard cutoff <=
      ∑ time ∈ Finset.range cutoff, (hazard time true).toReal := by
  rw [quittingHazardSurvival_eq_prod]
  have hcontinue : forall time,
      (hazard time false).toReal = 1 - (hazard time true).toReal := by
    intro time
    linarith [quittingHazard_continue_add_quit hazard time]
  simp_rw [hcontinue]
  exact one_sub_prod_one_sub_le_sum
    (fun time => (hazard time true).toReal) (Finset.range cutoff)
    (fun time _ => quittingHazard_quit_nonneg hazard time)
    (fun time _ => by
      linarith [quittingHazard_continue_nonneg hazard time,
        quittingHazard_continue_add_quit hazard time])

omit [DecidableEq iota] in
/-- Two fixed marginals with twice a positive ever-Quit exposure admit one
finite cutoff at which both raw marginal hazard sums exceed the exposure. -/
theorem exists_finiteCutoff_two_marginalHazardSums
    (profile : (quittingGame reward).BehaviorProfile)
    (first second : iota) (exposure : Real) (hexposure : 0 < exposure)
    (hfirst : 2 * exposure <=
      quittingBehaviorEverQuitMass reward (profile first))
    (hsecond : 2 * exposure <=
      quittingBehaviorEverQuitMass reward (profile second)) :
    ∃ cutoff, 0 < cutoff ∧
      exposure <= ∑ time ∈ Finset.range cutoff,
        quittingMarginalQuitHazard
          (quittingProfileLiveRoot reward profile) first time ∧
      exposure <= ∑ time ∈ Finset.range cutoff,
        quittingMarginalQuitHazard
          (quittingProfileLiveRoot reward profile) second time := by
  let roots := quittingProfileLiveRoot reward profile
  let firstHazard := quittingRootSequenceOwnHazard roots first
  let secondHazard := quittingRootSequenceOwnHazard roots second
  have hfirstHazard : firstHazard =
      quittingBehaviorLiveHazard reward (profile first) := rfl
  have hsecondHazard : secondHazard =
      quittingBehaviorLiveHazard reward (profile second) := rfl
  have hfirstTendsto : Tendsto
      (fun cutoff => 1 - quittingHazardSurvival firstHazard cutoff) atTop
      (nhds (quittingBehaviorEverQuitMass reward (profile first))) := by
    rw [hfirstHazard]
    simpa [quittingBehaviorEverQuitMass, quittingHazardEverQuitMass] using
      tendsto_const_nhds.sub
        (tendsto_quittingHazardSurvival_neverMass
          (quittingBehaviorLiveHazard reward (profile first)))
  have hsecondTendsto : Tendsto
      (fun cutoff => 1 - quittingHazardSurvival secondHazard cutoff) atTop
      (nhds (quittingBehaviorEverQuitMass reward (profile second))) := by
    rw [hsecondHazard]
    simpa [quittingBehaviorEverQuitMass, quittingHazardEverQuitMass] using
      tendsto_const_nhds.sub
        (tendsto_quittingHazardSurvival_neverMass
          (quittingBehaviorLiveHazard reward (profile second)))
  have hfirstEventually : ∀ᶠ cutoff in atTop,
      exposure < 1 - quittingHazardSurvival firstHazard cutoff :=
    (tendsto_order.1 hfirstTendsto).1 exposure (by linarith)
  have hsecondEventually : ∀ᶠ cutoff in atTop,
      exposure < 1 - quittingHazardSurvival secondHazard cutoff :=
    (tendsto_order.1 hsecondTendsto).1 exposure (by linarith)
  obtain ⟨cutoff, hfirstCutoff, hsecondCutoff⟩ :=
    (hfirstEventually.and hsecondEventually).exists
  have hfirstSum := one_sub_quittingHazardSurvival_le_sum_marginal
    firstHazard cutoff
  have hsecondSum := one_sub_quittingHazardSurvival_le_sum_marginal
    secondHazard cutoff
  have hcutoff : 0 < cutoff := by
    by_contra hnot
    have hzero : cutoff = 0 := Nat.eq_zero_of_not_pos hnot
    subst cutoff
    simp at hfirstCutoff
    linarith
  refine ⟨cutoff, hcutoff, ?_, ?_⟩
  · dsimp only [firstHazard, quittingRootSequenceOwnHazard] at hfirstSum
    simpa only [roots, quittingMarginalQuitHazard] using
      hfirstCutoff.le.trans hfirstSum
  · dsimp only [secondHazard, quittingRootSequenceOwnHazard] at hsecondSum
    simpa only [roots, quittingMarginalQuitHazard] using
      hsecondCutoff.le.trans hsecondSum

namespace QuittingPositiveMinimumDebtTangentFamily

/-- On the flat charged-circulation branch, one fixed active face and two
fixed distinct active movers generate literal finite packets at every
sufficiently late frozen rank.  Each mover contributes at least `kappa` times
the genuine frontier scale to the raw marginal Quit-hazard sum. -/
theorem exists_frozenRadialLiteralFiniteProfilePackets
    (frontier : QuittingPositiveMinimumDebtTangentFamily reward)
    (hcirculation : HasQuittingStoppingLawFlatChargedCirculation
      frontier.positiveDebtSupport frontier.tangent) :
    ∃ weight : {who // who ∈ frontier.positiveDebtSupport} -> Real,
      ∃ hweight0 : forall mover, 0 <= weight mover,
      ∃ hweight1 : forall mover, weight mover <= 1,
      ∃ first second : {who // who ∈ frontier.positiveDebtSupport},
        first ≠ second ∧ 0 < weight first ∧ 0 < weight second ∧
          ∃ kappa : Real, 0 < kappa ∧
            ∀ᶠ rank in atTop,
              Nonempty (QuittingLiteralFiniteProfilePacket reward
                (frontier.frozenRadialPacketProfile rank weight
                  hweight0 hweight1)
                frontier.positiveDebtSupport first.1 second.1
                (frontier.scale rank) kappa) := by
  obtain ⟨weight, hweight0, hweight1, hbalance, hcharge⟩ :=
    frontier.exists_frozenRadialBoundedCirculationWeights hcirculation
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
  refine ⟨weight, hweight0, hweight1, first, second, hne,
    hfirstWeight, hsecondWeight, kappa, hkappa, ?_⟩
  have hlambdaEventually : ∀ᶠ rank in atTop,
      frontier.scale rank < 1 / 2 :=
    (tendsto_order.1 frontier.scale_tendsto_zero).2 (1 / 2) (by norm_num)
  have hfirstGainEventually : ∀ᶠ rank in atTop,
      firstGain < frontier.frozenGain rank first :=
    (tendsto_order.1 (frontier.frozenRadialGain_tendsto first)).1 firstGain
      (by
        dsimp only [firstGain]
        linarith [frontier.frozenRadialTangentOwnerCharge_pos first])
  have hsecondGainEventually : ∀ᶠ rank in atTop,
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
  have hfirstScaled := mul_le_mul_of_nonneg_right hkappaFirst hlambda0
  have hsecondScaled := mul_le_mul_of_nonneg_right hkappaSecond hlambda0
  have hfirstExposure :
      2 * (kappa * frontier.scale rank) <=
        quittingBehaviorEverQuitMass reward (packetProfile first.1) := by
    apply le_trans _ hfirstMass
    calc
      2 * (kappa * frontier.scale rank) <=
          2 * ((weight first * firstGain / (4 * M)) *
            frontier.scale rank) := by linarith
      _ = weight first * frontier.scale rank * firstGain /
          (2 * M) := by field_simp [ne_of_gt hM]; ring
  have hsecondExposure :
      2 * (kappa * frontier.scale rank) <=
        quittingBehaviorEverQuitMass reward (packetProfile second.1) := by
    apply le_trans _ hsecondMass
    calc
      2 * (kappa * frontier.scale rank) <=
          2 * ((weight second * secondGain / (4 * M)) *
            frontier.scale rank) := by linarith
      _ = weight second * frontier.scale rank * secondGain /
          (2 * M) := by field_simp [ne_of_gt hM]; ring
  have hexposure : 0 < kappa * frontier.scale rank :=
    mul_pos hkappa (frontier.scale_pos rank)
  obtain ⟨cutoff, hcutoff, hfirstHazard, hsecondHazard⟩ :=
    exists_finiteCutoff_two_marginalHazardSums packetProfile first.1 second.1
      (kappa * frontier.scale rank) hexposure
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

end QuittingPositiveMinimumDebtTangentFamily

end GameTheory
