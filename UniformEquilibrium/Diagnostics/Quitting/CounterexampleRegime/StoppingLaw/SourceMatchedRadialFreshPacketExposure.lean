/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegime.StoppingLaw.SourceMatchedRadialResetCube
import UniformEquilibrium.Quitting.Cycles.PhaseSwitchResiduals
import UniformEquilibrium.Quitting.Paths.StoppingLawExposure

/-!
# Finite exposure in fresh source-matched radial packets

Positive diagonal charge of a complete stopping-law reset forces finite
stopping mass.  A balanced positive circulation has at least two positive
radial coordinates, so a fresh simultaneous radial packet exposes every
deleted-player clock as well as the joint clock.  The result is deliberately
packet-local: no repetition or moving-source estimate is asserted.
-/

noncomputable section

namespace GameTheory

open Filter Finset Math.Probability
open scoped BigOperators Topology

variable {iota : Type} [Fintype iota] [DecidableEq iota]
variable {reward : {S : Finset iota // S.Nonempty} -> Payoff iota}
variable {witness : QuittingTerminalExploitabilityWitness reward}

namespace QuittingCounterexampleStoppingLawFrontier

/-- The normalized owner debt drop is exactly the unscaled replacement's
prescribed payoff gain. -/
theorem actualGain_eq_endpointPayoffGain
    (frontier : QuittingCounterexampleStoppingLawFrontier witness)
    (rank : Nat) (mover : {who // who ∈ frontier.active}) :
    frontier.actualGain rank mover =
      quittingTerminalPayoff reward
          (Function.update (frontier.profiles (frontier.subseq rank)) mover.1
            (frontier.bestResponse mover (frontier.subseq rank))) mover.1 -
        quittingTerminalPayoff reward
          (frontier.profiles (frontier.subseq rank)) mover.1 := by
  have hlambda := frontier.lambda_pos (frontier.subseq rank)
  have hpay := quittingTerminalPayoff_stoppingLawMixture_sub_eq
    reward (frontier.profiles (frontier.subseq rank)) mover.1
      (frontier.bestResponse mover (frontier.subseq rank))
      (frontier.lambda (frontier.subseq rank)) hlambda.le
      (frontier.lambda_le_one (frontier.subseq rank))
  unfold actualGain actualDebtDirection
    quittingStoppingLawNormalizedDebtDirection
    quittingTerminalSemanticDebtChange quittingTerminalSemanticDebt
    quittingTerminalSemanticPair quittingStoppingLawResetProfile
  dsimp only
  rw [quittingContinuationBestResponseValue_update_self]
  field_simp [ne_of_gt hlambda]
  linarith [hpay]

/-- Actual finite-rank owner gains converge to the positive diagonal charge
of the limiting tangent column. -/
theorem actualGain_tendsto
    (frontier : QuittingCounterexampleStoppingLawFrontier witness)
    (mover : {who // who ∈ frontier.active}) :
    Tendsto (fun rank => frontier.actualGain rank mover) atTop
      (nhds (-frontier.tangent mover mover.1)) := by
  simpa [actualGain, actualDebtDirection] using
    (frontier.tangent_tendsto mover mover.1).neg

/-- Every active tangent has a strictly positive limiting owner charge. -/
theorem tangentOwnerCharge_pos
    (frontier : QuittingCounterexampleStoppingLawFrontier witness)
    (mover : {who // who ∈ frontier.active}) :
    0 < -frontier.tangent mover mover.1 := by
  have hdebt : 0 < quittingTerminalSemanticDebt frontier.base mover.1 :=
    (frontier.active_iff mover.1).mp mover.property
  have hdiag := frontier.tangent_diagonal mover
  linarith

/-- Exact balance with positive diagonal charge requires at least two
positive radial coordinates. -/
theorem exists_two_positive_boundedRadialCirculationWeights
    (frontier : QuittingCounterexampleStoppingLawFrontier witness)
    (weight : {who // who ∈ frontier.active} -> Real)
    (hweight0 : forall mover, 0 <= weight mover)
    (hbalance : forall observer,
      ∑ mover, weight mover * frontier.tangent mover observer = 0)
    (hcharge : 0 < ∑ mover,
      weight mover * (-frontier.tangent mover mover.1)) :
    ∃ first second : {who // who ∈ frontier.active},
      first ≠ second ∧ 0 < weight first ∧ 0 < weight second := by
  have hterm0 : forall mover,
      0 <= weight mover * (-frontier.tangent mover mover.1) := by
    intro mover
    exact mul_nonneg (hweight0 mover) (frontier.tangentOwnerCharge_pos mover).le
  obtain ⟨first, _hfirstMem, hfirstTerm⟩ :=
    (Finset.sum_pos_iff_of_nonneg
      (s := (Finset.univ : Finset {who // who ∈ frontier.active}))
      (fun mover _ => hterm0 mover)).mp hcharge
  have hfirstWeight : 0 < weight first := by
    by_contra hfirst
    have hzero : weight first = 0 :=
      le_antisymm (le_of_not_gt hfirst) (hweight0 first)
    rw [hzero, zero_mul] at hfirstTerm
    exact (lt_irrefl 0) hfirstTerm
  by_contra hpair
  have hnoSecond : forall second, second ≠ first ->
      ¬0 < weight second := by
    intro second hne hsecond
    exact hpair ⟨first, second, Ne.symm hne, hfirstWeight, hsecond⟩
  have hotherZero : forall other, other ≠ first -> weight other = 0 := by
    intro other hne
    exact le_antisymm (le_of_not_gt (hnoSecond other hne))
      (hweight0 other)
  have hsum :
      (∑ mover, weight mover * frontier.tangent mover first.1) =
        weight first * frontier.tangent first first.1 := by
    apply Finset.sum_eq_single first
    · intro other _ hne
      rw [hotherZero other hne, zero_mul]
    · simp
  have hbalanced := hbalance first.1
  rw [hsum] at hbalanced
  have hnegative : weight first * frontier.tangent first first.1 < 0 := by
    nlinarith [frontier.tangentOwnerCharge_pos first]
  linarith

/-- The simultaneous fresh packet is the full active face of the radial reset
cube at one source-matched rank. -/
def sourceMatchedRadialFreshPacketProfile
    (frontier : QuittingCounterexampleStoppingLawFrontier witness)
    (rank : Nat) (weight : {who // who ∈ frontier.active} -> Real)
    (hweight0 : forall mover, 0 <= weight mover)
    (hweight1 : forall mover, weight mover <= 1) :
    (quittingGame reward).BehaviorProfile :=
  (frontier.sourceMatchedRadialResetCubeData rank weight hweight0 hweight1).profile
    frontier.active

/-- An active marginal of the full fresh packet is its literal nested radial
stopping-law reset. -/
theorem sourceMatchedRadialFreshPacketProfile_apply
    (frontier : QuittingCounterexampleStoppingLawFrontier witness)
    (rank : Nat) (weight : {who // who ∈ frontier.active} -> Real)
    (hweight0 : forall mover, 0 <= weight mover)
    (hweight1 : forall mover, weight mover <= 1)
    (mover : {who // who ∈ frontier.active}) :
    frontier.sourceMatchedRadialFreshPacketProfile rank weight hweight0
        hweight1 mover.1 =
      frontier.sourceMatchedRadialResetProfile rank mover (weight mover)
        (hweight0 mover) (hweight1 mover) mover.1 := by
  let data := frontier.sourceMatchedRadialResetCubeData rank weight
    hweight0 hweight1
  change data.profile frontier.active mover.1 = _
  rw [data.profile_apply_of_mem frontier.active mover.1 mover.property]
  simp only [sourceMatchedRadialResetProfile, Function.update_self]
  have htarget : data.target mover.1 =
      frontier.sourceMatchedInnerResetStrategy rank mover :=
    frontier.sourceMatchedRadialCubeTarget_active rank mover
  have hscale : data.scale mover.1 = weight mover :=
    frontier.sourceMatchedRadialCubeScale_active weight mover
  have hsource : data.source mover.1 =
      frontier.profiles (frontier.subseq rank) mover.1 := rfl
  rw [htarget, hsource]
  simpa only using
    quittingStoppingLawMixtureBehaviorStrategy_congr_scale reward mover.1
      (frontier.profiles (frontier.subseq rank) mover.1)
      (frontier.sourceMatchedInnerResetStrategy rank mover)
      (data.scale mover.1) (weight mover) (data.scale_nonneg mover.1)
      (data.scale_le_one mover.1) hscale

/-- A positive lower bound on the finite-rank owner gain yields proportional
ever-quit mass in that mover's fresh radial marginal. -/
theorem sourceMatchedRadialFreshPacket_everQuitMass_ge
    (frontier : QuittingCounterexampleStoppingLawFrontier witness)
    (rank : Nat) (weight : {who // who ∈ frontier.active} -> Real)
    (hweight0 : forall mover, 0 <= weight mover)
    (hweight1 : forall mover, weight mover <= 1)
    (mover : {who // who ∈ frontier.active})
    (gainFloor M : Real) (hM : 0 < M)
    (hreward : forall terminal player, |reward terminal player| <= M)
    (hgain : gainFloor <= frontier.actualGain rank mover)
    (heffectiveHalf :
      weight mover * frontier.lambda (frontier.subseq rank) <= 1 / 2) :
    weight mover * frontier.lambda (frontier.subseq rank) * gainFloor /
          (2 * M) <=
      quittingBehaviorEverQuitMass reward
        (frontier.sourceMatchedRadialFreshPacketProfile rank weight hweight0
          hweight1 mover.1) := by
  rw [frontier.sourceMatchedRadialFreshPacketProfile_apply]
  unfold sourceMatchedRadialResetProfile sourceMatchedInnerResetStrategy
  simp only [Function.update_self]
  apply nestedRadialEverQuitMass_ge_weight_mul_gain_div
    reward (frontier.profiles (frontier.subseq rank)) mover.1
      (frontier.profiles (frontier.subseq rank) mover.1)
      (frontier.bestResponse mover (frontier.subseq rank))
      (weight mover) (frontier.lambda (frontier.subseq rank)) gainFloor M
      (hweight0 mover) (hweight1 mover)
      (frontier.lambda_pos (frontier.subseq rank)).le
      (frontier.lambda_le_one (frontier.subseq rank)) heffectiveHalf hM hreward
  rw [Function.update_eq_self]
  simpa only [frontier.actualGain_eq_endpointPayoffGain rank mover] using hgain

/-- Two distinct marginals with twice the requested ever-quit exposure have
one finite cutoff which exposes the joint clock and every player-deleted
clock.  The two movers cover one another when either mover's own coordinate
is deleted. -/
theorem exists_finiteCutoff_joint_and_deleted_exposure
    (profile : (quittingGame reward).BehaviorProfile)
    (first second : iota) (hne : first ≠ second)
    (exposure : Real) (hexposure : 0 < exposure)
    (hfirst : 2 * exposure <=
      quittingBehaviorEverQuitMass reward (profile first))
    (hsecond : 2 * exposure <=
      quittingBehaviorEverQuitMass reward (profile second)) :
    ∃ cutoff,
      exposure <= 1 - quittingJointSurvivalWeight
          (quittingProfileLiveRoot reward profile) 0 cutoff ∧
        forall who,
          exposure <= 1 - quittingOpponentSurvivalWeight
            (quittingProfileLiveRoot reward profile) who 0 cutoff := by
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
  refine ⟨cutoff, ?_, ?_⟩
  · have hjoint :=
      quittingJointSurvivalWeight_le_quittingOpponentSurvivalWeight
        roots second 0 cutoff
    have hopponent :=
      quittingOpponentSurvivalWeight_le_quittingHazardSurvival_ownHazard
        roots (who := second) (marked := first) hne cutoff
    dsimp only [firstHazard] at hfirstCutoff
    linarith
  · intro who
    by_cases hwho : who = first
    · subst who
      have hopponent :=
        quittingOpponentSurvivalWeight_le_quittingHazardSurvival_ownHazard
          roots (who := first) (marked := second) hne.symm cutoff
      dsimp only [secondHazard] at hsecondCutoff
      linarith
    · have hopponent :=
        quittingOpponentSurvivalWeight_le_quittingHazardSurvival_ownHazard
          roots (who := who) (marked := first) (Ne.symm hwho) cutoff
      dsimp only [firstHazard] at hfirstCutoff
      linarith

/-- A positive balanced circulation produces one bounded radial packet family
with a fixed positive exposure coefficient.  Eventually, at each selected
rank, a finite cutoff exposes both the joint clock and every deleted-player
clock by at least that coefficient times the genuine frontier reset scale. -/
theorem exists_boundedRadialFreshPacketExposure
    (frontier : QuittingCounterexampleStoppingLawFrontier witness)
    (hcirculation : HasQuittingStoppingLawFlatChargedCirculation
      frontier.active frontier.tangent) :
    ∃ weight : {who // who ∈ frontier.active} -> Real,
      ∃ hweight0 : forall mover, 0 <= weight mover,
      ∃ hweight1 : forall mover, weight mover <= 1,
      ∃ first second : {who // who ∈ frontier.active},
        first ≠ second ∧ 0 < weight first ∧ 0 < weight second ∧
          ∃ kappa : Real, 0 < kappa ∧
            ∀ᶠ rank in atTop, ∃ cutoff,
              kappa * frontier.lambda (frontier.subseq rank) <=
                  1 - quittingJointSurvivalWeight
                    (quittingProfileLiveRoot reward
                      (frontier.sourceMatchedRadialFreshPacketProfile rank
                        weight hweight0 hweight1)) 0 cutoff ∧
                forall who,
                  kappa * frontier.lambda (frontier.subseq rank) <=
                    1 - quittingOpponentSurvivalWeight
                      (quittingProfileLiveRoot reward
                        (frontier.sourceMatchedRadialFreshPacketProfile rank
                          weight hweight0 hweight1)) who 0 cutoff := by
  obtain ⟨weight, hweight0, hweight1, hbalance, hcharge⟩ :=
    frontier.exists_boundedRadialCirculationWeights hcirculation
  obtain ⟨first, second, hne, hfirstWeight, hsecondWeight⟩ :=
    frontier.exists_two_positive_boundedRadialCirculationWeights
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
    linarith [frontier.tangentOwnerCharge_pos first]
  have hsecondGain : 0 < secondGain := by
    dsimp only [secondGain]
    linarith [frontier.tangentOwnerCharge_pos second]
  have hkappa : 0 < kappa := by
    dsimp only [kappa]
    exact lt_min
      (div_pos (mul_pos hfirstWeight hfirstGain) (by positivity))
      (div_pos (mul_pos hsecondWeight hsecondGain) (by positivity))
  refine ⟨weight, hweight0, hweight1, first, second, hne,
    hfirstWeight, hsecondWeight, kappa, hkappa, ?_⟩
  have hlambdaEventually : ∀ᶠ rank in atTop,
      frontier.lambda (frontier.subseq rank) < 1 / 2 :=
    (tendsto_order.1 frontier.lambda_subseq_tendsto_zero).2 (1 / 2)
      (by norm_num)
  have hfirstGainEventually : ∀ᶠ rank in atTop,
      firstGain < frontier.actualGain rank first :=
    (tendsto_order.1 (frontier.actualGain_tendsto first)).1 firstGain
      (by
        dsimp only [firstGain]
        linarith [frontier.tangentOwnerCharge_pos first])
  have hsecondGainEventually : ∀ᶠ rank in atTop,
      secondGain < frontier.actualGain rank second :=
    (tendsto_order.1 (frontier.actualGain_tendsto second)).1 secondGain
      (by
        dsimp only [secondGain]
        linarith [frontier.tangentOwnerCharge_pos second])
  filter_upwards [hlambdaEventually, hfirstGainEventually,
    hsecondGainEventually] with rank hlambdaHalf hfirstActual hsecondActual
  let packet := frontier.sourceMatchedRadialFreshPacketProfile rank weight
    hweight0 hweight1
  have hlambda0 : 0 <= frontier.lambda (frontier.subseq rank) :=
    (frontier.lambda_pos (frontier.subseq rank)).le
  have hfirstEffective :
      weight first * frontier.lambda (frontier.subseq rank) <= 1 / 2 := by
    have hle := mul_le_mul_of_nonneg_right (hweight1 first) hlambda0
    linarith
  have hsecondEffective :
      weight second * frontier.lambda (frontier.subseq rank) <= 1 / 2 := by
    have hle := mul_le_mul_of_nonneg_right (hweight1 second) hlambda0
    linarith
  have hfirstMass := frontier.sourceMatchedRadialFreshPacket_everQuitMass_ge
    rank weight hweight0 hweight1 first firstGain M hM hrewardM
      hfirstActual.le hfirstEffective
  have hsecondMass := frontier.sourceMatchedRadialFreshPacket_everQuitMass_ge
    rank weight hweight0 hweight1 second secondGain M hM hrewardM
      hsecondActual.le hsecondEffective
  have hkappaFirst : kappa <= weight first * firstGain / (4 * M) :=
    min_le_left _ _
  have hkappaSecond : kappa <= weight second * secondGain / (4 * M) :=
    min_le_right _ _
  have hfirstScaled := mul_le_mul_of_nonneg_right hkappaFirst hlambda0
  have hsecondScaled := mul_le_mul_of_nonneg_right hkappaSecond hlambda0
  have hfirstExposure :
      2 * (kappa * frontier.lambda (frontier.subseq rank)) <=
        quittingBehaviorEverQuitMass reward (packet first.1) := by
    apply le_trans _ hfirstMass
    calc
      2 * (kappa * frontier.lambda (frontier.subseq rank)) <=
          2 * ((weight first * firstGain / (4 * M)) *
            frontier.lambda (frontier.subseq rank)) := by linarith
      _ = weight first * frontier.lambda (frontier.subseq rank) * firstGain /
          (2 * M) := by field_simp [ne_of_gt hM]; ring
  have hsecondExposure :
      2 * (kappa * frontier.lambda (frontier.subseq rank)) <=
        quittingBehaviorEverQuitMass reward (packet second.1) := by
    apply le_trans _ hsecondMass
    calc
      2 * (kappa * frontier.lambda (frontier.subseq rank)) <=
          2 * ((weight second * secondGain / (4 * M)) *
            frontier.lambda (frontier.subseq rank)) := by linarith
      _ = weight second * frontier.lambda (frontier.subseq rank) * secondGain /
          (2 * M) := by field_simp [ne_of_gt hM]; ring
  have hexposure :
      0 < kappa * frontier.lambda (frontier.subseq rank) :=
    mul_pos hkappa (frontier.lambda_pos (frontier.subseq rank))
  simpa only [packet] using
    exists_finiteCutoff_joint_and_deleted_exposure
      packet first.1 second.1 (Subtype.coe_ne_coe.mpr hne)
      (kappa * frontier.lambda (frontier.subseq rank)) hexposure
      hfirstExposure hsecondExposure

end QuittingCounterexampleStoppingLawFrontier

end GameTheory
