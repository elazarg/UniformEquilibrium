/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Research.Quitting.CertifiedForcedOwnerEndpointFlip

/-!
# A quantitative background host for the certified square

The owner/outsider square at a mixed root is an average of literal
pure-background four-cell coefficients.  This module performs that
decomposition only on dates carrying the certified packet.  A fixed
background label can therefore be selected without importing curvature from
unrelated rows.

The selected label may mention every ambient player as an action profile,
but its payoff geometry depends on them only through one quitting coalition
`T`.  Thus the local obstruction has owner, outsider, and one background-host
role.  The original stopping-time observer is the fourth game-facing role.
-/

noncomputable section

namespace GameTheory

open StochasticGame Math.Probability Math.PMFProduct

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- One pure-background contribution, restricted to a certified packet
date. -/
def quittingCertifiedPacketBackgroundCharge
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (terminal : {S : Finset ι // S.Nonempty})
    (owner who : ι) (action : Bool)
    (background : ι → Bool) (time : ℕ) : ℝ :=
  if 0 < quittingCertifiedForcedOwnerRectanglePacket
      reward profile terminal owner who action time then
    let root := quittingProfileLiveRoot reward profile time
    let tail := (quittingTerminalSemanticPair reward
      (quittingAllContinueProfileSpine reward profile (time + 1))).1
    quittingStageCoalitionMass reward profile time terminal *
      (root owner false).toReal *
        quittingPositiveOrientedBackgroundCharge
          reward tail root owner who action background
  else 0

theorem quittingCertifiedPacketBackgroundCharge_nonneg
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (terminal : {S : Finset ι // S.Nonempty})
    (owner who : ι) (action : Bool)
    (background : ι → Bool) (time : ℕ) :
    0 ≤ quittingCertifiedPacketBackgroundCharge
      reward profile terminal owner who action background time := by
  unfold quittingCertifiedPacketBackgroundCharge
  split_ifs
  · exact mul_nonneg
      (mul_nonneg
        (quittingStageCoalitionMass_nonneg reward profile time terminal)
        ENNReal.toReal_nonneg)
      (quittingPositiveOrientedBackgroundCharge_nonneg _ _ _ _ _ _ _)
  · exact le_rfl

/-- **Same-packet host decomposition.** -/
theorem certifiedPacket_le_sum_backgroundCharges
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (terminal : {S : Finset ι // S.Nonempty})
    (owner who : ι) (action : Bool) (time : ℕ)
    (howner : owner ∈ terminal.val) :
    quittingCertifiedForcedOwnerRectanglePacket
        reward profile terminal owner who action time ≤
      ∑ background,
        quittingCertifiedPacketBackgroundCharge reward profile terminal
          owner who action background time := by
  classical
  let packet := quittingCertifiedForcedOwnerRectanglePacket
    reward profile terminal owner who action time
  by_cases hpacket : 0 < packet
  · let root := quittingProfileLiveRoot reward profile time
    let tail := (quittingTerminalSemanticPair reward
      (quittingAllContinueProfileSpine reward profile (time + 1))).1
    let coefficient := quittingStageCoalitionMass reward profile time terminal *
      (root owner false).toReal
    let rectangle := quittingOwnerOutsiderDeviationRectangle
      reward tail root owner who action
    have hprops := positive_certifiedForcedOwnerRectanglePacket_properties
      reward profile terminal owner who action time
      (by simpa only [packet] using hpacket)
    have hne : owner ≠ who := Ne.symm hprops.1
    have hpacketRectangle :=
      certifiedForcedOwnerRectanglePacket_le_sameRectangle
        reward profile terminal owner who action time howner
    have hcoefficient0 : 0 ≤ coefficient := mul_nonneg
      (quittingStageCoalitionMass_nonneg reward profile time terminal)
      ENNReal.toReal_nonneg
    have hmax : max (coefficient * rectangle) 0 =
        coefficient * max rectangle 0 := by
      have h := mul_max_of_nonneg rectangle 0 hcoefficient0
      simpa using h.symm
    have hbackground :=
      max_rectangle_le_sum_positiveOrientedBackgroundCharge
        reward tail root owner who hne action
    have hscaled : coefficient * max rectangle 0 ≤
        coefficient * ∑ background,
          quittingPositiveOrientedBackgroundCharge
            reward tail root owner who action background :=
      mul_le_mul_of_nonneg_left hbackground hcoefficient0
    unfold quittingCertifiedPacketBackgroundCharge
    simp only [show 0 < quittingCertifiedForcedOwnerRectanglePacket
        reward profile terminal owner who action time by
          simpa only [packet] using hpacket, ↓reduceIte]
    calc
      packet ≤ max (coefficient * rectangle) 0 := by
        simpa only [packet, coefficient, rectangle, root, tail] using
          hpacketRectangle
      _ = coefficient * max rectangle 0 := hmax
      _ ≤ coefficient * ∑ background,
          quittingPositiveOrientedBackgroundCharge
            reward tail root owner who action background := hscaled
      _ = ∑ background,
          coefficient * quittingPositiveOrientedBackgroundCharge
            reward tail root owner who action background := by
        rw [Finset.mul_sum]
  · have hpacketNonneg : 0 ≤ packet := by
      dsimp only [packet]
      exact quittingCertifiedForcedOwnerRectanglePacket_nonneg
        reward profile terminal owner who action time
    have hpacket0 : packet = 0 :=
      le_antisymm (le_of_not_gt hpacket) hpacketNonneg
    change packet ≤ ∑ background,
      quittingCertifiedPacketBackgroundCharge reward profile terminal
        owner who action background time
    rw [hpacket0]
    exact Finset.sum_nonneg fun (background : ι → Bool) _ =>
      quittingCertifiedPacketBackgroundCharge_nonneg
        reward profile terminal owner who action background time

/-- Finite occupation of one fixed background label. -/
def quittingFiniteCertifiedPacketBackgroundCharge
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (terminal : {S : Finset ι // S.Nonempty})
    (owner who : ι) (action : Bool)
    (background : ι → Bool) (cutoff : ℕ) : ℝ :=
  ∑ time ∈ Finset.range cutoff,
    quittingCertifiedPacketBackgroundCharge reward profile terminal
      owner who action background time

/-- Finite packet mass is bounded by the sum of fixed background labels. -/
theorem finiteCertifiedPacket_le_sum_backgroundCharges
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (terminal : {S : Finset ι // S.Nonempty})
    (owner who : ι) (action : Bool) (cutoff : ℕ)
    (howner : owner ∈ terminal.val) :
    quittingFiniteCertifiedForcedOwnerRectanglePacket
        reward profile terminal owner who action cutoff ≤
      ∑ background,
        quittingFiniteCertifiedPacketBackgroundCharge reward profile terminal
          owner who action background cutoff := by
  have hsum := Finset.sum_le_sum fun time
      (_htime : time ∈ Finset.range cutoff) =>
    certifiedPacket_le_sum_backgroundCharges reward profile terminal
      owner who action time howner
  unfold quittingFiniteCertifiedForcedOwnerRectanglePacket
    quittingFiniteCertifiedPacketBackgroundCharge
  rw [Finset.sum_comm]
  exact hsum

/-- Freeze one background label with only the finite label-space loss. -/
theorem exists_fixed_background_of_positive_finiteCertifiedPacket
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (terminal : {S : Finset ι // S.Nonempty})
    (owner who : ι) (action : Bool) (cutoff : ℕ)
    (howner : owner ∈ terminal.val)
    (hpositive : 0 < quittingFiniteCertifiedForcedOwnerRectanglePacket
      reward profile terminal owner who action cutoff) :
    ∃ background : ι → Bool,
      0 < quittingFiniteCertifiedPacketBackgroundCharge reward profile terminal
          owner who action background cutoff ∧
        quittingFiniteCertifiedForcedOwnerRectanglePacket
          reward profile terminal owner who action cutoff ≤
        (Fintype.card (ι → Bool) : ℝ) *
          quittingFiniteCertifiedPacketBackgroundCharge reward profile terminal
            owner who action background cutoff := by
  let occupation : (ι → Bool) → ℝ := fun background =>
    quittingFiniteCertifiedPacketBackgroundCharge reward profile terminal
      owner who action background cutoff
  obtain ⟨background, _hbackground, hmax⟩ := Finset.exists_max_image
    (Finset.univ : Finset (ι → Bool)) occupation Finset.univ_nonempty
  have hsumLe : (∑ candidate, occupation candidate) ≤
      (Fintype.card (ι → Bool) : ℝ) * occupation background := by
    have h := (Finset.univ : Finset (ι → Bool)).sum_le_card_nsmul occupation
      (occupation background)
      (fun candidate hcandidate => hmax candidate hcandidate)
    simpa [nsmul_eq_mul] using h
  have hbound := (finiteCertifiedPacket_le_sum_backgroundCharges
    reward profile terminal owner who action cutoff howner).trans hsumLe
  have hcard0 : 0 ≤ (Fintype.card (ι → Bool) : ℝ) := by positivity
  have hoccupationPos : 0 < occupation background := by
    by_contra hnot
    have hoccupation0 : occupation background ≤ 0 := le_of_not_gt hnot
    have hproduct0 : (Fintype.card (ι → Bool) : ℝ) *
        occupation background ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hcard0 hoccupation0
    linarith
  refine ⟨background, by simpa only [occupation] using hoccupationPos, ?_⟩
  simpa only [occupation] using hbound

/-- Positive occupation of a fixed background label produces a literal row
where the same certified packet and the same oriented host square are both
positive. -/
theorem exists_literal_certifiedBackgroundHost_of_positive_occupation
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (terminal : {S : Finset ι // S.Nonempty})
    (owner who : ι) (action : Bool)
    (background : ι → Bool) (cutoff : ℕ)
    (hpositive : 0 < quittingFiniteCertifiedPacketBackgroundCharge
      reward profile terminal owner who action background cutoff) :
    ∃ time ∈ Finset.range cutoff,
      let root := quittingProfileLiveRoot reward profile time
      let tail := (quittingTerminalSemanticPair reward
        (quittingAllContinueProfileSpine reward profile (time + 1))).1
      let T := quittingPureBackgroundCoalition background owner who
      0 < quittingCertifiedForcedOwnerRectanglePacket
          reward profile terminal owner who action time ∧
        0 < ((pmfPi root) background).toReal ∧
        0 < quittingOrientedPureBackgroundSquare
          reward tail background owner who action ∧
        owner ∉ T ∧ who ∉ T := by
  classical
  unfold quittingFiniteCertifiedPacketBackgroundCharge at hpositive
  have hrow : ∃ time ∈ Finset.range cutoff,
      0 < quittingCertifiedPacketBackgroundCharge reward profile terminal
        owner who action background time := by
    by_contra hnone
    have hsumNonpos : (∑ time ∈ Finset.range cutoff,
        quittingCertifiedPacketBackgroundCharge reward profile terminal
          owner who action background time) ≤ 0 := by
      apply Finset.sum_nonpos
      intro time htime
      apply le_of_not_gt
      intro htimePos
      exact hnone ⟨time, htime, htimePos⟩
    linarith
  obtain ⟨time, htime, hrowPos⟩ := hrow
  refine ⟨time, htime, ?_⟩
  let root := quittingProfileLiveRoot reward profile time
  let tail := (quittingTerminalSemanticPair reward
    (quittingAllContinueProfileSpine reward profile (time + 1))).1
  let packet := quittingCertifiedForcedOwnerRectanglePacket
    reward profile terminal owner who action time
  have hpacketPos : 0 < packet := by
    by_contra hnot
    have hnotPos : ¬ 0 < quittingCertifiedForcedOwnerRectanglePacket
        reward profile terminal owner who action time := by
      simpa only [packet] using hnot
    unfold quittingCertifiedPacketBackgroundCharge at hrowPos
    rw [if_neg hnotPos] at hrowPos
    linarith
  unfold quittingCertifiedPacketBackgroundCharge at hrowPos
  rw [if_pos (by simpa only [packet] using hpacketPos)] at hrowPos
  change 0 < quittingStageCoalitionMass reward profile time terminal *
      (root owner false).toReal *
        quittingPositiveOrientedBackgroundCharge
          reward tail root owner who action background at hrowPos
  have hbackgroundChargePos : 0 < quittingPositiveOrientedBackgroundCharge
      reward tail root owner who action background := by
    by_contra hnot
    have hnonpos := le_of_not_gt hnot
    have hcoefficient0 : 0 ≤ quittingStageCoalitionMass reward profile time
        terminal * (root owner false).toReal :=
      mul_nonneg
        (quittingStageCoalitionMass_nonneg reward profile time terminal)
        ENNReal.toReal_nonneg
    have := mul_nonpos_of_nonneg_of_nonpos hcoefficient0 hnonpos
    linarith
  unfold quittingPositiveOrientedBackgroundCharge at hbackgroundChargePos
  have hprobPos : 0 < ((pmfPi root) background).toReal := by
    by_contra hnot
    have hprob0 : ((pmfPi root) background).toReal = 0 :=
      le_antisymm (le_of_not_gt hnot) ENNReal.toReal_nonneg
    rw [hprob0, mul_zero, zero_mul] at hbackgroundChargePos
    linarith
  have hsquarePos : 0 < quittingOrientedPureBackgroundSquare
      reward tail background owner who action := by
    by_contra hnot
    have hsquareNonpos : quittingOrientedPureBackgroundSquare
        reward tail background owner who action ≤ 0 := le_of_not_gt hnot
    rw [max_eq_right hsquareNonpos] at hbackgroundChargePos
    ring_nf at hbackgroundChargePos
    linarith
  exact ⟨by simpa only [packet] using hpacketPos, hprobPos, hsquarePos,
    quittingPureBackgroundCoalition_not_mem_owner background owner who,
    quittingPureBackgroundCoalition_not_mem_who background owner who⟩

/-- A player who is pure Continue at the mixed root cannot belong to a
positive-probability pure background, provided it is distinct from the two
displayed square coordinates. -/
theorem pureContinue_not_mem_positiveProbability_backgroundCoalition
    (root : ι → PMF Bool) (background : ι → Bool)
    (owner who observer : ι)
    (hobserverOwner : observer ≠ owner)
    (hobserverWho : observer ≠ who)
    (hpure : root observer = PMF.pure false)
    (hpositive : 0 < ((pmfPi root) background).toReal) :
    observer ∉ quittingPureBackgroundCoalition background owner who := by
  intro hmem
  have haction : background observer = true := by
    simpa [quittingPureBackgroundCoalition, quittingQuitters,
      hobserverOwner, hobserverWho] using hmem
  have hfactor : root observer (background observer) = 0 := by
    rw [haction, hpure]
    simp
  have hproduct : (∏ player, root player (background player)) = 0 :=
    Finset.prod_eq_zero (Finset.mem_univ observer) hfactor
  have hzero : ((pmfPi root) background).toReal = 0 := by
    rw [pmfPi_apply, hproduct]
    simp
  rw [hzero] at hpositive
  exact (lt_irrefl 0) hpositive

/-- Pure-background charge on the same dates as the certified endpoint-flip
loss.  Its coefficient is the loss coefficient rather than the terminal
cylinder coefficient. -/
def quittingCertifiedFlipBackgroundCharge
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (terminal : {S : Finset ι // S.Nonempty})
    (owner who : ι) (action : Bool)
    (background : ι → Bool) (time : ℕ) : ℝ :=
  if 0 < quittingCertifiedForcedOwnerRectanglePacket
      reward profile terminal owner who action time then
    let root := quittingProfileLiveRoot reward profile time
    let tail := (quittingTerminalSemanticPair reward
      (quittingAllContinueProfileSpine reward profile (time + 1))).1
    quittingLiveMass reward profile time * (root owner false).toReal *
      quittingPositiveOrientedBackgroundCharge
        reward tail root owner who action background
  else 0

theorem quittingCertifiedFlipBackgroundCharge_nonneg
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (terminal : {S : Finset ι // S.Nonempty})
    (owner who : ι) (action : Bool)
    (background : ι → Bool) (time : ℕ) :
    0 ≤ quittingCertifiedFlipBackgroundCharge reward profile terminal
      owner who action background time := by
  unfold quittingCertifiedFlipBackgroundCharge
  split_ifs
  · exact mul_nonneg
      (mul_nonneg
        (quittingLiveMass_nonneg reward profile time)
        ENNReal.toReal_nonneg)
      (quittingPositiveOrientedBackgroundCharge_nonneg _ _ _ _ _ _ _)
  · exact le_rfl

/-- **Same-support flip-to-host decomposition.**  On a certified date the
tested action is best on the owner-Quit face, so its negative owner-Continue
gain is bounded by the rectangle.  The oriented-background expansion then
decomposes the endpoint-flip loss without leaving its packet support. -/
theorem certifiedContinueFaceLoss_le_sum_flipBackgroundCharges
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (terminal : {S : Finset ι // S.Nonempty})
    (owner who : ι) (action : Bool) (time : ℕ) :
    quittingCertifiedPacketContinueFaceLoss reward profile terminal
        owner who action time ≤
      ∑ background,
        quittingCertifiedFlipBackgroundCharge reward profile terminal
          owner who action background time := by
  classical
  let packet := quittingCertifiedForcedOwnerRectanglePacket
    reward profile terminal owner who action time
  by_cases hpacket : 0 < packet
  · let root := quittingProfileLiveRoot reward profile time
    let tail := (quittingTerminalSemanticPair reward
      (quittingAllContinueProfileSpine reward profile (time + 1))).1
    let forcedQuit := Function.update root owner (PMF.pure true)
    let forcedContinue := Function.update root owner (PMF.pure false)
    let quitGain := quittingRootDeviationGain reward tail forcedQuit who
      (PMF.pure action)
    let continueGain := quittingRootDeviationGain reward tail forcedContinue who
      (PMF.pure action)
    let rectangle := quittingOwnerOutsiderDeviationRectangle
      reward tail root owner who action
    let coefficient := quittingLiveMass reward profile time *
      (root owner false).toReal
    have hprops := positive_certifiedForcedOwnerRectanglePacket_properties
      reward profile terminal owner who action time
      (by simpa only [packet] using hpacket)
    have hne : owner ≠ who := Ne.symm hprops.1
    have haction := hprops.2.1
    have hquitGain : quitGain =
        quittingRootCoordinateNashDefect reward tail forcedQuit who := by
      dsimp only [quitGain]
      rw [← haction]
      exact quittingRootDeviationGain_bestEndpoint_eq_coordinateNashDefect
        reward tail forcedQuit who
    have hquitGain0 : 0 ≤ quitGain := by
      rw [hquitGain]
      exact quittingRootCoordinateNashDefect_nonneg reward tail forcedQuit who
    have hrectangle : rectangle = quitGain - continueGain := rfl
    have hminus : -continueGain ≤ rectangle := by
      rw [hrectangle]
      linarith
    have hmax : max (-continueGain) 0 ≤ max rectangle 0 :=
      max_le (hminus.trans (le_max_left _ _)) (le_max_right _ _)
    have hbackground :=
      max_rectangle_le_sum_positiveOrientedBackgroundCharge
        reward tail root owner who hne action
    have hcoefficient0 : 0 ≤ coefficient := mul_nonneg
      (quittingLiveMass_nonneg reward profile time) ENNReal.toReal_nonneg
    have hscaled : coefficient * max (-continueGain) 0 ≤
        coefficient * ∑ background,
          quittingPositiveOrientedBackgroundCharge
            reward tail root owner who action background :=
      mul_le_mul_of_nonneg_left (hmax.trans hbackground) hcoefficient0
    unfold quittingCertifiedPacketContinueFaceLoss
      quittingCertifiedFlipBackgroundCharge
    simp only [show 0 < quittingCertifiedForcedOwnerRectanglePacket
        reward profile terminal owner who action time by
          simpa only [packet] using hpacket, ↓reduceIte]
    change coefficient * max (-continueGain) 0 ≤
      ∑ background,
        coefficient * quittingPositiveOrientedBackgroundCharge
          reward tail root owner who action background
    calc
      coefficient * max (-continueGain) 0 ≤
          coefficient * ∑ background,
            quittingPositiveOrientedBackgroundCharge
              reward tail root owner who action background := hscaled
      _ = ∑ background,
          coefficient * quittingPositiveOrientedBackgroundCharge
            reward tail root owner who action background := by
        rw [Finset.mul_sum]
  · unfold quittingCertifiedPacketContinueFaceLoss
      quittingCertifiedFlipBackgroundCharge
    simp only [show ¬ 0 < quittingCertifiedForcedOwnerRectanglePacket
        reward profile terminal owner who action time by
          simpa only [packet] using hpacket, ↓reduceIte]
    exact Finset.sum_nonneg fun background _ => le_rfl

/-- Finite same-support host occupation for a fixed background label. -/
def quittingFiniteCertifiedFlipBackgroundCharge
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (terminal : {S : Finset ι // S.Nonempty})
    (owner who : ι) (action : Bool)
    (background : ι → Bool) (cutoff : ℕ) : ℝ :=
  ∑ time ∈ Finset.range cutoff,
    quittingCertifiedFlipBackgroundCharge reward profile terminal
      owner who action background time

/-- Finite endpoint-flip loss is covered by fixed background labels. -/
theorem finiteCertifiedContinueFaceLoss_le_sum_flipBackgroundCharges
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (terminal : {S : Finset ι // S.Nonempty})
    (owner who : ι) (action : Bool) (cutoff : ℕ) :
    quittingFiniteCertifiedPacketContinueFaceLoss reward profile terminal
        owner who action cutoff ≤
      ∑ background,
        quittingFiniteCertifiedFlipBackgroundCharge reward profile terminal
          owner who action background cutoff := by
  have hsum := Finset.sum_le_sum fun time
      (_htime : time ∈ Finset.range cutoff) =>
    certifiedContinueFaceLoss_le_sum_flipBackgroundCharges
      reward profile terminal owner who action time
  unfold quittingFiniteCertifiedPacketContinueFaceLoss
    quittingFiniteCertifiedFlipBackgroundCharge
  rw [Finset.sum_comm]
  exact hsum

/-- A positive flip loss selects one fixed background host with quantitative
occupation. -/
theorem exists_fixed_flipBackground_of_positive_supportedLoss
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (terminal : {S : Finset ι // S.Nonempty})
    (owner who : ι) (action : Bool) (cutoff : ℕ)
    (hpositive : 0 < quittingFiniteCertifiedPacketContinueFaceLoss
      reward profile terminal owner who action cutoff) :
    ∃ background : ι → Bool,
      0 < quittingFiniteCertifiedFlipBackgroundCharge reward profile terminal
          owner who action background cutoff ∧
        quittingFiniteCertifiedPacketContinueFaceLoss reward profile terminal
            owner who action cutoff ≤
          (Fintype.card (ι → Bool) : ℝ) *
            quittingFiniteCertifiedFlipBackgroundCharge reward profile terminal
              owner who action background cutoff := by
  let occupation : (ι → Bool) → ℝ := fun background =>
    quittingFiniteCertifiedFlipBackgroundCharge reward profile terminal
      owner who action background cutoff
  obtain ⟨background, _hbackground, hmax⟩ := Finset.exists_max_image
    (Finset.univ : Finset (ι → Bool)) occupation Finset.univ_nonempty
  have hsumLe : (∑ candidate, occupation candidate) ≤
      (Fintype.card (ι → Bool) : ℝ) * occupation background := by
    have h := (Finset.univ : Finset (ι → Bool)).sum_le_card_nsmul occupation
      (occupation background)
      (fun candidate hcandidate => hmax candidate hcandidate)
    simpa [nsmul_eq_mul] using h
  have hbound :=
    (finiteCertifiedContinueFaceLoss_le_sum_flipBackgroundCharges
      reward profile terminal owner who action cutoff).trans hsumLe
  have hcard0 : 0 ≤ (Fintype.card (ι → Bool) : ℝ) := by positivity
  have hoccupationPos : 0 < occupation background := by
    by_contra hnot
    have hoccupation0 : occupation background ≤ 0 := le_of_not_gt hnot
    have hproduct0 : (Fintype.card (ι → Bool) : ℝ) *
        occupation background ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hcard0 hoccupation0
    linarith
  exact ⟨background, by simpa only [occupation] using hoccupationPos,
    by simpa only [occupation] using hbound⟩

end GameTheory
