/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Research.Quitting.CertifiedForcedOwnerRectanglePacket
import Research.Quitting.OwnerOutsiderSquareContextDecomposition
import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegimeObserverAbsentRectangleBaselineDispatch

/-!
# The certified rectangle residual is an endpoint flip

For a certified square, the outsider action is best when the owner is forced
to Quit.  If the affine rectangle is not paid at the actual source row, the
remaining negative Continue-face term means exactly that the outsider's best
endpoint flips when the owner is forced to Continue.

The supported occupations below keep this conclusion on the same dates as
the certified packet.  Hence neither source gain nor Continue-face loss may
be collected from unrelated positive-curvature rows.
-/

noncomputable section

namespace GameTheory

open StochasticGame Math.Probability Math.PMFProduct

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- A strictly bad pure action is opposite to the deterministic best
endpoint. -/
theorem quittingRootBestEndpointAction_eq_not_of_pureGain_neg
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : Payoff ι) (root : ι → PMF Bool) (who : ι) (action : Bool)
    (hneg : quittingRootDeviationGain reward tail root who
      (PMF.pure action) < 0) :
    quittingRootBestEndpointAction reward tail root who = !action := by
  cases action with
  | false =>
      rw [quittingRootDeviationGain_pure_false_eq] at hneg
      have hp0 : 0 ≤ (root who true).toReal := ENNReal.toReal_nonneg
      have hdiff : 0 < quittingRootEndpointDifference reward tail root who := by
        nlinarith
      unfold quittingRootEndpointDifference at hdiff
      have hnot : ¬ quittingRootQuitPayoff reward tail root who ≤
          quittingRootContinuePayoff reward tail root who := by linarith
      unfold quittingRootBestEndpointAction
      simp only [Bool.not_false]
      rw [if_neg hnot]
  | true =>
      rw [quittingRootDeviationGain_pure_true_eq] at hneg
      have hp0 : 0 ≤ (root who false).toReal := ENNReal.toReal_nonneg
      have hdiff : quittingRootEndpointDifference reward tail root who < 0 := by
        nlinarith
      unfold quittingRootEndpointDifference at hdiff
      have hle : quittingRootQuitPayoff reward tail root who ≤
          quittingRootContinuePayoff reward tail root who := by linarith
      unfold quittingRootBestEndpointAction
      simp only [Bool.not_true]
      rw [if_pos hle]

/-- **Local endpoint-flip passport.**  The certified action is strictly best
on the owner-Quit face; if it is strictly bad on the owner-Continue face,
the deterministic best endpoint there is the opposite Boolean action and
the same-action rectangle is strictly positive. -/
theorem forcedOwner_bestEndpoint_flip_of_continueFaceLoss
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : Payoff ι) (root : ι → PMF Bool)
    (owner who : ι)
    (hforcedPos : 0 < quittingRootCoordinateNashDefect reward tail
      (Function.update root owner (PMF.pure true)) who)
    (hloss : quittingRootDeviationGain reward tail
      (Function.update root owner (PMF.pure false)) who
        (PMF.pure (quittingForcedOwnerBestEndpointAction
          reward tail root owner who)) < 0) :
    let action := quittingForcedOwnerBestEndpointAction
      reward tail root owner who
    quittingRootDeviationGain reward tail
        (Function.update root owner (PMF.pure true)) who
          (PMF.pure action) > 0 ∧
      quittingRootBestEndpointAction reward tail
          (Function.update root owner (PMF.pure false)) who = !action ∧
      0 < quittingOwnerOutsiderDeviationRectangle
        reward tail root owner who action := by
  dsimp only
  let forcedQuit := Function.update root owner (PMF.pure true)
  let forcedContinue := Function.update root owner (PMF.pure false)
  let action := quittingForcedOwnerBestEndpointAction
    reward tail root owner who
  have hgain : quittingRootDeviationGain reward tail forcedQuit who
        (PMF.pure action) =
      quittingRootCoordinateNashDefect reward tail forcedQuit who :=
    quittingRootDeviationGain_bestEndpoint_eq_coordinateNashDefect
      reward tail forcedQuit who
  have hgainPos : 0 < quittingRootDeviationGain reward tail forcedQuit who
      (PMF.pure action) := by
    rw [hgain]
    exact hforcedPos
  have hflip := quittingRootBestEndpointAction_eq_not_of_pureGain_neg
    reward tail forcedContinue who action hloss
  have hrectangle : 0 < quittingOwnerOutsiderDeviationRectangle
      reward tail root owner who action := by
    unfold quittingOwnerOutsiderDeviationRectangle
    dsimp only [forcedQuit, forcedContinue] at hgainPos hflip ⊢
    linarith
  exact ⟨hgainPos, hflip, hrectangle⟩

/-- Source-row positive gain, restricted to dates carrying the certified
packet. -/
def quittingCertifiedPacketSourceGain
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (terminal : {S : Finset ι // S.Nonempty})
    (owner who : ι) (action : Bool) (time : ℕ) : ℝ :=
  if 0 < quittingCertifiedForcedOwnerRectanglePacket
      reward profile terminal owner who action time then
    let root := quittingProfileLiveRoot reward profile time
    let tail := (quittingTerminalSemanticPair reward
      (quittingAllContinueProfileSpine reward profile (time + 1))).1
    quittingLiveMass reward profile time *
      max (quittingRootDeviationGain reward tail root who
        (PMF.pure action)) 0
  else 0

/-- Owner-Continue-face loss, restricted to dates carrying the same
certified packet. -/
def quittingCertifiedPacketContinueFaceLoss
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (terminal : {S : Finset ι // S.Nonempty})
    (owner who : ι) (action : Bool) (time : ℕ) : ℝ :=
  if 0 < quittingCertifiedForcedOwnerRectanglePacket
      reward profile terminal owner who action time then
    let root := quittingProfileLiveRoot reward profile time
    let tail := (quittingTerminalSemanticPair reward
      (quittingAllContinueProfileSpine reward profile (time + 1))).1
    quittingLiveMass reward profile time * (root owner false).toReal *
      max (-quittingRootDeviationGain reward tail
        (Function.update root owner (PMF.pure false)) who
          (PMF.pure action)) 0
  else 0

/-- Same-support affine split of one certified packet. -/
theorem certifiedPacket_le_supportedSourceGain_add_continueFaceLoss
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (terminal : {S : Finset ι // S.Nonempty})
    (owner who : ι) (action : Bool) (time : ℕ)
    (hne : owner ≠ who) (howner : owner ∈ terminal.val) :
    quittingCertifiedForcedOwnerRectanglePacket
        reward profile terminal owner who action time ≤
      quittingCertifiedPacketSourceGain reward profile terminal
          owner who action time +
        quittingCertifiedPacketContinueFaceLoss reward profile terminal
          owner who action time := by
  by_cases hpacket : 0 < quittingCertifiedForcedOwnerRectanglePacket
      reward profile terminal owner who action time
  · let root := quittingProfileLiveRoot reward profile time
    let tail := (quittingTerminalSemanticPair reward
      (quittingAllContinueProfileSpine reward profile (time + 1))).1
    let mass := quittingStageCoalitionMass reward profile time terminal
    let coefficient := mass * (root owner false).toReal
    let rectangle := quittingOwnerOutsiderDeviationRectangle
      reward tail root owner who action
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
    rw [hmax] at hpacketRectangle
    have hrow := stageRectangleCharge_le_sourceGain_add_continueFaceLoss
      reward profile terminal owner who hne howner action time
    unfold quittingCertifiedPacketSourceGain
      quittingCertifiedPacketContinueFaceLoss
    rw [if_pos hpacket, if_pos hpacket]
    exact hpacketRectangle.trans (by
      simpa only [root, tail, mass, coefficient] using hrow)
  · have hzero : quittingCertifiedForcedOwnerRectanglePacket
        reward profile terminal owner who action time = 0 :=
      le_antisymm (le_of_not_gt hpacket)
        (quittingCertifiedForcedOwnerRectanglePacket_nonneg
          reward profile terminal owner who action time)
    rw [hzero]
    exact add_nonneg (by
      unfold quittingCertifiedPacketSourceGain
      rw [if_neg hpacket]) (by
      unfold quittingCertifiedPacketContinueFaceLoss
      rw [if_neg hpacket])

/-- Same-support source occupation on a finite clock. -/
def quittingFiniteCertifiedPacketSourceGain
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (terminal : {S : Finset ι // S.Nonempty})
    (owner who : ι) (action : Bool) (cutoff : ℕ) : ℝ :=
  ∑ time ∈ Finset.range cutoff,
    quittingCertifiedPacketSourceGain
      reward profile terminal owner who action time

/-- Same-support endpoint-flip loss occupation on a finite clock. -/
def quittingFiniteCertifiedPacketContinueFaceLoss
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (terminal : {S : Finset ι // S.Nonempty})
    (owner who : ι) (action : Bool) (cutoff : ℕ) : ℝ :=
  ∑ time ∈ Finset.range cutoff,
    quittingCertifiedPacketContinueFaceLoss
      reward profile terminal owner who action time

/-- Finite same-support affine split. -/
theorem finiteCertifiedPacket_le_supportedSourceGain_add_continueFaceLoss
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (terminal : {S : Finset ι // S.Nonempty})
    (owner who : ι) (action : Bool) (cutoff : ℕ)
    (hne : owner ≠ who) (howner : owner ∈ terminal.val) :
    quittingFiniteCertifiedForcedOwnerRectanglePacket
        reward profile terminal owner who action cutoff ≤
      quittingFiniteCertifiedPacketSourceGain
          reward profile terminal owner who action cutoff +
        quittingFiniteCertifiedPacketContinueFaceLoss
          reward profile terminal owner who action cutoff := by
  have hsum := Finset.sum_le_sum fun time
      (_htime : time ∈ Finset.range cutoff) =>
    certifiedPacket_le_supportedSourceGain_add_continueFaceLoss
      reward profile terminal owner who action time hne howner
  unfold quittingFiniteCertifiedForcedOwnerRectanglePacket
    quittingFiniteCertifiedPacketSourceGain
    quittingFiniteCertifiedPacketContinueFaceLoss
  simpa only [Finset.sum_add_distrib] using hsum

/-- Restricting to certified dates can only decrease the source gain
occupation. -/
theorem finiteCertifiedPacketSourceGain_le_unrestricted
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (terminal : {S : Finset ι // S.Nonempty})
    (owner who : ι) (action : Bool) (cutoff : ℕ) :
    quittingFiniteCertifiedPacketSourceGain
        reward profile terminal owner who action cutoff ≤
      quittingFinitePureActionSourceGainOccupation
        reward profile who action cutoff := by
  unfold quittingFiniteCertifiedPacketSourceGain
    quittingFinitePureActionSourceGainOccupation
  apply Finset.sum_le_sum
  intro time _
  by_cases hpacket : 0 < quittingCertifiedForcedOwnerRectanglePacket
      reward profile terminal owner who action time
  · unfold quittingCertifiedPacketSourceGain
    rw [if_pos hpacket]
  · unfold quittingCertifiedPacketSourceGain
    rw [if_neg hpacket]
    exact mul_nonneg (quittingLiveMass_nonneg reward profile time)
      (le_max_right _ 0)

/-- A fixed certified packet is either consumed by the matching source
action, or leaves a same-support endpoint-flip loss. -/
theorem exists_sourceConsumer_or_certifiedEndpointFlipLoss
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (terminal : {S : Finset ι // S.Nonempty})
    (owner who : ι) (action : Bool) (cutoff : ℕ)
    (hne : owner ≠ who) (howner : owner ∈ terminal.val)
    (lower : ℝ)
    (hpacket : lower ≤
      quittingFiniteCertifiedForcedOwnerRectanglePacket
        reward profile terminal owner who action cutoff) :
    (action = false ∧
      ∃ deviation : (quittingGame reward).BehaviorStrategy who,
        lower / 2 ≤ quittingTerminalPayoff reward
            (Function.update profile who deviation) who -
          quittingTerminalPayoff reward profile who) ∨
    (action = true ∧ ∃ coalition ∈ (Finset.univ.erase who).powerset,
      lower / 2 ≤ (((Finset.univ.erase who).powerset.card : ℝ) *
        quittingFiniteQuitDefectAtomOccupationAt reward
          (fun time => (quittingTerminalSemanticPair reward
            (quittingAllContinueProfileSpine reward profile
              (time + 1))).1)
          (quittingProfileLiveRoot reward profile)
          (quittingLiveMass reward profile) cutoff who coalition)) ∨
    lower / 2 ≤ quittingFiniteCertifiedPacketContinueFaceLoss
      reward profile terminal owner who action cutoff := by
  have hsplit :=
    finiteCertifiedPacket_le_supportedSourceGain_add_continueFaceLoss
      reward profile terminal owner who action cutoff hne howner
  let source := quittingFiniteCertifiedPacketSourceGain
    reward profile terminal owner who action cutoff
  let loss := quittingFiniteCertifiedPacketContinueFaceLoss
    reward profile terminal owner who action cutoff
  have hlower : lower ≤ source + loss :=
    hpacket.trans (by simpa only [source, loss] using hsplit)
  by_cases hloss : lower / 2 ≤ loss
  · exact Or.inr (Or.inr hloss)
  · have hsource : lower / 2 ≤ source := by linarith
    have hsourceFull : lower / 2 ≤
        quittingFinitePureActionSourceGainOccupation
          reward profile who action cutoff :=
      hsource.trans (finiteCertifiedPacketSourceGain_le_unrestricted
        reward profile terminal owner who action cutoff)
    cases action with
    | false =>
        left
        obtain ⟨deviation, hgain⟩ :=
          exists_behaviorDeviation_gain_ge_pureFalseSourceOccupation
            reward profile who cutoff
        exact ⟨rfl, deviation, hsourceFull.trans hgain⟩
    | true =>
        right; left
        obtain ⟨coalition, hcoalition, hatom⟩ :=
          exists_fixedCoalition_of_pureTrueSourceOccupation
            reward profile who cutoff
        exact ⟨rfl, coalition, hcoalition, hsourceFull.trans hatom⟩

/-- Positive supported loss produces one literal row with the complete
endpoint-flip passport. -/
theorem exists_literal_endpointFlip_of_positive_supportedLoss
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (terminal : {S : Finset ι // S.Nonempty})
    (owner who : ι) (action : Bool) (cutoff : ℕ)
    (hpositive : 0 < quittingFiniteCertifiedPacketContinueFaceLoss
      reward profile terminal owner who action cutoff) :
    ∃ time ∈ Finset.range cutoff,
      let root := quittingProfileLiveRoot reward profile time
      let tail := (quittingTerminalSemanticPair reward
        (quittingAllContinueProfileSpine reward profile (time + 1))).1
      0 < quittingCertifiedForcedOwnerRectanglePacket
          reward profile terminal owner who action time ∧
        quittingForcedOwnerBestEndpointAction reward tail root owner who =
          action ∧
        0 < quittingRootCoordinateNashDefect reward tail
          (Function.update root owner (PMF.pure true)) who ∧
        quittingRootDeviationGain reward tail
          (Function.update root owner (PMF.pure false)) who
            (PMF.pure action) < 0 ∧
        quittingRootBestEndpointAction reward tail
          (Function.update root owner (PMF.pure false)) who = !action ∧
        0 < quittingOwnerOutsiderDeviationRectangle
          reward tail root owner who action := by
  classical
  unfold quittingFiniteCertifiedPacketContinueFaceLoss at hpositive
  have hrow : ∃ time ∈ Finset.range cutoff,
      0 < quittingCertifiedPacketContinueFaceLoss
        reward profile terminal owner who action time := by
    by_contra hnone
    have hnonpos : (∑ time ∈ Finset.range cutoff,
        quittingCertifiedPacketContinueFaceLoss
          reward profile terminal owner who action time) ≤ 0 := by
      apply Finset.sum_nonpos
      intro time htime
      apply le_of_not_gt
      intro htimePos
      exact hnone ⟨time, htime, htimePos⟩
    linarith
  obtain ⟨time, htime, hlossPos⟩ := hrow
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
    unfold quittingCertifiedPacketContinueFaceLoss at hlossPos
    rw [if_neg hnotPos] at hlossPos
    linarith
  have hprops := positive_certifiedForcedOwnerRectanglePacket_properties
    reward profile terminal owner who action time
      (by simpa only [packet] using hpacketPos)
  have hfaceNeg : quittingRootDeviationGain reward tail
      (Function.update root owner (PMF.pure false)) who
        (PMF.pure action) < 0 := by
    unfold quittingCertifiedPacketContinueFaceLoss at hlossPos
    rw [if_pos (by simpa only [packet] using hpacketPos)] at hlossPos
    by_contra hnot
    have hgain0 : 0 ≤ quittingRootDeviationGain reward tail
        (Function.update root owner (PMF.pure false)) who
          (PMF.pure action) := le_of_not_gt hnot
    have hmaxzero : max (-quittingRootDeviationGain reward tail
        (Function.update root owner (PMF.pure false)) who
          (PMF.pure action)) 0 = 0 := max_eq_right (neg_nonpos.mpr hgain0)
    change 0 < quittingLiveMass reward profile time *
      (root owner false).toReal *
        max (-quittingRootDeviationGain reward tail
          (Function.update root owner (PMF.pure false)) who
            (PMF.pure action)) 0 at hlossPos
    rw [hmaxzero, mul_zero] at hlossPos
    linarith
  have hforcedPos : 0 < quittingRootCoordinateNashDefect reward tail
      (Function.update root owner (PMF.pure true)) who :=
    lt_of_lt_of_le hprops.2.2.1 hprops.2.2.2.1
  have haction : quittingForcedOwnerBestEndpointAction
      reward tail root owner who = action := by
    simpa only [root, tail] using hprops.2.1
  have hflip := forcedOwner_bestEndpoint_flip_of_continueFaceLoss
    reward tail root owner who hforcedPos (by
      rw [haction]
      exact hfaceNeg)
  rw [haction] at hflip
  refine ⟨by simpa only [packet] using hpacketPos, haction,
    hforcedPos, hfaceNeg, ?_, ?_⟩
  · simpa only [root, tail] using hflip.2.1
  · simpa only [root, tail] using hflip.2.2

namespace QuittingStoppingLawVanishingDebtRectangleSequence

/-- **Game-facing finite-clock endpoint-flip frontier.**  The observer-absent
finite clock is consumed by a legal deviation or fixed Quit atom, except for
one fixed certified owner/outsider/action loss.  Every positive instance of
that last loss is a literal copy/negate endpoint flip by
`exists_literal_endpointFlip_of_positive_supportedLoss`. -/
theorem observerAbsent_finiteClock_certifiedEndpointFlip
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {regime : QuittingCounterexampleRegime reward}
    {frontier : QuittingCounterexampleStoppingLawFrontier regime}
    (packet : QuittingStoppingLawVanishingDebtRectangleSequence frontier)
    (habsent : packet.observer ∉ packet.terminal.val)
    (n stop : ℕ) (hstop : packet.quitTime n = some stop)
    (δ : ℝ) (hδ : 0 < δ) :
    let profile := quittingStoppingLawObserverAbsentCarrierProfile packet n
    let owner := quittingStoppingLawObserverAbsentOwner packet
    let charge := quittingStoppingLawObserverAbsentMassLower packet *
      regime.terminalGap
    (∃ deviation : (quittingGame reward).BehaviorStrategy owner,
      charge / 2 - δ ≤
        quittingTerminalPayoff reward
            (Function.update profile owner deviation) owner -
          quittingTerminalPayoff reward profile owner) ∨
    (∃ who : ι, ∃ deviation : (quittingGame reward).BehaviorStrategy who,
      charge / 12 ≤ (Fintype.card ι : ℝ) *
        (quittingTerminalPayoff reward
            (Function.update profile who deviation) who -
          quittingTerminalPayoff reward profile who)) ∨
    (∃ who coalition,
      coalition ∈ (Finset.univ.erase who).powerset ∧
      charge / 12 ≤
        (Fintype.card ι : ℝ) *
          (((Finset.univ.erase who).powerset.card : ℝ) *
            quittingFiniteQuitDefectAtomOccupationAt reward
              (fun time => (quittingTerminalSemanticPair reward
                (quittingAllContinueProfileSpine reward profile
                  (time + 1))).1)
              (quittingProfileLiveRoot reward profile)
              (quittingLiveMass reward profile) stop who coalition)) ∨
    (∃ who action, who ≠ owner ∧
      ((action = false ∧
        ∃ deviation : (quittingGame reward).BehaviorStrategy who,
          charge / (24 * (Fintype.card (ι × Bool) : ℝ)) ≤
            quittingTerminalPayoff reward
                (Function.update profile who deviation) who -
              quittingTerminalPayoff reward profile who) ∨
       (action = true ∧
        ∃ coalition ∈ (Finset.univ.erase who).powerset,
          charge / (24 * (Fintype.card (ι × Bool) : ℝ)) ≤
            (((Finset.univ.erase who).powerset.card : ℝ) *
              quittingFiniteQuitDefectAtomOccupationAt reward
                (fun time => (quittingTerminalSemanticPair reward
                  (quittingAllContinueProfileSpine reward profile
                    (time + 1))).1)
                (quittingProfileLiveRoot reward profile)
                (quittingLiveMass reward profile) stop who coalition)) ∨
       charge / (24 * (Fintype.card (ι × Bool) : ℝ)) ≤
        quittingFiniteCertifiedPacketContinueFaceLoss reward profile
          packet.terminal owner who action stop)) := by
  classical
  dsimp only
  let profile := quittingStoppingLawObserverAbsentCarrierProfile packet n
  let owner := quittingStoppingLawObserverAbsentOwner packet
  let charge := quittingStoppingLawObserverAbsentMassLower packet *
    regime.terminalGap
  have hchargePos : 0 < charge := mul_pos
    packet.observerAbsentMassLower_pos regime.terminalGap_pos
  have hsplit := packet.observerAbsent_finiteClock_strategicSplit habsent
    n stop hstop δ hδ
  rcases hsplit with hforced | hrefusal
  · have hdispatch :=
      exists_continueDeviation_or_fixedQuitAtom_or_certifiedRectanglePacket
        reward profile packet.terminal owner stop (charge / 2)
          (div_pos hchargePos (by norm_num)) hforced
    rcases hdispatch with hcontinue | hquit | hcertified
    · right; left
      simpa only [show (charge / 2) / 6 = charge / 12 by ring] using hcontinue
    · right; right; left
      simpa only [show (charge / 2) / 6 = charge / 12 by ring] using hquit
    · rcases hcertified with ⟨who, action, hwho, hpacket⟩
      have hlabelCard : 0 < (Fintype.card (ι × Bool) : ℝ) := by
        exact_mod_cast Fintype.card_pos_iff.mpr ⟨(owner, false)⟩
      have hpacketLower :
          charge / (12 * (Fintype.card (ι × Bool) : ℝ)) ≤
            quittingFiniteCertifiedForcedOwnerRectanglePacket reward profile
              packet.terminal owner who action stop := by
        apply (div_le_iff₀ (mul_pos (by norm_num) hlabelCard)).2
        calc
          charge = 12 * (charge / 12) := by ring
          _ ≤ 12 * ((Fintype.card (ι × Bool) : ℝ) *
              quittingFiniteCertifiedForcedOwnerRectanglePacket reward profile
                packet.terminal owner who action stop) :=
            mul_le_mul_of_nonneg_left (by
              simpa only [show (charge / 2) / 6 = charge / 12 by ring]
                using hpacket) (by norm_num)
          _ = quittingFiniteCertifiedForcedOwnerRectanglePacket reward profile
                packet.terminal owner who action stop *
              (12 * (Fintype.card (ι × Bool) : ℝ)) := by ring
      have hrefined := exists_sourceConsumer_or_certifiedEndpointFlipLoss
        reward profile packet.terminal owner who action stop hwho.symm
          (quittingStoppingLawObserverAbsentOwner_mem packet)
          (charge / (12 * (Fintype.card (ι × Bool) : ℝ))) hpacketLower
      right; right; right
      refine ⟨who, action, hwho, ?_⟩
      simpa only [show
        (charge / (12 * (Fintype.card (ι × Bool) : ℝ))) / 2 =
          charge / (24 * (Fintype.card (ι × Bool) : ℝ)) by ring] using hrefined
  · left
    simpa only [charge, profile, owner] using hrefusal

end QuittingStoppingLawVanishingDebtRectangleSequence

/-- Every positive certified flip loss has a literal pure-background host.
All ambient players enter its four payoff cells only through the displayed
coalition, which excludes the owner and outsider. -/
theorem exists_literal_endpointFlip_backgroundHost_of_positive_supportedLoss
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (terminal : {S : Finset ι // S.Nonempty})
    (owner who : ι) (action : Bool) (cutoff : ℕ)
    (hpositive : 0 < quittingFiniteCertifiedPacketContinueFaceLoss
      reward profile terminal owner who action cutoff) :
    ∃ time ∈ Finset.range cutoff, ∃ background : ι → Bool,
      let root := quittingProfileLiveRoot reward profile time
      let tail := (quittingTerminalSemanticPair reward
        (quittingAllContinueProfileSpine reward profile (time + 1))).1
      let T := quittingPureBackgroundCoalition background owner who
      0 < quittingCertifiedForcedOwnerRectanglePacket
          reward profile terminal owner who action time ∧
        quittingForcedOwnerBestEndpointAction reward tail root owner who =
          action ∧
        quittingRootBestEndpointAction reward tail
          (Function.update root owner (PMF.pure false)) who = !action ∧
        0 < ((pmfPi root) background).toReal ∧
        0 < quittingOrientedPureBackgroundSquare
          reward tail background owner who action ∧
        owner ∉ T ∧ who ∉ T := by
  obtain ⟨time, htime, hpacket, haction, _hforced, _hloss, hflip,
      hrectangle⟩ :=
    exists_literal_endpointFlip_of_positive_supportedLoss reward profile
      terminal owner who action cutoff hpositive
  let root := quittingProfileLiveRoot reward profile time
  let tail := (quittingTerminalSemanticPair reward
    (quittingAllContinueProfileSpine reward profile (time + 1))).1
  have hne : owner ≠ who := by
    have hprops := positive_certifiedForcedOwnerRectanglePacket_properties
      reward profile terminal owner who action time hpacket
    exact Ne.symm hprops.1
  obtain ⟨background, hbackgroundProb, hbackgroundSquare⟩ :=
    exists_positiveProbability_orientedPureBackgroundSquare_of_rectangle_pos
      reward tail root owner who hne action hrectangle
  refine ⟨time, htime, background, hpacket, haction, hflip,
    hbackgroundProb, hbackgroundSquare, ?_, ?_⟩
  · exact quittingPureBackgroundCoalition_not_mem_owner
      background owner who
  · exact quittingPureBackgroundCoalition_not_mem_who
      background owner who

end GameTheory
