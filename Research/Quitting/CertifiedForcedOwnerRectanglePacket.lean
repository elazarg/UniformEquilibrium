/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Research.Quitting.BestEndpointForcedOwnerRectanglePassport

/-!
# Certified forced-owner rectangle packets

Summing every positive square can lose the identity of the square that paid
the forced-owner wall.  This module keeps that identity.

At a literal row let `c = mass * forcedDefect / 2`.  A certified packet for
`(who, action)` has value `c` exactly when:

* `who` attains the forced-owner defect;
* the actual-row defect of `who` is strictly too small to pay `c`;
* `action` is `who`'s deterministic best endpoint on the forced-Quit face.

The canonical curvature alternative then proves that this very packet is
bounded by the same row, same coalition, same outsider, same action square.
Thus finite label selection cannot be hijacked by unrelated positive
curvature.
-/

noncomputable section

namespace GameTheory

open StochasticGame Math.Probability Math.PMFProduct

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The half-wall amount at one literal row. -/
def quittingForcedOwnerHalfWallCharge
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (terminal : {S : Finset ι // S.Nonempty})
    (owner : ι) (time : ℕ) : ℝ :=
  let root := quittingProfileLiveRoot reward profile time
  quittingStageCoalitionMass reward profile time terminal *
    quittingForcedOwnerOutsiderDefect reward
      (Function.update root owner (PMF.pure true)) owner / 2

/-- A row packet with payer, forced-defect witness, best endpoint, and
failure of actual-row payment all retained in its definition. -/
def quittingCertifiedForcedOwnerRectanglePacket
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (terminal : {S : Finset ι // S.Nonempty})
    (owner who : ι) (action : Bool) (time : ℕ) : ℝ :=
  let root := quittingProfileLiveRoot reward profile time
  let tail := (quittingTerminalSemanticPair reward
    (quittingAllContinueProfileSpine reward profile (time + 1))).1
  let forcedRoot := Function.update root owner (PMF.pure true)
  let forcedDefect :=
    quittingForcedOwnerOutsiderDefect reward forcedRoot owner
  let charge := quittingForcedOwnerHalfWallCharge
    reward profile terminal owner time
  if who = owner then 0 else
  if quittingForcedOwnerBestEndpointAction reward tail root owner who ≠
      action then 0 else
  if forcedDefect ≤
      quittingRootCoordinateNashDefect reward tail forcedRoot who ∧
    quittingLiveMass reward profile time *
        quittingRootCoordinateNashDefect reward tail root who < charge
  then charge else 0

theorem quittingForcedOwnerHalfWallCharge_nonneg
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (terminal : {S : Finset ι // S.Nonempty})
    (owner : ι) (time : ℕ) :
    0 ≤ quittingForcedOwnerHalfWallCharge
      reward profile terminal owner time := by
  unfold quittingForcedOwnerHalfWallCharge
  exact div_nonneg
    (mul_nonneg
      (quittingStageCoalitionMass_nonneg reward profile time terminal)
      (quittingForcedOwnerOutsiderDefect_nonneg reward _ owner))
    (by norm_num)

theorem quittingCertifiedForcedOwnerRectanglePacket_nonneg
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (terminal : {S : Finset ι // S.Nonempty})
    (owner who : ι) (action : Bool) (time : ℕ) :
    0 ≤ quittingCertifiedForcedOwnerRectanglePacket
      reward profile terminal owner who action time := by
  let root := quittingProfileLiveRoot reward profile time
  let tail := (quittingTerminalSemanticPair reward
    (quittingAllContinueProfileSpine reward profile (time + 1))).1
  let forcedRoot := Function.update root owner (PMF.pure true)
  let forcedDefect :=
    quittingForcedOwnerOutsiderDefect reward forcedRoot owner
  let charge := quittingForcedOwnerHalfWallCharge
    reward profile terminal owner time
  change 0 ≤ if who = owner then 0 else
    if quittingForcedOwnerBestEndpointAction reward tail root owner who ≠
        action then 0 else
    if forcedDefect ≤
        quittingRootCoordinateNashDefect reward tail forcedRoot who ∧
      quittingLiveMass reward profile time *
          quittingRootCoordinateNashDefect reward tail root who < charge
    then charge else 0
  split_ifs
  · exact le_rfl
  · exact le_rfl
  · exact quittingForcedOwnerHalfWallCharge_nonneg
      reward profile terminal owner time
  · exact le_rfl

/-- A positive packet exposes every item in its certificate. -/
theorem positive_certifiedForcedOwnerRectanglePacket_properties
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (terminal : {S : Finset ι // S.Nonempty})
    (owner who : ι) (action : Bool) (time : ℕ)
    (hpositive : 0 < quittingCertifiedForcedOwnerRectanglePacket
      reward profile terminal owner who action time) :
    let root := quittingProfileLiveRoot reward profile time
    let tail := (quittingTerminalSemanticPair reward
      (quittingAllContinueProfileSpine reward profile (time + 1))).1
    let forcedRoot := Function.update root owner (PMF.pure true)
    let forcedDefect :=
      quittingForcedOwnerOutsiderDefect reward forcedRoot owner
    let charge := quittingForcedOwnerHalfWallCharge
      reward profile terminal owner time
    who ≠ owner ∧
      quittingForcedOwnerBestEndpointAction reward tail root owner who =
        action ∧
      0 < forcedDefect ∧
      forcedDefect ≤
        quittingRootCoordinateNashDefect reward tail forcedRoot who ∧
      quittingLiveMass reward profile time *
          quittingRootCoordinateNashDefect reward tail root who < charge ∧
      quittingCertifiedForcedOwnerRectanglePacket
        reward profile terminal owner who action time = charge := by
  dsimp only
  let root := quittingProfileLiveRoot reward profile time
  let tail := (quittingTerminalSemanticPair reward
    (quittingAllContinueProfileSpine reward profile (time + 1))).1
  let forcedRoot := Function.update root owner (PMF.pure true)
  let forcedDefect :=
    quittingForcedOwnerOutsiderDefect reward forcedRoot owner
  let charge := quittingForcedOwnerHalfWallCharge
    reward profile terminal owner time
  have hwho : who ≠ owner := by
    intro heq
    unfold quittingCertifiedForcedOwnerRectanglePacket at hpositive
    simp [heq] at hpositive
  have haction : quittingForcedOwnerBestEndpointAction
      reward tail root owner who = action := by
    by_contra hne
    unfold quittingCertifiedForcedOwnerRectanglePacket at hpositive
    rw [if_neg hwho] at hpositive
    change 0 < (if quittingForcedOwnerBestEndpointAction
        reward tail root owner who ≠ action then 0 else
      if forcedDefect ≤
          quittingRootCoordinateNashDefect reward tail forcedRoot who ∧
        quittingLiveMass reward profile time *
            quittingRootCoordinateNashDefect reward tail root who < charge
      then charge else 0) at hpositive
    rw [if_pos hne] at hpositive
    linarith
  have hcert : forcedDefect ≤
        quittingRootCoordinateNashDefect reward tail forcedRoot who ∧
      quittingLiveMass reward profile time *
          quittingRootCoordinateNashDefect reward tail root who < charge := by
    by_contra hnot
    unfold quittingCertifiedForcedOwnerRectanglePacket at hpositive
    rw [if_neg hwho] at hpositive
    change 0 < (if quittingForcedOwnerBestEndpointAction
        reward tail root owner who ≠ action then 0 else
      if forcedDefect ≤
          quittingRootCoordinateNashDefect reward tail forcedRoot who ∧
        quittingLiveMass reward profile time *
            quittingRootCoordinateNashDefect reward tail root who < charge
      then charge else 0) at hpositive
    have hnotne : ¬ quittingForcedOwnerBestEndpointAction
        reward tail root owner who ≠ action := fun hne => hne haction
    rw [if_neg hnotne, if_neg hnot] at hpositive
    linarith
  have hpacket : quittingCertifiedForcedOwnerRectanglePacket
      reward profile terminal owner who action time = charge := by
    have hnotne : ¬ quittingForcedOwnerBestEndpointAction
        reward tail root owner who ≠ action := fun hne => hne haction
    change (if who = owner then 0 else
      if quittingForcedOwnerBestEndpointAction
          reward tail root owner who ≠ action then 0 else
      if forcedDefect ≤
          quittingRootCoordinateNashDefect reward tail forcedRoot who ∧
        quittingLiveMass reward profile time *
            quittingRootCoordinateNashDefect reward tail root who < charge
      then charge else 0) = charge
    rw [if_neg hwho, if_neg hnotne, if_pos hcert]
  have hchargePos : 0 < charge := by rw [← hpacket]; exact hpositive
  have hmass0 : 0 ≤ quittingStageCoalitionMass reward profile time terminal :=
    quittingStageCoalitionMass_nonneg reward profile time terminal
  have hforced0 : 0 ≤ forcedDefect :=
    quittingForcedOwnerOutsiderDefect_nonneg reward forcedRoot owner
  have hforcedPos : 0 < forcedDefect := by
    unfold charge quittingForcedOwnerHalfWallCharge at hchargePos
    nlinarith
  exact ⟨hwho, haction, hforcedPos, hcert.1, hcert.2, hpacket⟩

/-- **Literal packet-to-square passport.**  Every certified packet is paid
by its own best-endpoint rectangle, not merely by an aggregate square sum. -/
theorem certifiedForcedOwnerRectanglePacket_le_sameRectangle
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (terminal : {S : Finset ι // S.Nonempty})
    (owner who : ι) (action : Bool) (time : ℕ)
    (howner : owner ∈ terminal.val) :
    quittingCertifiedForcedOwnerRectanglePacket
        reward profile terminal owner who action time ≤
      max (quittingStageCoalitionMass reward profile time terminal *
        ((quittingProfileLiveRoot reward profile time) owner false).toReal *
          quittingOwnerOutsiderDeviationRectangle reward
            (quittingTerminalSemanticPair reward
              (quittingAllContinueProfileSpine reward profile
                (time + 1))).1
            (quittingProfileLiveRoot reward profile time)
            owner who action) 0 := by
  classical
  let root := quittingProfileLiveRoot reward profile time
  let tail := (quittingTerminalSemanticPair reward
    (quittingAllContinueProfileSpine reward profile (time + 1))).1
  let forcedRoot := Function.update root owner (PMF.pure true)
  let forcedDefect :=
    quittingForcedOwnerOutsiderDefect reward forcedRoot owner
  let charge := quittingForcedOwnerHalfWallCharge
    reward profile terminal owner time
  by_cases hwho : who = owner
  · have hzero : quittingCertifiedForcedOwnerRectanglePacket
          reward profile terminal owner who action time = 0 := by
      unfold quittingCertifiedForcedOwnerRectanglePacket
      rw [if_pos hwho]
    rw [hzero]
    exact le_max_right _ _
  · by_cases haction : quittingForcedOwnerBestEndpointAction
        reward tail root owner who = action
    · by_cases hcert : forcedDefect ≤
          quittingRootCoordinateNashDefect reward tail forcedRoot who ∧
        quittingLiveMass reward profile time *
            quittingRootCoordinateNashDefect reward tail root who < charge
      · have hpacket : quittingCertifiedForcedOwnerRectanglePacket
            reward profile terminal owner who action time = charge := by
          have hnotne : ¬ quittingForcedOwnerBestEndpointAction
              reward tail root owner who ≠ action := fun hne => hne haction
          change (if who = owner then 0 else
            if quittingForcedOwnerBestEndpointAction
                reward tail root owner who ≠ action then 0 else
            if forcedDefect ≤
                quittingRootCoordinateNashDefect reward tail forcedRoot who ∧
              quittingLiveMass reward profile time *
                  quittingRootCoordinateNashDefect reward tail root who < charge
            then charge else 0) = charge
          rw [if_neg hwho, if_neg hnotne, if_pos hcert]
        rw [hpacket]
        obtain ⟨hrealize, halt⟩ :=
          stageCoalitionMass_mul_forcedOwnerDefect_actual_or_bestRectangle
            reward profile tail time owner who (Ne.symm hwho) terminal howner
        have hmass0 : 0 ≤
            quittingStageCoalitionMass reward profile time terminal :=
          quittingStageCoalitionMass_nonneg reward profile time terminal
        have hweighted :
            quittingStageCoalitionMass reward profile time terminal *
                forcedDefect ≤
              quittingStageCoalitionMass reward profile time terminal *
                quittingRootCoordinateNashDefect reward tail forcedRoot who :=
          mul_le_mul_of_nonneg_left hcert.1 hmass0
        have hhalf : charge ≤
            quittingStageCoalitionMass reward profile time terminal *
              quittingRootCoordinateNashDefect reward tail forcedRoot who / 2 := by
          unfold charge quittingForcedOwnerHalfWallCharge
          exact div_le_div_of_nonneg_right hweighted (by norm_num)
        rw [← hrealize] at hhalf
        rcases halt with hactual | hrectangle
        · have : charge ≤ quittingLiveMass reward profile time *
              quittingRootCoordinateNashDefect reward tail root who :=
            hhalf.trans hactual
          linarith
        · have hsquare : charge ≤
              quittingStageCoalitionMass reward profile time terminal *
                (root owner false).toReal *
                  quittingForcedOwnerBestEndpointRectangle
                    reward tail root owner who :=
            hhalf.trans hrectangle
          rw [quittingForcedOwnerBestEndpointRectangle, haction] at hsquare
          exact hsquare.trans (le_max_left _ _)
      · have hzero : quittingCertifiedForcedOwnerRectanglePacket
            reward profile terminal owner who action time = 0 := by
          have hnotne : ¬ quittingForcedOwnerBestEndpointAction
              reward tail root owner who ≠ action := fun hne => hne haction
          change (if who = owner then 0 else
            if quittingForcedOwnerBestEndpointAction
                reward tail root owner who ≠ action then 0 else
            if forcedDefect ≤
                quittingRootCoordinateNashDefect reward tail forcedRoot who ∧
              quittingLiveMass reward profile time *
                  quittingRootCoordinateNashDefect reward tail root who < charge
            then charge else 0) = 0
          rw [if_neg hwho, if_neg hnotne, if_neg hcert]
        rw [hzero]
        exact le_max_right _ _
    · have hzero : quittingCertifiedForcedOwnerRectanglePacket
          reward profile terminal owner who action time = 0 := by
        change (if who = owner then 0 else
          if quittingForcedOwnerBestEndpointAction
              reward tail root owner who ≠ action then 0 else
          if forcedDefect ≤
              quittingRootCoordinateNashDefect reward tail forcedRoot who ∧
            quittingLiveMass reward profile time *
                quittingRootCoordinateNashDefect reward tail root who < charge
          then charge else 0) = 0
        rw [if_neg hwho, if_pos haction]
      rw [hzero]
      exact le_max_right _ _

/-- Total certified packet mass at one row. -/
def quittingCertifiedForcedOwnerRectangleRowTotal
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (terminal : {S : Finset ι // S.Nonempty})
    (owner : ι) (time : ℕ) : ℝ :=
  ∑ who, ∑ action,
    quittingCertifiedForcedOwnerRectanglePacket
      reward profile terminal owner who action time

theorem quittingCertifiedForcedOwnerRectangleRowTotal_nonneg
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (terminal : {S : Finset ι // S.Nonempty})
    (owner : ι) (time : ℕ) :
    0 ≤ quittingCertifiedForcedOwnerRectangleRowTotal
      reward profile terminal owner time := by
  unfold quittingCertifiedForcedOwnerRectangleRowTotal
  exact Finset.sum_nonneg fun who _ => Finset.sum_nonneg fun action _ =>
    quittingCertifiedForcedOwnerRectanglePacket_nonneg
      reward profile terminal owner who action time

/-- **No-theft row split.**  Half of the forced wall is paid either by the
actual total Nash defect or by certified packets.  Unlike a sum of all
positive squares, every packet in the second term retains a forced-defect
witness and is bounded by its own literal rectangle. -/
theorem forcedOwnerHalfWallCharge_le_actualDefect_add_certifiedPackets
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (terminal : {S : Finset ι // S.Nonempty})
    (owner : ι) (time : ℕ) :
    let root := quittingProfileLiveRoot reward profile time
    let tail := (quittingTerminalSemanticPair reward
      (quittingAllContinueProfileSpine reward profile (time + 1))).1
    quittingForcedOwnerHalfWallCharge reward profile terminal owner time ≤
      quittingLiveMass reward profile time *
          quittingRootTotalNashDefect reward tail root +
        quittingCertifiedForcedOwnerRectangleRowTotal
          reward profile terminal owner time := by
  classical
  dsimp only
  let root := quittingProfileLiveRoot reward profile time
  let tail := (quittingTerminalSemanticPair reward
    (quittingAllContinueProfileSpine reward profile (time + 1))).1
  let forcedRoot := Function.update root owner (PMF.pure true)
  let forcedDefect :=
    quittingForcedOwnerOutsiderDefect reward forcedRoot owner
  let charge := quittingForcedOwnerHalfWallCharge
    reward profile terminal owner time
  let actual := quittingLiveMass reward profile time *
    quittingRootTotalNashDefect reward tail root
  have hactual0 : 0 ≤ actual := mul_nonneg
    (quittingLiveMass_nonneg reward profile time)
    (quittingRootTotalNashDefect_nonneg reward tail root)
  have hpackets0 : 0 ≤ quittingCertifiedForcedOwnerRectangleRowTotal
      reward profile terminal owner time :=
    quittingCertifiedForcedOwnerRectangleRowTotal_nonneg
      reward profile terminal owner time
  by_cases hpaid : charge ≤ actual
  · exact hpaid.trans (le_add_of_nonneg_right hpackets0)
  · have hchargePos : 0 < charge := lt_of_le_of_lt hactual0 (lt_of_not_ge hpaid)
    have hmass0 : 0 ≤
        quittingStageCoalitionMass reward profile time terminal :=
      quittingStageCoalitionMass_nonneg reward profile time terminal
    have hforced0 : 0 ≤ forcedDefect :=
      quittingForcedOwnerOutsiderDefect_nonneg reward forcedRoot owner
    have hforcedPos : 0 < forcedDefect := by
      unfold charge quittingForcedOwnerHalfWallCharge at hchargePos
      nlinarith
    obtain ⟨who, hwho, hcoordinate⟩ :=
      exists_outsider_coordinateNashDefect_ge_of_forcedOwnerDefect_ge
        reward tail forcedRoot owner (by simp [forcedRoot]) hforcedPos le_rfl
    let action := quittingForcedOwnerBestEndpointAction
      reward tail root owner who
    have hcoordinateTotal :=
      quittingRootCoordinateNashDefect_le_total reward tail root who
    have hactualWho : quittingLiveMass reward profile time *
          quittingRootCoordinateNashDefect reward tail root who ≤ actual :=
      mul_le_mul_of_nonneg_left hcoordinateTotal
        (quittingLiveMass_nonneg reward profile time)
    have hactualWhoLt : quittingLiveMass reward profile time *
          quittingRootCoordinateNashDefect reward tail root who < charge :=
      lt_of_le_of_lt hactualWho (lt_of_not_ge hpaid)
    have hpacket : quittingCertifiedForcedOwnerRectanglePacket
          reward profile terminal owner who action time = charge := by
      change (if who = owner then 0 else
        if quittingForcedOwnerBestEndpointAction
            reward tail root owner who ≠ action then 0 else
        if forcedDefect ≤
            quittingRootCoordinateNashDefect reward tail forcedRoot who ∧
          quittingLiveMass reward profile time *
              quittingRootCoordinateNashDefect reward tail root who < charge
        then charge else 0) = charge
      have hnotne : ¬ quittingForcedOwnerBestEndpointAction
          reward tail root owner who ≠ action := by
        intro hne
        exact hne rfl
      rw [if_neg hwho, if_neg hnotne,
        if_pos ⟨hcoordinate, hactualWhoLt⟩]
    have hselected : charge ≤
        quittingCertifiedForcedOwnerRectangleRowTotal
          reward profile terminal owner time := by
      unfold quittingCertifiedForcedOwnerRectangleRowTotal
      have hactionLe :
          quittingCertifiedForcedOwnerRectanglePacket
              reward profile terminal owner who action time ≤
            ∑ endpoint,
              quittingCertifiedForcedOwnerRectanglePacket
                reward profile terminal owner who endpoint time :=
        Finset.single_le_sum
          (fun endpoint _ =>
            quittingCertifiedForcedOwnerRectanglePacket_nonneg
              reward profile terminal owner who endpoint time)
          (Finset.mem_univ action)
      have hwhoLe : (∑ endpoint,
            quittingCertifiedForcedOwnerRectanglePacket
              reward profile terminal owner who endpoint time) ≤
          ∑ player, ∑ endpoint,
            quittingCertifiedForcedOwnerRectanglePacket
              reward profile terminal owner player endpoint time :=
        Finset.single_le_sum
          (fun player _ => Finset.sum_nonneg fun endpoint _ =>
            quittingCertifiedForcedOwnerRectanglePacket_nonneg
              reward profile terminal owner player endpoint time)
          (Finset.mem_univ who)
      rw [← hpacket]
      exact hactionLe.trans hwhoLe
    exact hselected.trans (le_add_of_nonneg_left hactual0)

/-- Certified packet occupation of one fixed outsider/action label. -/
def quittingFiniteCertifiedForcedOwnerRectanglePacket
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (terminal : {S : Finset ι // S.Nonempty})
    (owner who : ι) (action : Bool) (cutoff : ℕ) : ℝ :=
  ∑ time ∈ Finset.range cutoff,
    quittingCertifiedForcedOwnerRectanglePacket
      reward profile terminal owner who action time

/-- Total certified packet occupation on a finite clock. -/
def quittingFiniteCertifiedForcedOwnerRectangleTotal
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (terminal : {S : Finset ι // S.Nonempty})
    (owner : ι) (cutoff : ℕ) : ℝ :=
  ∑ time ∈ Finset.range cutoff,
    quittingCertifiedForcedOwnerRectangleRowTotal
      reward profile terminal owner time

theorem quittingFiniteCertifiedForcedOwnerRectanglePacket_nonneg
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (terminal : {S : Finset ι // S.Nonempty})
    (owner who : ι) (action : Bool) (cutoff : ℕ) :
    0 ≤ quittingFiniteCertifiedForcedOwnerRectanglePacket
      reward profile terminal owner who action cutoff := by
  unfold quittingFiniteCertifiedForcedOwnerRectanglePacket
  exact Finset.sum_nonneg fun time _ =>
    quittingCertifiedForcedOwnerRectanglePacket_nonneg
      reward profile terminal owner who action time

/-- Finite total equals the sum of its fixed labels. -/
theorem quittingFiniteCertifiedForcedOwnerRectangleTotal_eq_sum_labels
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (terminal : {S : Finset ι // S.Nonempty})
    (owner : ι) (cutoff : ℕ) :
    quittingFiniteCertifiedForcedOwnerRectangleTotal
        reward profile terminal owner cutoff =
      ∑ who, ∑ action,
        quittingFiniteCertifiedForcedOwnerRectanglePacket
          reward profile terminal owner who action cutoff := by
  unfold quittingFiniteCertifiedForcedOwnerRectangleTotal
    quittingCertifiedForcedOwnerRectangleRowTotal
    quittingFiniteCertifiedForcedOwnerRectanglePacket
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro who _
  rw [Finset.sum_comm]

/-- Summed no-theft account. -/
theorem sum_forcedOwnerHalfWallCharge_le_actualDefect_add_certifiedPackets
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (terminal : {S : Finset ι // S.Nonempty})
    (owner : ι) (cutoff : ℕ) :
    (∑ time ∈ Finset.range cutoff,
      quittingForcedOwnerHalfWallCharge
        reward profile terminal owner time) ≤
      quittingFiniteActualDefectOccupation reward profile cutoff +
        quittingFiniteCertifiedForcedOwnerRectangleTotal
          reward profile terminal owner cutoff := by
  have hsum := Finset.sum_le_sum fun time
      (_htime : time ∈ Finset.range cutoff) =>
    forcedOwnerHalfWallCharge_le_actualDefect_add_certifiedPackets
      reward profile terminal owner time
  calc
    _ ≤ (∑ time ∈ Finset.range cutoff,
          quittingLiveMass reward profile time *
            quittingRootTotalNashDefect reward
              (quittingTerminalSemanticPair reward
                (quittingAllContinueProfileSpine reward profile
                  (time + 1))).1
              (quittingProfileLiveRoot reward profile time)) +
        ∑ time ∈ Finset.range cutoff,
          quittingCertifiedForcedOwnerRectangleRowTotal
            reward profile terminal owner time := by
      simpa only [Finset.sum_add_distrib] using hsum
    _ = _ := by
      unfold quittingFiniteActualDefectOccupation
        quittingRootTotalNashDefect
        quittingFiniteCertifiedForcedOwnerRectangleTotal
      rfl

/-- A fixed certified label is itself bounded by the chronological sum of
its own literal best-endpoint squares. -/
theorem finiteCertifiedPacket_le_sameRectangleOccupation
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (terminal : {S : Finset ι // S.Nonempty})
    (owner who : ι) (action : Bool) (cutoff : ℕ)
    (howner : owner ∈ terminal.val) :
    quittingFiniteCertifiedForcedOwnerRectanglePacket
        reward profile terminal owner who action cutoff ≤
      ∑ time ∈ Finset.range cutoff,
        max (quittingStageCoalitionMass reward profile time terminal *
          ((quittingProfileLiveRoot reward profile time) owner false).toReal *
            quittingOwnerOutsiderDeviationRectangle reward
              (quittingTerminalSemanticPair reward
                (quittingAllContinueProfileSpine reward profile
                  (time + 1))).1
              (quittingProfileLiveRoot reward profile time)
              owner who action) 0 := by
  unfold quittingFiniteCertifiedForcedOwnerRectanglePacket
  exact Finset.sum_le_sum fun time _ =>
    certifiedForcedOwnerRectanglePacket_le_sameRectangle
      reward profile terminal owner who action time howner

/-- Freeze one certified outsider/action label. -/
theorem exists_fixed_finiteCertifiedForcedOwnerRectanglePacket
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (terminal : {S : Finset ι // S.Nonempty})
    (owner : ι) (cutoff : ℕ)
    (hpositive : 0 < quittingFiniteCertifiedForcedOwnerRectangleTotal
      reward profile terminal owner cutoff) :
    ∃ who action, who ≠ owner ∧
      quittingFiniteCertifiedForcedOwnerRectangleTotal
          reward profile terminal owner cutoff ≤
        (Fintype.card (ι × Bool) : ℝ) *
          quittingFiniteCertifiedForcedOwnerRectanglePacket
            reward profile terminal owner who action cutoff := by
  letI : Nonempty (ι × Bool) := ⟨(owner, false)⟩
  let occupation : ι × Bool → ℝ := fun label =>
    quittingFiniteCertifiedForcedOwnerRectanglePacket reward profile terminal
      owner label.1 label.2 cutoff
  obtain ⟨label, _hlabel, hmax⟩ := Finset.exists_max_image
    (Finset.univ : Finset (ι × Bool)) occupation Finset.univ_nonempty
  have hsumLe : (∑ candidate, occupation candidate) ≤
      (Fintype.card (ι × Bool) : ℝ) * occupation label := by
    have h := (Finset.univ : Finset (ι × Bool)).sum_le_card_nsmul occupation
      (occupation label) (fun candidate hcandidate => hmax candidate hcandidate)
    simpa [nsmul_eq_mul] using h
  have hne : label.1 ≠ owner := by
    intro heq
    have hzero : occupation label = 0 := by
      unfold occupation quittingFiniteCertifiedForcedOwnerRectanglePacket
        quittingCertifiedForcedOwnerRectanglePacket
      simp [heq]
    have hallZero : ∀ candidate, occupation candidate ≤ 0 := by
      intro candidate
      simpa only [hzero] using hmax candidate (Finset.mem_univ candidate)
    have htotalNonneg : 0 ≤ ∑ candidate, occupation candidate :=
      Finset.sum_nonneg fun candidate _ =>
        quittingFiniteCertifiedForcedOwnerRectanglePacket_nonneg
          reward profile terminal owner candidate.1 candidate.2 cutoff
    have htotalZero : (∑ candidate, occupation candidate) = 0 :=
      le_antisymm (Finset.sum_nonpos fun candidate _ => hallZero candidate)
        htotalNonneg
    have htotal : (∑ candidate, occupation candidate) =
        quittingFiniteCertifiedForcedOwnerRectangleTotal
          reward profile terminal owner cutoff := by
      rw [quittingFiniteCertifiedForcedOwnerRectangleTotal_eq_sum_labels]
      rw [Fintype.sum_prod_type]
    have hbad : 0 < ∑ candidate, occupation candidate := by
      rw [htotal]
      exact hpositive
    rw [htotalZero] at hbad
    exact (lt_irrefl 0) hbad
  refine ⟨label.1, label.2, hne, ?_⟩
  rw [quittingFiniteCertifiedForcedOwnerRectangleTotal_eq_sum_labels]
  rw [Fintype.sum_prod_type] at hsumLe
  simpa only [occupation] using hsumLe

theorem sum_forcedOwnerHalfWallCharge_eq_half_sum
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (terminal : {S : Finset ι // S.Nonempty})
    (owner : ι) (cutoff : ℕ) :
    (∑ time ∈ Finset.range cutoff,
      quittingForcedOwnerHalfWallCharge
        reward profile terminal owner time) =
      (∑ time ∈ Finset.range cutoff,
        quittingStageCoalitionMass reward profile time terminal *
          quittingForcedOwnerOutsiderDefect reward
            (Function.update
              (quittingProfileLiveRoot reward profile time) owner
              (PMF.pure true)) owner) / 2 := by
  unfold quittingForcedOwnerHalfWallCharge
  rw [Finset.sum_div]

/-- **Exhaustive finite dispatch with no curvature theft.**  A forced-owner
wall is consumed by a legal Continue deviation, a fixed Quit atom, or a fixed
certified best-endpoint square packet.  In the last branch the same packet is
bounded by the chronological occupation of its own literal square, and each
charged row still carries the forced defect that created it. -/
theorem exists_continueDeviation_or_fixedQuitAtom_or_certifiedRectanglePacket
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (terminal : {S : Finset ι // S.Nonempty})
    (owner : ι) (cutoff : ℕ)
    (lower : ℝ) (hlower : 0 < lower)
    (hcharge : lower ≤
      ∑ time ∈ Finset.range cutoff,
        quittingStageCoalitionMass reward profile time terminal *
          quittingForcedOwnerOutsiderDefect reward
            (Function.update
              (quittingProfileLiveRoot reward profile time) owner
              (PMF.pure true)) owner) :
    (∃ who : ι, ∃ deviation : (quittingGame reward).BehaviorStrategy who,
      lower / 6 ≤ (Fintype.card ι : ℝ) *
        (quittingTerminalPayoff reward
            (Function.update profile who deviation) who -
          quittingTerminalPayoff reward profile who)) ∨
    (∃ who coalition,
      coalition ∈ (Finset.univ.erase who).powerset ∧
      lower / 6 ≤
        (Fintype.card ι : ℝ) *
          (((Finset.univ.erase who).powerset.card : ℝ) *
            quittingFiniteQuitDefectAtomOccupationAt reward
              (fun time => (quittingTerminalSemanticPair reward
                (quittingAllContinueProfileSpine reward profile
                  (time + 1))).1)
              (quittingProfileLiveRoot reward profile)
              (quittingLiveMass reward profile) cutoff who coalition)) ∨
    (∃ who action, who ≠ owner ∧
      lower / 6 ≤ (Fintype.card (ι × Bool) : ℝ) *
        quittingFiniteCertifiedForcedOwnerRectanglePacket
          reward profile terminal owner who action cutoff) := by
  let actual := quittingFiniteActualDefectOccupation reward profile cutoff
  let continueCharge :=
    quittingFiniteActualContinueDefectOccupation reward profile cutoff
  let quit := quittingFiniteActualQuitDefectOccupation reward profile cutoff
  let packet := quittingFiniteCertifiedForcedOwnerRectangleTotal
    reward profile terminal owner cutoff
  have haccount :=
    sum_forcedOwnerHalfWallCharge_le_actualDefect_add_certifiedPackets
      reward profile terminal owner cutoff
  have hhalfIdentity := sum_forcedOwnerHalfWallCharge_eq_half_sum
    reward profile terminal owner cutoff
  have hlowerHalf : lower / 2 ≤ actual + packet := by
    rw [hhalfIdentity] at haccount
    exact (div_le_div_of_nonneg_right hcharge (by norm_num)).trans
      (by simpa only [actual, packet] using haccount)
  have hpolarity : actual = continueCharge + quit := by
    simpa only [actual, continueCharge, quit] using
      quittingFiniteActualDefectOccupation_eq_polaritySum reward profile cutoff
  rw [hpolarity] at hlowerHalf
  letI : Nonempty ι := ⟨owner⟩
  by_cases hcontinue : lower / 6 ≤ continueCharge
  · left
    obtain ⟨who, deviation, hgain⟩ :=
      exists_fixedPlayer_behaviorDeviation_of_continueOccupation
        reward profile cutoff
    exact ⟨who, deviation, hcontinue.trans hgain⟩
  · have hquitPacket : lower / 3 ≤ quit + packet := by linarith
    by_cases hquit : lower / 6 ≤ quit
    · right; left
      obtain ⟨who, coalition, hcoalition, hatom⟩ :=
        exists_fixed_valid_quittingQuitDefectAtom reward
          (fun time => (quittingTerminalSemanticPair reward
            (quittingAllContinueProfileSpine reward profile
              (time + 1))).1)
          (quittingProfileLiveRoot reward profile)
          (quittingLiveMass reward profile) cutoff
          (quittingLiveMass_nonneg reward profile)
      refine ⟨who, coalition, hcoalition, hquit.trans ?_⟩
      simpa only [quit, quittingFiniteActualQuitDefectOccupation,
        mul_assoc] using hatom
    · have hpacketLower : lower / 6 ≤ packet := by linarith
      have hpacketPos : 0 < packet :=
        lt_of_lt_of_le (div_pos hlower (by norm_num)) hpacketLower
      right; right
      obtain ⟨who, action, hwho, hfixed⟩ :=
        exists_fixed_finiteCertifiedForcedOwnerRectanglePacket
          reward profile terminal owner cutoff
          (by simpa only [packet] using hpacketPos)
      exact ⟨who, action, hwho, hpacketLower.trans hfixed⟩

end GameTheory
