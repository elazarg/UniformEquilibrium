/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.StoppingLaw.ForcedOwnerDefectPolarity

/-!
# A best-endpoint passport for forced-owner rectangles

The chronological rectangle dispatcher freezes an outsider and a Boolean
action, but its raw charge does not remember that this action was selected as
a best endpoint on the owner-forced-Quit face.  That provenance is precisely
what is needed to interpret the square as two literal resets.

This file keeps the deterministic best-endpoint label before summation.  A
positive charge in one frozen `(outsider, action)` passport therefore says on
every charged row both:

* `action` is the deterministic best endpoint after forcing the owner to Quit;
* the same action has a positive owner-Quit/owner-Continue gain rectangle.

No chronology or recurrence conclusion is asserted.
-/

noncomputable section

namespace GameTheory

open StochasticGame Math.Probability Math.PMFProduct

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The deterministic selected endpoint realizes the coordinate Nash defect. -/
theorem quittingRootDeviationGain_bestEndpoint_eq_coordinateNashDefect
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : Payoff ι) (root : ι → PMF Bool) (who : ι) :
    quittingRootDeviationGain reward tail root who
        (PMF.pure (quittingRootBestEndpointAction reward tail root who)) =
      quittingRootCoordinateNashDefect reward tail root who := by
  unfold quittingRootDeviationGain
  exact quittingRootSuccessorPayoff_bestEndpoint_sub_eq_coordinateNashDefect
    reward tail root who

/-- The best endpoint used on the owner-forced-Quit face. -/
def quittingForcedOwnerBestEndpointAction
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : Payoff ι) (root : ι → PMF Bool)
    (owner who : ι) : Bool :=
  quittingRootBestEndpointAction reward tail
    (Function.update root owner (PMF.pure true)) who

/-- The same-witness rectangle evaluated at the forced-Quit best endpoint. -/
def quittingForcedOwnerBestEndpointRectangle
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : Payoff ι) (root : ι → PMF Bool)
    (owner who : ι) : ℝ :=
  quittingOwnerOutsiderDeviationRectangle reward tail root owner who
    (quittingForcedOwnerBestEndpointAction reward tail root owner who)

/-- **Best-labelled one-row localization.**  The witness in forced-owner
curvature may be chosen canonically: it is the deterministic best endpoint
on the forced-Quit face. -/
theorem forcedOwner_coordinateDefect_actual_or_bestEndpointRectangle
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : Payoff ι) (root : ι → PMF Bool)
    (owner who : ι) (hne : owner ≠ who) :
    let forcedRoot := Function.update root owner (PMF.pure true)
    let action := quittingForcedOwnerBestEndpointAction
      reward tail root owner who
    let quitGain := quittingRootDeviationGain reward tail forcedRoot who
      (PMF.pure action)
    let continueGain := quittingRootDeviationGain reward tail
      (Function.update root owner (PMF.pure false)) who (PMF.pure action)
    quitGain = quittingRootCoordinateNashDefect reward tail forcedRoot who ∧
      ((root owner true).toReal * quitGain / 2 ≤
          quittingRootCoordinateNashDefect reward tail root who ∨
        (root owner true).toReal * quitGain / 2 ≤
          (root owner true).toReal * (root owner false).toReal *
            (quitGain - continueGain)) := by
  dsimp only [quittingForcedOwnerBestEndpointAction]
  let forcedRoot := Function.update root owner (PMF.pure true)
  let action := quittingRootBestEndpointAction reward tail forcedRoot who
  let actualGain := quittingRootDeviationGain reward tail root who
    (PMF.pure action)
  let quitGain := quittingRootDeviationGain reward tail forcedRoot who
    (PMF.pure action)
  let continueGain := quittingRootDeviationGain reward tail
    (Function.update root owner (PMF.pure false)) who (PMF.pure action)
  have hrealize : quitGain =
      quittingRootCoordinateNashDefect reward tail forcedRoot who := by
    exact quittingRootDeviationGain_bestEndpoint_eq_coordinateNashDefect
      reward tail forcedRoot who
  refine ⟨hrealize, ?_⟩
  have haffine : actualGain =
      (root owner true).toReal * quitGain +
        (root owner false).toReal * continueGain := by
    exact quittingRootDeviationGain_eq_ownerEndpointMix reward tail root owner
      who hne (PMF.pure action)
  have hsum := quittingRoot_continueProbability_add_quitProbability root owner
  have hfalse : (root owner false).toReal =
      1 - (root owner true).toReal := by linarith
  have hq0 : 0 ≤ (root owner true).toReal := ENNReal.toReal_nonneg
  have hq1 : (root owner true).toReal ≤ 1 := by
    have hc0 : 0 ≤ (root owner false).toReal := ENNReal.toReal_nonneg
    linarith
  have halt := half_quitContribution_le_actual_or_rectangle
    (root owner true).toReal quitGain continueGain actualGain hq0 hq1
    (by rw [haffine, hfalse])
  rcases halt with hactual | hrectangle
  · left
    have hgainLe := pureEndpointDeviationGain_le_coordinateNashDefect
      reward tail root who action
    have hdefect0 := quittingRootCoordinateNashDefect_nonneg
      reward tail root who
    exact hactual.trans (max_le hgainLe hdefect0)
  · right
    simpa only [hfalse] using hrectangle

/-- Coalition-weighted form of the canonical best-endpoint localization. -/
theorem coalitionMass_mul_forcedOwnerDefect_actual_or_bestEndpointRectangle
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : Payoff ι) (root : ι → PMF Bool)
    (owner who : ι) (hne : owner ≠ who)
    (coalition : Finset ι) (howner : owner ∈ coalition) :
    let forcedRoot := Function.update root owner (PMF.pure true)
    let action := quittingForcedOwnerBestEndpointAction
      reward tail root owner who
    let quitGain := quittingRootDeviationGain reward tail forcedRoot who
      (PMF.pure action)
    let continueGain := quittingRootDeviationGain reward tail
      (Function.update root owner (PMF.pure false)) who (PMF.pure action)
    let mass := quittingRootCoalitionMass root coalition
    quitGain = quittingRootCoordinateNashDefect reward tail forcedRoot who ∧
      (mass * quitGain / 2 ≤
          quittingRootCoordinateNashDefect reward tail root who ∨
        mass * quitGain / 2 ≤
          mass * (root owner false).toReal * (quitGain - continueGain)) := by
  obtain ⟨hrealize, halt⟩ :=
    forcedOwner_coordinateDefect_actual_or_bestEndpointRectangle
      reward tail root owner who hne
  refine ⟨hrealize, ?_⟩
  let action := quittingForcedOwnerBestEndpointAction
    reward tail root owner who
  let quitGain := quittingRootDeviationGain reward tail
    (Function.update root owner (PMF.pure true)) who (PMF.pure action)
  let continueGain := quittingRootDeviationGain reward tail
    (Function.update root owner (PMF.pure false)) who (PMF.pure action)
  let mass := quittingRootCoalitionMass root coalition
  let forcedMass := quittingRootCoalitionMass
    (Function.update root owner (PMF.pure true)) coalition
  have hmass : mass = (root owner true).toReal * forcedMass :=
    quittingRootCoalitionMass_eq_ownerQuit_mul_forced root owner coalition howner
  have hforcedMass0 : 0 ≤ forcedMass :=
    MarkedAbsorptionCylinder.quittingRootCoalitionMass_nonneg _ _
  have hforcedMass1 : forcedMass ≤ 1 := by
    have hle := quittingRootCoalitionMass_le_quitProbability_of_mem
      (Function.update root owner (PMF.pure true)) coalition owner howner
    simpa [forcedMass] using hle
  have hactual0 : 0 ≤ quittingRootCoordinateNashDefect reward tail root who :=
    quittingRootCoordinateNashDefect_nonneg reward tail root who
  rcases halt with hactual | hrectangle
  · left
    calc
      mass * quitGain / 2 =
          forcedMass * ((root owner true).toReal * quitGain / 2) := by
        rw [hmass]
        ring
      _ ≤ forcedMass *
          quittingRootCoordinateNashDefect reward tail root who :=
        mul_le_mul_of_nonneg_left hactual hforcedMass0
      _ ≤ quittingRootCoordinateNashDefect reward tail root who :=
        mul_le_of_le_one_left hactual0 hforcedMass1
  · right
    calc
      mass * quitGain / 2 =
          forcedMass * ((root owner true).toReal * quitGain / 2) := by
        rw [hmass]
        ring
      _ ≤ forcedMass *
          ((root owner true).toReal * (root owner false).toReal *
            (quitGain - continueGain)) :=
        mul_le_mul_of_nonneg_left hrectangle hforcedMass0
      _ = mass * (root owner false).toReal *
          (quitGain - continueGain) := by
        rw [hmass]
        ring

/-- Chronological coalition-weighted form, still carrying the canonical
forced-face best action. -/
theorem stageCoalitionMass_mul_forcedOwnerDefect_actual_or_bestRectangle
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (tail : Payoff ι) (time : ℕ)
    (owner who : ι) (hne : owner ≠ who)
    (terminal : {S : Finset ι // S.Nonempty})
    (howner : owner ∈ terminal.val) :
    let root := quittingProfileLiveRoot reward profile time
    let forcedRoot := Function.update root owner (PMF.pure true)
    let action := quittingForcedOwnerBestEndpointAction
      reward tail root owner who
    let quitGain := quittingRootDeviationGain reward tail forcedRoot who
      (PMF.pure action)
    let continueGain := quittingRootDeviationGain reward tail
      (Function.update root owner (PMF.pure false)) who (PMF.pure action)
    let mass := quittingStageCoalitionMass reward profile time terminal
    quitGain = quittingRootCoordinateNashDefect reward tail forcedRoot who ∧
      (mass * quitGain / 2 ≤
          quittingLiveMass reward profile time *
            quittingRootCoordinateNashDefect reward tail root who ∨
        mass * quitGain / 2 ≤
          mass * (root owner false).toReal * (quitGain - continueGain)) := by
  let root := quittingProfileLiveRoot reward profile time
  obtain ⟨hrealize, halt⟩ :=
    coalitionMass_mul_forcedOwnerDefect_actual_or_bestEndpointRectangle
      reward tail root owner who hne terminal.val howner
  refine ⟨hrealize, ?_⟩
  let action := quittingForcedOwnerBestEndpointAction
    reward tail root owner who
  let quitGain := quittingRootDeviationGain reward tail
    (Function.update root owner (PMF.pure true)) who (PMF.pure action)
  let continueGain := quittingRootDeviationGain reward tail
    (Function.update root owner (PMF.pure false)) who (PMF.pure action)
  let rootMass := quittingRootCoalitionMass root terminal.val
  let mass := quittingStageCoalitionMass reward profile time terminal
  have hmass : mass = quittingLiveMass reward profile time * rootMass :=
    quittingStageCoalitionMass_eq_liveMass_mul_rootCoalitionMass
      reward profile time terminal
  have hlive0 : 0 ≤ quittingLiveMass reward profile time :=
    quittingLiveMass_nonneg reward profile time
  rcases halt with hactual | hrectangle
  · left
    calc
      mass * quitGain / 2 = quittingLiveMass reward profile time *
          (rootMass * quitGain / 2) := by
        rw [hmass]
        ring
      _ ≤ quittingLiveMass reward profile time *
          quittingRootCoordinateNashDefect reward tail root who :=
        mul_le_mul_of_nonneg_left hactual hlive0
  · right
    calc
      mass * quitGain / 2 = quittingLiveMass reward profile time *
          (rootMass * quitGain / 2) := by
        rw [hmass]
        ring
      _ ≤ quittingLiveMass reward profile time *
          (rootMass * (root owner false).toReal *
            (quitGain - continueGain)) :=
        mul_le_mul_of_nonneg_left hrectangle hlive0
      _ = mass * (root owner false).toReal *
          (quitGain - continueGain) := by
        rw [hmass]
        ring

/-- Sum of canonical best-endpoint rectangle charges at one literal row. -/
def quittingForcedOwnerBestRectangleRowTotal
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (terminal : {S : Finset ι // S.Nonempty})
    (owner : ι) (time : ℕ) : ℝ :=
  ∑ who,
    if who = owner then 0 else
      let root := quittingProfileLiveRoot reward profile time
      let tail := (quittingTerminalSemanticPair reward
        (quittingAllContinueProfileSpine reward profile (time + 1))).1
      quittingStageCoalitionMass reward profile time terminal *
        (root owner false).toReal *
          max (quittingForcedOwnerBestEndpointRectangle
            reward tail root owner who) 0

/-- **Witness-free row account with best-endpoint provenance.**  Compared
with the raw rectangle account, the Boolean witness has disappeared: every
square in the residual is evaluated at the forced-Quit best endpoint. -/
theorem stageCoalitionMass_mul_forcedOwnerOutsiderDefect_le_actual_add_bestRectangles
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (terminal : {S : Finset ι // S.Nonempty})
    (owner : ι) (howner : owner ∈ terminal.val) (time : ℕ) :
    let root := quittingProfileLiveRoot reward profile time
    let tail := (quittingTerminalSemanticPair reward
      (quittingAllContinueProfileSpine reward profile (time + 1))).1
    quittingStageCoalitionMass reward profile time terminal *
          quittingForcedOwnerOutsiderDefect reward
            (Function.update root owner (PMF.pure true)) owner / 2 ≤
      quittingLiveMass reward profile time *
          quittingRootTotalNashDefect reward tail root +
        quittingForcedOwnerBestRectangleRowTotal
          reward profile terminal owner time := by
  classical
  dsimp only
  let root := quittingProfileLiveRoot reward profile time
  let tail := (quittingTerminalSemanticPair reward
    (quittingAllContinueProfileSpine reward profile (time + 1))).1
  let forcedRoot := Function.update root owner (PMF.pure true)
  let forcedDefect := quittingForcedOwnerOutsiderDefect reward forcedRoot owner
  let mass := quittingStageCoalitionMass reward profile time terminal
  have hmass0 : 0 ≤ mass :=
    quittingStageCoalitionMass_nonneg reward profile time terminal
  have hlive0 : 0 ≤ quittingLiveMass reward profile time :=
    quittingLiveMass_nonneg reward profile time
  have hactual0 : 0 ≤ quittingLiveMass reward profile time *
      quittingRootTotalNashDefect reward tail root :=
    mul_nonneg hlive0 (quittingRootTotalNashDefect_nonneg reward tail root)
  have hrectangles0 : 0 ≤ quittingForcedOwnerBestRectangleRowTotal
      reward profile terminal owner time := by
    unfold quittingForcedOwnerBestRectangleRowTotal
    apply Finset.sum_nonneg
    intro who _
    split_ifs
    · exact le_rfl
    · exact mul_nonneg (mul_nonneg hmass0 ENNReal.toReal_nonneg)
        (le_max_right _ 0)
  change mass * forcedDefect / 2 ≤
    quittingLiveMass reward profile time *
        quittingRootTotalNashDefect reward tail root +
      quittingForcedOwnerBestRectangleRowTotal
        reward profile terminal owner time
  by_cases hpositive : 0 < forcedDefect
  · obtain ⟨who, hwho, hcoordinate⟩ :=
      exists_outsider_coordinateNashDefect_ge_of_forcedOwnerDefect_ge
        reward tail forcedRoot owner (by simp [forcedRoot]) hpositive le_rfl
    have hweighted : mass * forcedDefect ≤ mass *
        quittingRootCoordinateNashDefect reward tail forcedRoot who :=
      mul_le_mul_of_nonneg_left hcoordinate hmass0
    obtain ⟨hrealize, halt⟩ :=
      stageCoalitionMass_mul_forcedOwnerDefect_actual_or_bestRectangle
        reward profile tail time owner who hwho.symm terminal howner
    have hhalf : mass * forcedDefect / 2 ≤
        mass * quittingRootCoordinateNashDefect reward tail forcedRoot who / 2 :=
      div_le_div_of_nonneg_right hweighted (by norm_num)
    rw [← hrealize] at hhalf
    rcases halt with hactual | hrectangle
    · have hcoordinateTotal :=
        quittingRootCoordinateNashDefect_le_total reward tail root who
      have hscaled := mul_le_mul_of_nonneg_left hcoordinateTotal hlive0
      exact hhalf.trans (hactual.trans
        (hscaled.trans (le_add_of_nonneg_right hrectangles0)))
    · let rectangle := quittingForcedOwnerBestEndpointRectangle
        reward tail root owner who
      have hpositivePart : mass * (root owner false).toReal * rectangle ≤
          mass * (root owner false).toReal * max rectangle 0 :=
        mul_le_mul_of_nonneg_left (le_max_left rectangle 0)
          (mul_nonneg hmass0 ENNReal.toReal_nonneg)
      have hselected : mass * (root owner false).toReal * max rectangle 0 ≤
          quittingForcedOwnerBestRectangleRowTotal
            reward profile terminal owner time := by
        unfold quittingForcedOwnerBestRectangleRowTotal
        have hterm0 : ∀ player : ι, 0 ≤
            (if player = owner then 0 else
              mass * (root owner false).toReal *
                max (quittingForcedOwnerBestEndpointRectangle
                  reward tail root owner player) 0) := by
          intro player
          split_ifs
          · exact le_rfl
          · exact mul_nonneg
              (mul_nonneg hmass0 ENNReal.toReal_nonneg)
              (le_max_right _ 0)
        have hsingle := Finset.single_le_sum
          (fun player _ => hterm0 player) (Finset.mem_univ who)
        simpa [hwho, mass, root, tail, rectangle] using hsingle
      exact hhalf.trans (hrectangle.trans
        (hpositivePart.trans
          (hselected.trans (le_add_of_nonneg_left hactual0))))
  · have hforced0 : 0 ≤ forcedDefect :=
      quittingForcedOwnerOutsiderDefect_nonneg reward forcedRoot owner
    have hzero : forcedDefect = 0 :=
      le_antisymm (le_of_not_gt hpositive) hforced0
    rw [hzero, mul_zero, zero_div]
    exact add_nonneg hactual0 hrectangles0

/-- Total canonical best-rectangle occupation over a finite window. -/
def quittingFiniteForcedOwnerBestRectangleTotal
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (terminal : {S : Finset ι // S.Nonempty})
    (owner : ι) (cutoff : ℕ) : ℝ :=
  ∑ time ∈ Finset.range cutoff,
    quittingForcedOwnerBestRectangleRowTotal
      reward profile terminal owner time

/-- A finite-window passport charge.  The indicator is deliberately inside
the chronological sum: whenever a summand is nonzero, the frozen action is
literally the deterministic best endpoint at that row's forced-Quit face. -/
def quittingFiniteForcedOwnerBestRectanglePassport
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (terminal : {S : Finset ι // S.Nonempty})
    (owner who : ι) (action : Bool) (cutoff : ℕ) : ℝ :=
  ∑ time ∈ Finset.range cutoff,
    if who = owner then 0 else
      let root := quittingProfileLiveRoot reward profile time
      let tail := (quittingTerminalSemanticPair reward
        (quittingAllContinueProfileSpine reward profile (time + 1))).1
      if quittingForcedOwnerBestEndpointAction reward tail root owner who =
          action then
        quittingStageCoalitionMass reward profile time terminal *
          (root owner false).toReal *
            max (quittingForcedOwnerBestEndpointRectangle
              reward tail root owner who) 0
      else 0

theorem quittingFiniteForcedOwnerBestRectanglePassport_nonneg
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (terminal : {S : Finset ι // S.Nonempty})
    (owner who : ι) (action : Bool) (cutoff : ℕ) :
    0 ≤ quittingFiniteForcedOwnerBestRectanglePassport
      reward profile terminal owner who action cutoff := by
  unfold quittingFiniteForcedOwnerBestRectanglePassport
  by_cases hwho : who = owner
  · simp [hwho]
  · simp only [if_neg hwho]
    apply Finset.sum_nonneg
    intro time _
    let root := quittingProfileLiveRoot reward profile time
    let tail := (quittingTerminalSemanticPair reward
      (quittingAllContinueProfileSpine reward profile (time + 1))).1
    change 0 ≤ if quittingForcedOwnerBestEndpointAction
        reward tail root owner who = action then
      quittingStageCoalitionMass reward profile time terminal *
        (root owner false).toReal *
          max (quittingForcedOwnerBestEndpointRectangle
            reward tail root owner who) 0
      else 0
    split_ifs
    · exact mul_nonneg
        (mul_nonneg
          (quittingStageCoalitionMass_nonneg reward profile time terminal)
          ENNReal.toReal_nonneg)
        (le_max_right _ 0)
    · exact le_rfl

/-- The finite canonical charge is exactly the sum of the frozen
outsider/action passports. -/
theorem quittingFiniteForcedOwnerBestRectangleTotal_eq_sum_passports
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (terminal : {S : Finset ι // S.Nonempty})
    (owner : ι) (cutoff : ℕ) :
    quittingFiniteForcedOwnerBestRectangleTotal
        reward profile terminal owner cutoff =
      ∑ who, ∑ action,
        quittingFiniteForcedOwnerBestRectanglePassport
          reward profile terminal owner who action cutoff := by
  classical
  unfold quittingFiniteForcedOwnerBestRectangleTotal
    quittingForcedOwnerBestRectangleRowTotal
    quittingFiniteForcedOwnerBestRectanglePassport
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro who _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro time htime
  by_cases hwho : who = owner
  · simp [hwho]
  · simp only [if_neg hwho]
    let root := quittingProfileLiveRoot reward profile time
    let tail := (quittingTerminalSemanticPair reward
      (quittingAllContinueProfileSpine reward profile (time + 1))).1
    change quittingStageCoalitionMass reward profile time terminal *
          (root owner false).toReal *
            max (quittingForcedOwnerBestEndpointRectangle
              reward tail root owner who) 0 =
      ∑ action,
        if quittingForcedOwnerBestEndpointAction reward tail root owner who =
            action then
          quittingStageCoalitionMass reward profile time terminal *
            (root owner false).toReal *
              max (quittingForcedOwnerBestEndpointRectangle
                reward tail root owner who) 0
        else 0
    cases quittingForcedOwnerBestEndpointAction
        reward tail root owner who <;> simp

/-- Summed canonical row account. -/
theorem sum_stageCoalitionMass_mul_forcedOwnerDefect_half_le_actual_add_bestRectangle
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (terminal : {S : Finset ι // S.Nonempty})
    (owner : ι) (howner : owner ∈ terminal.val) (cutoff : ℕ) :
    (∑ time ∈ Finset.range cutoff,
        quittingStageCoalitionMass reward profile time terminal *
          quittingForcedOwnerOutsiderDefect reward
            (Function.update
              (quittingProfileLiveRoot reward profile time) owner
              (PMF.pure true)) owner) / 2 ≤
      quittingFiniteActualDefectOccupation reward profile cutoff +
        quittingFiniteForcedOwnerBestRectangleTotal
          reward profile terminal owner cutoff := by
  have hsum := Finset.sum_le_sum fun time
      (_htime : time ∈ Finset.range cutoff) =>
    stageCoalitionMass_mul_forcedOwnerOutsiderDefect_le_actual_add_bestRectangles
      reward profile terminal owner howner time
  rw [← Finset.sum_div] at hsum
  calc
    _ ≤ (∑ time ∈ Finset.range cutoff,
          quittingLiveMass reward profile time *
            quittingRootTotalNashDefect reward
              (quittingTerminalSemanticPair reward
                (quittingAllContinueProfileSpine reward profile
                  (time + 1))).1
              (quittingProfileLiveRoot reward profile time)) +
        ∑ time ∈ Finset.range cutoff,
          quittingForcedOwnerBestRectangleRowTotal
            reward profile terminal owner time := by
      simpa only [Finset.sum_add_distrib] using hsum
    _ = _ := by
      unfold quittingFiniteActualDefectOccupation
        quittingRootTotalNashDefect
        quittingFiniteForcedOwnerBestRectangleTotal
      rfl

/-- Freeze one outsider and one Boolean best-endpoint orientation while
retaining a finite-player fraction of the canonical rectangle charge. -/
theorem exists_fixed_forcedOwnerBestRectanglePassport
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (terminal : {S : Finset ι // S.Nonempty})
    (owner : ι) (cutoff : ℕ)
    (hpositive : 0 < quittingFiniteForcedOwnerBestRectangleTotal
      reward profile terminal owner cutoff) :
    ∃ who action, who ≠ owner ∧
      quittingFiniteForcedOwnerBestRectangleTotal
          reward profile terminal owner cutoff ≤
        (Fintype.card (ι × Bool) : ℝ) *
          quittingFiniteForcedOwnerBestRectanglePassport
            reward profile terminal owner who action cutoff := by
  letI : Nonempty (ι × Bool) := ⟨(owner, false)⟩
  let occupation : ι × Bool → ℝ := fun label =>
    quittingFiniteForcedOwnerBestRectanglePassport reward profile terminal
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
      unfold occupation quittingFiniteForcedOwnerBestRectanglePassport
      simp [heq]
    have hallZero : ∀ candidate, occupation candidate ≤ 0 := by
      intro candidate
      simpa only [hzero] using hmax candidate (Finset.mem_univ candidate)
    have htotalNonneg : 0 ≤ ∑ candidate, occupation candidate :=
      Finset.sum_nonneg fun candidate _ =>
        quittingFiniteForcedOwnerBestRectanglePassport_nonneg
          reward profile terminal owner candidate.1 candidate.2 cutoff
    have htotalZero : (∑ candidate, occupation candidate) = 0 :=
      le_antisymm (Finset.sum_nonpos fun candidate _ => hallZero candidate)
        htotalNonneg
    have htotal : (∑ candidate, occupation candidate) =
        quittingFiniteForcedOwnerBestRectangleTotal
          reward profile terminal owner cutoff := by
      rw [quittingFiniteForcedOwnerBestRectangleTotal_eq_sum_passports]
      rw [Fintype.sum_prod_type]
    have hbad : 0 < ∑ candidate, occupation candidate := by
      rw [htotal]
      exact hpositive
    rw [htotalZero] at hbad
    exact (lt_irrefl 0) hbad
  refine ⟨label.1, label.2, hne, ?_⟩
  rw [quittingFiniteForcedOwnerBestRectangleTotal_eq_sum_passports]
  rw [Fintype.sum_prod_type] at hsumLe
  simpa only [occupation] using hsumLe

/-- **Finite-window strategic dispatch with a reset-ready square.**  The
raw same-witness rectangle alternative can be strengthened, at no extra
constant, to a fixed passport whose action is the forced-Quit best endpoint
on every charged row. -/
theorem exists_continueDeviation_or_fixedQuitAtom_or_fixedBestRectanglePassport
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (terminal : {S : Finset ι // S.Nonempty})
    (owner : ι) (howner : owner ∈ terminal.val) (cutoff : ℕ)
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
        quittingFiniteForcedOwnerBestRectanglePassport reward profile terminal
          owner who action cutoff) := by
  let actual := quittingFiniteActualDefectOccupation reward profile cutoff
  let continueCharge :=
    quittingFiniteActualContinueDefectOccupation reward profile cutoff
  let quit := quittingFiniteActualQuitDefectOccupation reward profile cutoff
  let rectangle := quittingFiniteForcedOwnerBestRectangleTotal reward profile
    terminal owner cutoff
  have hcurvature :=
    sum_stageCoalitionMass_mul_forcedOwnerDefect_half_le_actual_add_bestRectangle
      reward profile terminal owner howner cutoff
  have hlowerHalf : lower / 2 ≤ actual + rectangle :=
    (div_le_div_of_nonneg_right hcharge (by norm_num)).trans
      (by simpa only [actual, rectangle] using hcurvature)
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
  · have hquitRectangle : lower / 3 ≤ quit + rectangle := by linarith
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
    · have hrectangleLower : lower / 6 ≤ rectangle := by linarith
      have hrectanglePos : 0 < rectangle :=
        lt_of_lt_of_le (div_pos hlower (by norm_num)) hrectangleLower
      right; right
      obtain ⟨who, action, hwho, hfixed⟩ :=
        exists_fixed_forcedOwnerBestRectanglePassport reward profile terminal
          owner cutoff (by simpa only [rectangle] using hrectanglePos)
      exact ⟨who, action, hwho, hrectangleLower.trans hfixed⟩

/-- A positive passport has a literal charged row carrying both pieces of
provenance: best-endpoint equality on the forced-Quit face and positive
same-action rectangle curvature. -/
theorem exists_row_of_positive_forcedOwnerBestRectanglePassport
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (terminal : {S : Finset ι // S.Nonempty})
    (owner who : ι) (action : Bool) (cutoff : ℕ)
    (hpositive : 0 < quittingFiniteForcedOwnerBestRectanglePassport
      reward profile terminal owner who action cutoff) :
    ∃ time ∈ Finset.range cutoff,
      let root := quittingProfileLiveRoot reward profile time
      let tail := (quittingTerminalSemanticPair reward
        (quittingAllContinueProfileSpine reward profile (time + 1))).1
      who ≠ owner ∧
        quittingForcedOwnerBestEndpointAction reward tail root owner who =
          action ∧
        0 < quittingStageCoalitionMass reward profile time terminal *
          (root owner false).toReal *
            quittingOwnerOutsiderDeviationRectangle
              reward tail root owner who action := by
  classical
  unfold quittingFiniteForcedOwnerBestRectanglePassport at hpositive
  by_contra hnot
  push Not at hnot
  have hnonpos : (∑ time ∈ Finset.range cutoff,
      if who = owner then 0 else
        let root := quittingProfileLiveRoot reward profile time
        let tail := (quittingTerminalSemanticPair reward
          (quittingAllContinueProfileSpine reward profile (time + 1))).1
        if quittingForcedOwnerBestEndpointAction reward tail root owner who =
            action then
          quittingStageCoalitionMass reward profile time terminal *
            (root owner false).toReal *
              max (quittingForcedOwnerBestEndpointRectangle
                reward tail root owner who) 0
        else 0) ≤ 0 := by
    apply Finset.sum_nonpos
    intro time htime
    by_cases hwho : who = owner
    · simp [hwho]
    · simp only [if_neg hwho]
      let root := quittingProfileLiveRoot reward profile time
      let tail := (quittingTerminalSemanticPair reward
        (quittingAllContinueProfileSpine reward profile (time + 1))).1
      change (if quittingForcedOwnerBestEndpointAction
          reward tail root owner who = action then
        quittingStageCoalitionMass reward profile time terminal *
          (root owner false).toReal *
            max (quittingForcedOwnerBestEndpointRectangle
              reward tail root owner who) 0
        else 0) ≤ 0
      by_cases haction : quittingForcedOwnerBestEndpointAction
          reward tail root owner who = action
      · simp only [haction, ↓reduceIte]
        have hrow : ¬ 0 <
            quittingStageCoalitionMass reward profile time terminal *
              (root owner false).toReal *
                quittingOwnerOutsiderDeviationRectangle
                  reward tail root owner who action := by
          intro hrow
          exact hnot time htime ⟨hwho, haction, hrow⟩
        rw [quittingForcedOwnerBestEndpointRectangle, haction]
        by_cases hrect : quittingOwnerOutsiderDeviationRectangle
            reward tail root owner who action ≤ 0
        · rw [max_eq_right hrect]
          norm_num
        · rw [max_eq_left (le_of_not_ge hrect)]
          exact le_of_not_gt hrow
      · simp [haction]
  linarith

end GameTheory
