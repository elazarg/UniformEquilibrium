/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticForcedOwnerRefusalCollector
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticForcedOwnerWallRectangleCurvature

/-!
# Observer-absent clocks: legal deviation, actual defect, or square curvature

The landed forced-owner collector removes owner refusal from a finite
observer-absent clock: either one legal owner strategy is profitable, or the
clock carries aggregate forced-owner outsider defect.  The affine two-face
identity then localizes the latter, on the same actual rows, into ordinary
live Nash-defect occupation plus positive owner/outsider Boolean squares.

This file composes those statements without choosing a row, outsider, or
endpoint.  The result is an exhaustive strategic trichotomy.  It does not
claim that positive square charges at different times share a common label,
table slot, or compatible reset chronology.
-/

noncomputable section

namespace GameTheory

open StochasticGame Math.Probability Math.PMFProduct

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Actual live root Nash-defect occupation over a finite clock. -/
def quittingFiniteClockActualDefectOccupation
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (stop : ℕ) : ℝ :=
  ∑ time ∈ Finset.range stop,
    quittingLiveMass reward profile time *
      quittingSpineTotalNashDefect reward profile time

/-- Positive owner/outsider square charge over the same finite clock and
one marked terminal cylinder. -/
def quittingFiniteClockPositiveSquareCharge
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (terminal : {S : Finset ι // S.Nonempty})
    (owner : ι) (stop : ℕ) : ℝ :=
  ∑ time ∈ Finset.range stop,
    let root := quittingProfileLiveRoot reward profile time
    let tail := (quittingTerminalSemanticPair reward
      (quittingAllContinueProfileSpine reward profile (time + 1))).1
    let mass := quittingStageCoalitionMass reward profile time terminal
    ∑ who ∈ Finset.univ.erase owner, ∑ action,
      quittingPositiveOwnerOutsiderRectangleCharge
        reward tail root mass owner who action

theorem quittingFiniteClockActualDefectOccupation_nonneg
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (stop : ℕ) :
    0 ≤ quittingFiniteClockActualDefectOccupation reward profile stop := by
  unfold quittingFiniteClockActualDefectOccupation
  exact Finset.sum_nonneg fun time _ => mul_nonneg
    (quittingLiveMass_nonneg reward profile time)
    (quittingRootTotalNashDefect_nonneg reward _ _)

theorem quittingFiniteClockPositiveSquareCharge_nonneg
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (terminal : {S : Finset ι // S.Nonempty})
    (owner : ι) (stop : ℕ) :
    0 ≤ quittingFiniteClockPositiveSquareCharge
      reward profile terminal owner stop := by
  unfold quittingFiniteClockPositiveSquareCharge
  exact Finset.sum_nonneg fun time _ =>
    Finset.sum_nonneg fun who _ =>
      Finset.sum_nonneg fun action _ =>
        quittingPositiveOwnerOutsiderRectangleCharge_nonneg reward _ _ _
          owner who action

/-- Outsider-only strengthening of the witness-free row account.  Unlike a
sum over all player labels, this cannot be inflated by an inadmissible
owner-against-itself square. -/
theorem stageCoalitionMass_mul_forcedOwnerOutsiderDefect_le_actual_add_outsiderSquares
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (tail : Payoff ι) (time : ℕ) (owner : ι)
    (terminal : {S : Finset ι // S.Nonempty})
    (howner : owner ∈ terminal.val) :
    let root := quittingProfileLiveRoot reward profile time
    let mass := quittingStageCoalitionMass reward profile time terminal
    mass * quittingForcedOwnerOutsiderDefect reward
          (Function.update root owner (PMF.pure true)) owner / 2 ≤
      quittingLiveMass reward profile time *
          quittingRootTotalNashDefect reward tail root +
        ∑ who ∈ Finset.univ.erase owner, ∑ action,
          quittingPositiveOwnerOutsiderRectangleCharge
            reward tail root mass owner who action := by
  classical
  dsimp only
  let root := quittingProfileLiveRoot reward profile time
  let mass := quittingStageCoalitionMass reward profile time terminal
  let forcedRoot := Function.update root owner (PMF.pure true)
  let forcedDefect := quittingForcedOwnerOutsiderDefect reward forcedRoot owner
  change mass * forcedDefect / 2 ≤
    quittingLiveMass reward profile time *
        quittingRootTotalNashDefect reward tail root +
      ∑ who ∈ Finset.univ.erase owner, ∑ action,
        quittingPositiveOwnerOutsiderRectangleCharge
          reward tail root mass owner who action
  have hmass0 : 0 ≤ mass :=
    quittingStageCoalitionMass_nonneg reward profile time terminal
  have hlive0 : 0 ≤ quittingLiveMass reward profile time :=
    quittingLiveMass_nonneg reward profile time
  have htotal0 : 0 ≤ quittingRootTotalNashDefect reward tail root :=
    quittingRootTotalNashDefect_nonneg reward tail root
  have hsquares0 : 0 ≤ ∑ who ∈ Finset.univ.erase owner, ∑ action,
      quittingPositiveOwnerOutsiderRectangleCharge
        reward tail root mass owner who action := by
    exact Finset.sum_nonneg fun who _ =>
      Finset.sum_nonneg fun action _ =>
        quittingPositiveOwnerOutsiderRectangleCharge_nonneg
          reward tail root mass owner who action
  by_cases hpositive : 0 < forcedDefect
  · obtain ⟨who, hwho, hcoordinate⟩ :=
      exists_outsider_coordinateNashDefect_ge_of_forcedOwnerDefect_ge
        reward tail forcedRoot owner (by simp [forcedRoot]) hpositive le_rfl
    have hgap : mass * forcedDefect ≤ mass *
        quittingRootCoordinateNashDefect reward tail forcedRoot who :=
      mul_le_mul_of_nonneg_left hcoordinate hmass0
    obtain ⟨action, _hrealize, halt⟩ :=
      stageCoalitionMass_gap_actualDefect_or_rectangle reward profile tail
        time owner who hwho.symm terminal howner forcedDefect hgap
    rcases halt with hactual | hrectangle
    · have hcoordinateTotal :=
        quittingRootCoordinateNashDefect_le_total reward tail root who
      have hactualTotal :
          quittingLiveMass reward profile time *
              quittingRootCoordinateNashDefect reward tail root who ≤
            quittingLiveMass reward profile time *
              quittingRootTotalNashDefect reward tail root :=
        mul_le_mul_of_nonneg_left hcoordinateTotal hlive0
      exact hactual.trans <|
        hactualTotal.trans (le_add_of_nonneg_right hsquares0)
    · have hrectanglePositive : mass * (root owner false).toReal *
          (quittingRootDeviationGain reward tail forcedRoot who
              (PMF.pure action) -
            quittingRootDeviationGain reward tail
              (Function.update root owner (PMF.pure false)) who
              (PMF.pure action)) ≤
          quittingPositiveOwnerOutsiderRectangleCharge
            reward tail root mass owner who action := by
        unfold quittingPositiveOwnerOutsiderRectangleCharge
          quittingOwnerOutsiderDeviationRectangle
        exact le_max_right _ _
      have hactionLe :
          quittingPositiveOwnerOutsiderRectangleCharge
              reward tail root mass owner who action ≤
            ∑ endpoint,
              quittingPositiveOwnerOutsiderRectangleCharge
                reward tail root mass owner who endpoint :=
        Finset.single_le_sum
          (fun endpoint _ =>
            quittingPositiveOwnerOutsiderRectangleCharge_nonneg
              reward tail root mass owner who endpoint)
          (Finset.mem_univ action)
      have hwhoLe :
          (∑ endpoint,
              quittingPositiveOwnerOutsiderRectangleCharge
                reward tail root mass owner who endpoint) ≤
            ∑ player ∈ Finset.univ.erase owner, ∑ endpoint,
              quittingPositiveOwnerOutsiderRectangleCharge
                reward tail root mass owner player endpoint :=
        Finset.single_le_sum
          (fun player _ => Finset.sum_nonneg fun endpoint _ =>
            quittingPositiveOwnerOutsiderRectangleCharge_nonneg
              reward tail root mass owner player endpoint)
          (Finset.mem_erase.mpr ⟨hwho, Finset.mem_univ who⟩)
      have hrectangles := hrectangle.trans
        (hrectanglePositive.trans (hactionLe.trans hwhoLe))
      exact hrectangles.trans
        (le_add_of_nonneg_left (mul_nonneg hlive0 htotal0))
  · have hforced0 : 0 ≤ forcedDefect :=
      quittingForcedOwnerOutsiderDefect_nonneg reward forcedRoot owner
    have hforced : forcedDefect = 0 :=
      le_antisymm (le_of_not_gt hpositive) hforced0
    rw [hforced, mul_zero, zero_div]
    exact add_nonneg (mul_nonneg hlive0 htotal0) hsquares0

/-- Summing the witness-free row account costs no player-cardinality factor.
Half of the aggregate forced-owner outsider defect is paid by actual defect
occupation plus positive square charge. -/
theorem half_sum_forcedOwnerOutsiderDefect_le_actualOccupation_add_squares
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (terminal : {S : Finset ι // S.Nonempty})
    (owner : ι) (howner : owner ∈ terminal.val) (stop : ℕ) :
    (∑ time ∈ Finset.range stop,
        quittingStageCoalitionMass reward profile time terminal *
          quittingForcedOwnerOutsiderDefect reward
            (Function.update
              (quittingProfileLiveRoot reward profile time) owner
              (PMF.pure true)) owner) / 2 ≤
      quittingFiniteClockActualDefectOccupation reward profile stop +
        quittingFiniteClockPositiveSquareCharge
          reward profile terminal owner stop := by
  have hrows :
      (∑ time ∈ Finset.range stop,
        (quittingStageCoalitionMass reward profile time terminal *
          quittingForcedOwnerOutsiderDefect reward
            (Function.update
              (quittingProfileLiveRoot reward profile time) owner
              (PMF.pure true)) owner) / 2) ≤
        ∑ time ∈ Finset.range stop, (
          quittingLiveMass reward profile time *
              quittingSpineTotalNashDefect reward profile time +
            ∑ who ∈ Finset.univ.erase owner, ∑ action,
              quittingPositiveOwnerOutsiderRectangleCharge reward
                (quittingTerminalSemanticPair reward
                  (quittingAllContinueProfileSpine reward profile
                    (time + 1))).1
                (quittingProfileLiveRoot reward profile time)
                (quittingStageCoalitionMass reward profile time terminal)
                owner who action) := by
    exact Finset.sum_le_sum fun time htime =>
      stageCoalitionMass_mul_forcedOwnerOutsiderDefect_le_actual_add_outsiderSquares
        reward profile
        (quittingTerminalSemanticPair reward
          (quittingAllContinueProfileSpine reward profile (time + 1))).1
        time owner terminal howner
  unfold quittingFiniteClockActualDefectOccupation
    quittingFiniteClockPositiveSquareCharge
  rw [Finset.sum_add_distrib] at hrows
  simpa only [Finset.sum_div] using hrows

namespace QuittingStoppingLawVanishingDebtRectangleSequence

/-- Strong combined form of the finite-clock dispatch.  Before separating
actual defect from square curvature, the only quantitative loss is the two
halvings forced by the landed wall/refusal split and affine no-cancellation. -/
theorem observerAbsent_finiteClock_actualPlusSquare_or_deviation
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {regime : QuittingCounterexampleRegime reward}
    {frontier : QuittingCounterexampleStoppingLawFrontier regime}
    (packet : QuittingStoppingLawVanishingDebtRectangleSequence frontier)
    (habsent : packet.observer ∉ packet.terminal.val)
    (n stop : ℕ) (hstop : packet.quitTime n = some stop)
    (δ : ℝ) (hδ : 0 < δ) :
    let profile := quittingStoppingLawObserverAbsentCarrierProfile packet n
    let owner := quittingStoppingLawObserverAbsentOwner packet
    quittingStoppingLawObserverAbsentMassLower packet *
          regime.terminalGap / 4 ≤
        quittingFiniteClockActualDefectOccupation reward profile stop +
          quittingFiniteClockPositiveSquareCharge
            reward profile packet.terminal owner stop ∨
      ∃ deviation : (quittingGame reward).BehaviorStrategy owner,
        quittingStoppingLawObserverAbsentMassLower packet *
              regime.terminalGap / 2 - δ ≤
          quittingTerminalPayoff reward
              (Function.update profile owner deviation) owner -
            quittingTerminalPayoff reward profile owner := by
  classical
  dsimp only
  let profile := quittingStoppingLawObserverAbsentCarrierProfile packet n
  let owner := quittingStoppingLawObserverAbsentOwner packet
  let wall := quittingStoppingLawObserverAbsentMassLower packet *
    regime.terminalGap
  let outside := ∑ time ∈ Finset.range stop,
    quittingStageCoalitionMass reward profile time packet.terminal *
      quittingForcedOwnerOutsiderDefect reward
        (Function.update (quittingProfileLiveRoot reward profile time) owner
          (PMF.pure true)) owner
  let actual := quittingFiniteClockActualDefectOccupation
    reward profile stop
  let squares := quittingFiniteClockPositiveSquareCharge
    reward profile packet.terminal owner stop
  have hsplit := packet.observerAbsent_finiteClock_strategicSplit
    habsent n stop hstop δ hδ
  dsimp only at hsplit
  rcases hsplit with houtside | hdeviation
  · have howner : owner ∈ packet.terminal.val :=
      quittingStoppingLawObserverAbsentOwner_mem packet
    have haccount : outside / 2 ≤ actual + squares :=
      half_sum_forcedOwnerOutsiderDefect_le_actualOccupation_add_squares
        reward profile packet.terminal owner howner stop
    left
    have hhalf : wall / 4 ≤ outside / 2 := by
      dsimp only [wall]
      linarith
    exact hhalf.trans haccount
  · exact Or.inr hdeviation

/-- **Finite observer-absent strategic trichotomy.**  For every finite
clock ending at its declared stopping time, one of three things happens:

* actual live Nash-defect occupation pays one eighth of the wall;
* positive same-witness owner/outsider square curvature pays one eighth;
* one legal behavioral strategy of the fixed owner gains one half of the
  wall, up to the arbitrary approximation `δ`.

The first two constants arise by two honest binary splits. -/
theorem observerAbsent_finiteClock_actualDefect_or_square_or_deviation
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {regime : QuittingCounterexampleRegime reward}
    {frontier : QuittingCounterexampleStoppingLawFrontier regime}
    (packet : QuittingStoppingLawVanishingDebtRectangleSequence frontier)
    (habsent : packet.observer ∉ packet.terminal.val)
    (n stop : ℕ) (hstop : packet.quitTime n = some stop)
    (δ : ℝ) (hδ : 0 < δ) :
    let profile := quittingStoppingLawObserverAbsentCarrierProfile packet n
    let owner := quittingStoppingLawObserverAbsentOwner packet
    quittingStoppingLawObserverAbsentMassLower packet *
          regime.terminalGap / 8 ≤
        quittingFiniteClockActualDefectOccupation reward profile stop ∨
      quittingStoppingLawObserverAbsentMassLower packet *
          regime.terminalGap / 8 ≤
        quittingFiniteClockPositiveSquareCharge
          reward profile packet.terminal owner stop ∨
      ∃ deviation : (quittingGame reward).BehaviorStrategy owner,
        quittingStoppingLawObserverAbsentMassLower packet *
              regime.terminalGap / 2 - δ ≤
          quittingTerminalPayoff reward
              (Function.update profile owner deviation) owner -
            quittingTerminalPayoff reward profile owner := by
  classical
  dsimp only
  let profile := quittingStoppingLawObserverAbsentCarrierProfile packet n
  let owner := quittingStoppingLawObserverAbsentOwner packet
  let wall := quittingStoppingLawObserverAbsentMassLower packet *
    regime.terminalGap
  let outside := ∑ time ∈ Finset.range stop,
    quittingStageCoalitionMass reward profile time packet.terminal *
      quittingForcedOwnerOutsiderDefect reward
        (Function.update (quittingProfileLiveRoot reward profile time) owner
          (PMF.pure true)) owner
  let actual := quittingFiniteClockActualDefectOccupation
    reward profile stop
  let squares := quittingFiniteClockPositiveSquareCharge
    reward profile packet.terminal owner stop
  have hsplit := packet.observerAbsent_finiteClock_strategicSplit
    habsent n stop hstop δ hδ
  dsimp only at hsplit
  rcases hsplit with houtside | hdeviation
  · have howner : owner ∈ packet.terminal.val := by
      exact quittingStoppingLawObserverAbsentOwner_mem packet
    have haccount : outside / 2 ≤ actual + squares := by
      exact half_sum_forcedOwnerOutsiderDefect_le_actualOccupation_add_squares
        reward profile packet.terminal owner howner stop
    have hwall : wall / 4 ≤ actual + squares := by
      have := (div_le_div_of_nonneg_right houtside (by norm_num : (0 : ℝ) ≤ 2)).trans
        haccount
      dsimp only [wall] at this ⊢
      linarith
    by_cases hactual : wall / 8 ≤ actual
    · exact Or.inl hactual
    · right
      left
      linarith
  · exact Or.inr (Or.inr hdeviation)

end QuittingStoppingLawVanishingDebtRectangleSequence

end GameTheory
