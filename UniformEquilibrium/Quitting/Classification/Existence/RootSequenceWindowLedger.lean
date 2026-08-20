/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Classification.Existence.PureTimeDeviationLedger
import UniformEquilibrium.Quitting.Boundary.Repair.JointComplementarity

/-!
# Unrolled plan values and deviation ledgers over a window

The two stage-local recursions of the Solan–Vieille block analysis, summed
over a finite window with joint-survival weights:

* the plan's value over a window is the survival-weighted sum of the
  absorbing contributions plus the surviving continuation; and
* the gap between a pure-time deviation's value and the plan's value over a
  window is the survival-weighted sum of the own-quit-weighted edges over
  quitting now, plus the surviving end gap.

Both are exact identities; all bounding happens downstream.  The window sums
are indexed from the window's start with the front-recursive
`quittingJointSurvivalWeight`.
-/

noncomputable section

namespace GameTheory

open Math.Probability Math.PMFProduct

variable {ι : Type} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
/-- Peeling the first stage off a joint survival weight. -/
theorem quittingJointSurvivalWeight_succ_left
    (roots : ℕ → ι → PMF Bool) (start fuel : ℕ) :
    quittingJointSurvivalWeight roots start (fuel + 1) =
      quittingStationaryContinueMass (roots start) *
        quittingJointSurvivalWeight roots (start + 1) fuel :=
  rfl

/-! ## The plan's window unroll -/

omit [DecidableEq ι] in
/-- **The plan's value over a window.**  The plan's value at the window
start is the survival-weighted sum of the stagewise absorbing contributions
plus the survival through the window times the value at the window end. -/
theorem quittingRootSequenceTerminalValue_eq_window_sum
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι) :
    ∀ fuel start,
      quittingRootSequenceTerminalValue reward roots who start =
        (∑ offset ∈ Finset.range fuel,
          quittingJointSurvivalWeight roots start offset *
            quittingRootAbsorbingContribution reward (roots (start + offset))
              who) +
          quittingJointSurvivalWeight roots start fuel *
            quittingRootSequenceTerminalValue reward roots who
              (start + fuel) := by
  intro fuel
  induction fuel with
  | zero =>
      intro start
      simp
  | succ fuel ih =>
      intro start
      have hplan :=
        quittingRootSequenceTerminalValue_eq_absorbingContribution_add
          reward roots who start
      have hnext := ih (start + 1)
      have hpeel : ∀ f : ℕ → ℝ,
          ∑ offset ∈ Finset.range (fuel + 1), f offset =
            (∑ offset ∈ Finset.range fuel, f (offset + 1)) + f 0 :=
        fun f => Finset.sum_range_succ' f fuel
      rw [hpeel, hplan, hnext]
      have hshift : ∀ offset : ℕ,
          quittingJointSurvivalWeight roots start (offset + 1) *
              quittingRootAbsorbingContribution reward
                (roots (start + (offset + 1))) who =
            quittingStationaryContinueMass (roots start) *
              (quittingJointSurvivalWeight roots (start + 1) offset *
                quittingRootAbsorbingContribution reward
                  (roots (start + 1 + offset)) who) := by
        intro offset
        rw [quittingJointSurvivalWeight_succ_left,
          show start + (offset + 1) = start + 1 + offset from by omega]
        ring
      rw [Finset.sum_congr rfl fun offset _ => hshift offset,
        ← Finset.mul_sum, quittingJointSurvivalWeight_succ_left,
        show start + 1 + fuel = start + (fuel + 1) from by omega]
      have hzero : quittingJointSurvivalWeight roots start 0 = 1 :=
        quittingJointSurvivalWeight_zero_fuel roots start
      rw [hzero]
      simp only [Nat.add_zero]
      ring

/-! ## The deviation ledger's window unroll -/

/-- **The deviation gap over a window.**  Away from the deviation's quit
date, the gap between a pure-time deviation's value and the plan's value at
the window start is the survival-weighted sum of the own-quit-weighted edges
over quitting now, plus the survival through the window times the end
gap. -/
theorem quittingPureTimeDeviationLedger_window_sum
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι) (quitTime : Option ℕ) :
    ∀ fuel start,
      (∀ offset, offset < fuel → quitTime ≠ some (start + offset)) →
      quittingRootSequencePureTimeTerminalValue reward roots who quitTime
          start -
        quittingRootSequenceTerminalValue reward roots who start =
        (∑ offset ∈ Finset.range fuel,
          quittingJointSurvivalWeight roots start offset *
            ((roots (start + offset) who true).toReal *
              (quittingRootSequencePureTimeTerminalValue reward roots who
                  quitTime (start + offset) -
                quittingFixedOpponentsQuitValue reward roots who
                  (start + offset)))) +
          quittingJointSurvivalWeight roots start fuel *
            (quittingRootSequencePureTimeTerminalValue reward roots who
                quitTime (start + fuel) -
              quittingRootSequenceTerminalValue reward roots who
                (start + fuel)) := by
  intro fuel
  induction fuel with
  | zero =>
      intro start _
      simp
  | succ fuel ih =>
      intro start hne
      have hledger := quittingPureTimeDeviationLedger reward roots who
        quitTime start (by simpa using hne 0 (Nat.succ_pos fuel))
      have hnext := ih (start + 1) fun offset hoffset => by
        have := hne (offset + 1) (by omega)
        simpa [show start + (offset + 1) = start + 1 + offset from by omega]
          using this
      have hpeel : ∀ f : ℕ → ℝ,
          ∑ offset ∈ Finset.range (fuel + 1), f offset =
            (∑ offset ∈ Finset.range fuel, f (offset + 1)) + f 0 :=
        fun f => Finset.sum_range_succ' f fuel
      rw [hpeel, hledger, hnext]
      have hshift : ∀ offset : ℕ,
          quittingJointSurvivalWeight roots start (offset + 1) *
              ((roots (start + (offset + 1)) who true).toReal *
                (quittingRootSequencePureTimeTerminalValue reward roots who
                    quitTime (start + (offset + 1)) -
                  quittingFixedOpponentsQuitValue reward roots who
                    (start + (offset + 1)))) =
            quittingStationaryContinueMass (roots start) *
              (quittingJointSurvivalWeight roots (start + 1) offset *
                ((roots (start + 1 + offset) who true).toReal *
                  (quittingRootSequencePureTimeTerminalValue reward roots who
                      quitTime (start + 1 + offset) -
                    quittingFixedOpponentsQuitValue reward roots who
                      (start + 1 + offset)))) := by
        intro offset
        rw [quittingJointSurvivalWeight_succ_left,
          show start + (offset + 1) = start + 1 + offset from by omega]
        ring
      rw [Finset.sum_congr rfl fun offset _ => hshift offset,
        ← Finset.mul_sum, quittingJointSurvivalWeight_succ_left,
        show start + 1 + fuel = start + (fuel + 1) from by omega]
      have hzero : quittingJointSurvivalWeight roots start 0 = 1 :=
        quittingJointSurvivalWeight_zero_fuel roots start
      rw [hzero]
      simp only [Nat.add_zero]
      ring

end GameTheory
