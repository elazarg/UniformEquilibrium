/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegime.Seam
import Mathlib.Data.Fintype.Pigeonhole

/-!
# Canonically blocked periodic windows of a counterexample tail

Restart the length-`n+1` optimized-tail window beginning at date `n`, with
phase zero as the restart point.  Every such periodic profile is exposed by
the counterexample's full terminal gap.  Hence the resulting canonical
periodic family is payoff-blocked from its first member, at half that gap, by
one of the exact finite evaluator's two branches: refusal/`Never`, or one
concrete stop phase.

Finiteness then stabilizes the obstructing player and the evaluator branch
on an infinite set of windows.  This does not attach a periodic suffix to an
arbitrary earlier exact-D prefix.  It only classifies the obstruction inside
the compatible periodic-window grammar already realized by the evaluator.
-/

noncomputable section

namespace GameTheory

open Math.Probability

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
variable {witness : QuittingTerminalExploitabilityWitness reward}

namespace QuittingTerminalExploitabilityWitness

/-- Every periodic behavior profile is exposed by its exact finite periodic
best-response cap at the full terminal gap. -/
theorem exists_periodicCap_gain
    (witness : QuittingTerminalExploitabilityWitness reward)
    (profile : (quittingGame reward).BehaviorProfile)
    (period : ℕ) [NeZero period]
    (hperiodic : ∀ time,
      quittingProfileLiveRoot reward profile (time + period) =
        quittingProfileLiveRoot reward profile time) :
    ∃ who,
      quittingTerminalPayoff reward profile who + witness.terminalGap ≤
        quittingPeriodicWindowBestResponseValue reward
          (quittingProfileLiveRoot reward profile) who period := by
  obtain ⟨who, hgain⟩ := witness.exists_pureTimeCap_gap profile
  refine ⟨who, ?_⟩
  rw [← sSup_range_quittingTerminalPayoff_update_eq_periodicWindow
    reward profile who period hperiodic,
    sSup_range_quittingTerminalPayoff_update_eq_pureTime]
  exact hgain

end QuittingTerminalExploitabilityWitness

namespace QuittingCounterexampleDynamicTailWitness

variable (seam : QuittingCounterexampleDynamicTailWitness witness)

/-- The canonical increasing family: window `n` starts at tail date `n` and
contains `n+1` roots before periodic restart. -/
def canonicalPeriodicTailWindowFamily :
    QuittingPeriodicWindowFamily reward where
  roots window :=
    quittingCyclicRootSequence
      (quittingDynamicDebtTailWindowCycle seam.tail window window)
      (quittingPeriodicWindowInitialPhase window)
  periodIndex window := window
  delivery window :=
    quittingCyclicTerminalValue reward
      (quittingDynamicDebtTailWindowCycle seam.tail window window)
      (quittingPeriodicWindowInitialPhase window)
  periodic window time := by
    exact quittingCyclicRootSequence_add_period
      (quittingDynamicDebtTailWindowCycle seam.tail window window)
      (quittingPeriodicWindowInitialPhase window) time

/-- Every canonical restarted window has an exact refusal-or-phase
obstruction at half the counterexample margin. -/
theorem canonicalPeriodicTailWindow_escape (window : ℕ) :
    ∃ who,
      witness.terminalGap / 2 <
          quittingPeriodicWindowRefusalValue reward
            (seam.canonicalPeriodicTailWindowFamily.roots window) who -
            seam.canonicalPeriodicTailWindowFamily.delivery window who ∨
        ∃ phase : Fin (window + 1),
          witness.terminalGap / 2 <
            quittingPeriodicWindowPhaseStopValue reward
              (seam.canonicalPeriodicTailWindowFamily.roots window) who phase -
              seam.canonicalPeriodicTailWindowFamily.delivery window who := by
  obtain ⟨who, hgap⟩ := witness.exists_cyclicWindow_finiteEvaluation_gap
    seam.tail window window (quittingPeriodicWindowInitialPhase window)
  have hstrict : witness.terminalGap / 2 <
      quittingPeriodicWindowBestResponseValue reward
          (seam.canonicalPeriodicTailWindowFamily.roots window) who
            (window + 1) -
        seam.canonicalPeriodicTailWindowFamily.delivery window who := by
    change witness.terminalGap / 2 <
      quittingPeriodicWindowBestResponseValue reward
        (quittingCyclicRootSequence
          (quittingDynamicDebtTailWindowCycle seam.tail window window)
          (quittingPeriodicWindowInitialPhase window)) who (window + 1) -
      quittingCyclicTerminalValue reward
        (quittingDynamicDebtTailWindowCycle seam.tail window window)
        (quittingPeriodicWindowInitialPhase window) who
    linarith [witness.terminalGap_pos]
  exact ⟨who,
    (lt_quittingPeriodicWindowBestResponseValue_sub_iff reward
      (seam.canonicalPeriodicTailWindowFamily.roots window) who
        (window + 1)
        (seam.canonicalPeriodicTailWindowFamily.delivery window who)
        (witness.terminalGap / 2)).1 hstrict⟩

/-- The canonical family is payoff-blocked from its first window. -/
theorem canonicalPeriodicTailWindow_eventuallyPayoffBlocked :
    seam.canonicalPeriodicTailWindowFamily.EventuallyPayoffBlocked := by
  refine ⟨witness.terminalGap / 2, half_pos witness.terminalGap_pos,
    0, fun window _ ↦ ?_⟩
  exact seam.canonicalPeriodicTailWindow_escape window

/-- A choice of one exact finite obstruction for each canonical window. -/
structure CanonicalPeriodicTailWindowObstruction (window : ℕ) where
  who : ι
  escape :
    witness.terminalGap / 2 <
        quittingPeriodicWindowRefusalValue reward
          (seam.canonicalPeriodicTailWindowFamily.roots window) who -
          seam.canonicalPeriodicTailWindowFamily.delivery window who ∨
      ∃ phase : Fin (window + 1),
        witness.terminalGap / 2 <
          quittingPeriodicWindowPhaseStopValue reward
            (seam.canonicalPeriodicTailWindowFamily.roots window) who phase -
            seam.canonicalPeriodicTailWindowFamily.delivery window who

/-- Canonical choice of one player and one evaluator branch per window. -/
def canonicalPeriodicTailWindowObstruction (window : ℕ) :
    seam.CanonicalPeriodicTailWindowObstruction window :=
  Classical.choice (by
    obtain ⟨who, hescape⟩ := seam.canonicalPeriodicTailWindow_escape window
    exact ⟨⟨who, hescape⟩⟩)

/-- Boolean code for the selected branch: `true` means refusal and `false`
means a concrete phase stop. -/
def canonicalPeriodicTailWindowRefusalBranch (window : ℕ) : Bool :=
  if witness.terminalGap / 2 <
      quittingPeriodicWindowRefusalValue reward
        (seam.canonicalPeriodicTailWindowFamily.roots window)
        (seam.canonicalPeriodicTailWindowObstruction window).who -
        seam.canonicalPeriodicTailWindowFamily.delivery window
          (seam.canonicalPeriodicTailWindowObstruction window).who
  then true else false

/-- **Stabilized obstruction.**  Some fixed player is obstructed on
infinitely many canonical windows by one fixed evaluator branch: either
refusal throughout that infinite set, or a concrete (window-dependent) phase
stop throughout it. -/
theorem exists_infinite_fixedPlayer_fixedBranch :
    (∃ who, Set.Infinite {window : ℕ |
      witness.terminalGap / 2 <
        quittingPeriodicWindowRefusalValue reward
          (seam.canonicalPeriodicTailWindowFamily.roots window) who -
          seam.canonicalPeriodicTailWindowFamily.delivery window who}) ∨
    (∃ who, Set.Infinite {window : ℕ |
      ∃ phase : Fin (window + 1),
        witness.terminalGap / 2 <
          quittingPeriodicWindowPhaseStopValue reward
            (seam.canonicalPeriodicTailWindowFamily.roots window) who phase -
            seam.canonicalPeriodicTailWindowFamily.delivery window who}) := by
  let color : ℕ → ι × Bool := fun window ↦
    ((seam.canonicalPeriodicTailWindowObstruction window).who,
      seam.canonicalPeriodicTailWindowRefusalBranch window)
  obtain ⟨⟨who, branch⟩, hinfinite⟩ :=
    Finite.exists_infinite_fiber color
  cases branch with
  | false =>
      right
      refine ⟨who, (Set.infinite_coe_iff.1 hinfinite).mono ?_⟩
      intro window hwindow
      have hcolor : color window = (who, false) := by
        simpa only [Set.mem_preimage, Set.mem_singleton_iff] using hwindow
      have hwho :
          (seam.canonicalPeriodicTailWindowObstruction window).who = who :=
        congrArg Prod.fst hcolor
      have hbranch :
          seam.canonicalPeriodicTailWindowRefusalBranch window = false :=
        congrArg Prod.snd hcolor
      have hrefusalNot : ¬ witness.terminalGap / 2 <
          quittingPeriodicWindowRefusalValue reward
            (seam.canonicalPeriodicTailWindowFamily.roots window)
              (seam.canonicalPeriodicTailWindowObstruction window).who -
            seam.canonicalPeriodicTailWindowFamily.delivery window
              (seam.canonicalPeriodicTailWindowObstruction window).who := by
        unfold canonicalPeriodicTailWindowRefusalBranch at hbranch
        split at hbranch <;> simp_all
      rcases (seam.canonicalPeriodicTailWindowObstruction window).escape with
        hrefusal | hphase
      · exact (hrefusalNot hrefusal).elim
      · simpa [hwho] using hphase
  | true =>
      left
      refine ⟨who, (Set.infinite_coe_iff.1 hinfinite).mono ?_⟩
      intro window hwindow
      have hcolor : color window = (who, true) := by
        simpa only [Set.mem_preimage, Set.mem_singleton_iff] using hwindow
      have hwho :
          (seam.canonicalPeriodicTailWindowObstruction window).who = who :=
        congrArg Prod.fst hcolor
      have hbranch :
          seam.canonicalPeriodicTailWindowRefusalBranch window = true :=
        congrArg Prod.snd hcolor
      have hrefusal : witness.terminalGap / 2 <
          quittingPeriodicWindowRefusalValue reward
            (seam.canonicalPeriodicTailWindowFamily.roots window)
              (seam.canonicalPeriodicTailWindowObstruction window).who -
            seam.canonicalPeriodicTailWindowFamily.delivery window
              (seam.canonicalPeriodicTailWindowObstruction window).who := by
        unfold canonicalPeriodicTailWindowRefusalBranch at hbranch
        split at hbranch <;> simp_all
      simpa [hwho] using hrefusal

end QuittingCounterexampleDynamicTailWitness

end GameTheory
