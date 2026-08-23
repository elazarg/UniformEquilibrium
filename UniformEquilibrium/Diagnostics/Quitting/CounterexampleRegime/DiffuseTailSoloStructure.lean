/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegime.Conditioned.Diffuse.Closure
import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegime.PeriodicWindows
import UniformEquilibrium.Quitting.Cycles.DiffuseTailSoloStructure

/-!
# The canonical counterexample seam as an exact diffuse tail

`UniformEquilibrium/Quitting/Cycles/DiffuseTailSoloStructure.lean` formalizes
a coexistence obstruction for persistently active players in an *exact
diffuse tail*: a root sequence with an exact policy recursion, exact endpoint
Nash at accuracy zero, positive remaining eventual absorption, vanishing
conditioned mesh, and a boundary tight at every persistently active player.

The canonical counterexample seam of
`UniformEquilibrium/Diagnostics/Quitting/CounterexampleRegime/Seam.lean`,
read through the conditioning of
`UniformEquilibrium/Quitting/Cycles/PhantomBoundaryConditioning.lean`,
supplies exactly this data: its root sequence is
`quittingDynamicDebtTailRoots seam.tail`, its policy recursion and endpoint
Nash come from `seam.tail_edge`, and its boundary is `seam.limit.value`.
Active tightness — the boundary coordinate of a recurrently active player is
that player's singleton reward — is
`eventually_active_implies_limitValue_eq_singleton` at seam grade, recorded
here as `limitValue_eq_soloReward_of_persistentlyActive`.

The remaining declarations develop **T4(a)**, the phase-stop branch of the
seam's stabilized obstruction on canonical periodic windows solo at `owner`:

* `not_refusalObstruction_of_soloWindow`: on a window solo at `owner`, a
  coordinate other than `owner` already continues surely there, so its
  refusal reproduces the window's own delivery — no refusal obstruction.
* `soloWindows_ownerRefusal_or_phaseStop`: consequently the stabilized
  obstruction of `exists_infinite_fixedPlayer_fixedBranch` is either
  `owner`'s own refusal or some coordinate's phase stop.
* `soloWindows_negativeOwnerDelivery_or_phaseStop`: `owner`'s own refusal
  stops all absorption and pays zero
  (`quittingPeriodicWindowRefusalValue_eq_zero_of_soloRoots`), so its refusal
  obstruction is exactly a delivery below `-terminalGap / 2`.
* `exists_phaseStopObstruction_of_soloWindows`: if the canonical windows
  never deliver `owner` less than `-terminalGap / 2`, the stabilized
  obstruction is a phase stop.
* `QuittingSoloWindowPhaseStopBranch`: the T4(a) proposition, adding to the
  phase-stop conjunct above the preemption edge at the obstructing
  coordinate.
-/

noncomputable section

namespace GameTheory

namespace QuittingCounterexampleDynamicTailWitness

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
variable {regime : QuittingCounterexampleRegime reward}

/-- A persistently active player's seam boundary coordinate is its own
singleton reward.  This is the seam-grade active-tightness input used by T2
and T3, read off `eventually_active_implies_limitValue_eq_singleton`. -/
theorem limitValue_eq_soloReward_of_persistentlyActive
    (seam : QuittingCounterexampleDynamicTailWitness regime) (who : ι)
    (hactive : QuittingTailPersistentlyActive
      (quittingDynamicDebtTailRoots seam.tail) who) :
    seam.limit.value who = quittingSoloReward reward who who := by
  obtain ⟨start, hstart⟩ := Filter.eventually_atTop.1
    seam.eventually_active_implies_limitValue_eq_singleton
  obtain ⟨time, hle, hquit⟩ := hactive start
  have hnotPure :
      quittingDynamicDebtTailRoots seam.tail time who ≠ PMF.pure false := by
    intro hpure
    rw [hpure] at hquit
    simp at hquit
  simpa using hstart time hle who hnotPure

/-- **T4(a), refusal degeneracy.**  On a canonical periodic window whose every
root is solo at `owner`, no other coordinate has a refusal obstruction: it
already continues surely at every date of the window, so refusing to quit
reproduces the window's own delivery. -/
theorem not_refusalObstruction_of_soloWindow
    (seam : QuittingCounterexampleDynamicTailWitness regime) {window : ℕ}
    {owner who : ι} (hne : who ≠ owner)
    (hsolo : ∀ time, IsQuittingSoloRoot
      (seam.canonicalPeriodicTailWindowFamily.roots window time) owner) :
    ¬ regime.terminalGap / 2 <
        quittingPeriodicWindowRefusalValue reward
          (seam.canonicalPeriodicTailWindowFamily.roots window) who -
          seam.canonicalPeriodicTailWindowFamily.delivery window who := by
  have hpure : ∀ time,
      seam.canonicalPeriodicTailWindowFamily.roots window time who =
        PMF.pure false := fun time => hsolo time who hne
  have hrefusal := quittingPeriodicWindowRefusalValue_eq_of_continueSurely
    reward (seam.canonicalPeriodicTailWindowFamily.roots window) who hpure
  have hdelivery : seam.canonicalPeriodicTailWindowFamily.delivery window who =
      quittingRootSequenceTerminalValue reward
        (seam.canonicalPeriodicTailWindowFamily.roots window) who 0 := rfl
  rw [hrefusal, hdelivery, sub_self]
  exact not_lt.2 (by linarith [regime.terminalGap_pos])

/-- **T4(a), reduced to the owner's own refusal.**  On a seam whose canonical
periodic windows are solo at `owner`, the stabilized obstruction of
`exists_infinite_fixedPlayer_fixedBranch` is either `owner`'s own refusal or
some coordinate's phase stop: every other coordinate's refusal obstruction set
is empty. -/
theorem soloWindows_ownerRefusal_or_phaseStop
    (seam : QuittingCounterexampleDynamicTailWitness regime) (owner : ι)
    (hsolo : ∀ window time, IsQuittingSoloRoot
      (seam.canonicalPeriodicTailWindowFamily.roots window time) owner) :
    Set.Infinite {window : ℕ |
        regime.terminalGap / 2 <
          quittingPeriodicWindowRefusalValue reward
            (seam.canonicalPeriodicTailWindowFamily.roots window) owner -
            seam.canonicalPeriodicTailWindowFamily.delivery window owner} ∨
      (∃ other, Set.Infinite {window : ℕ |
        ∃ phase : Fin (window + 1),
          regime.terminalGap / 2 <
            quittingPeriodicWindowPhaseStopValue reward
              (seam.canonicalPeriodicTailWindowFamily.roots window) other
              phase -
              seam.canonicalPeriodicTailWindowFamily.delivery window
                other}) := by
  rcases seam.exists_infinite_fixedPlayer_fixedBranch with
    ⟨who, hinfinite⟩ | hphase
  · by_cases hwho : who = owner
    · subst who
      exact Or.inl hinfinite
    · obtain ⟨window, hwindow⟩ := hinfinite.nonempty
      exact absurd hwindow
        (seam.not_refusalObstruction_of_soloWindow hwho (hsolo window))
  · exact Or.inr hphase

/-- **T4(a), reduced to the owner's on-path delivery.**  On a seam whose
canonical periodic windows are solo at `owner`, the stabilized obstruction is
either an infinite family of windows whose delivery to `owner` falls below
`-terminalGap / 2`, or some coordinate's phase stop.  The owner's refusal
stops all absorption, so its refusal obstruction is exactly a negative
delivery. -/
theorem soloWindows_negativeOwnerDelivery_or_phaseStop
    (seam : QuittingCounterexampleDynamicTailWitness regime) (owner : ι)
    (hsolo : ∀ window time, IsQuittingSoloRoot
      (seam.canonicalPeriodicTailWindowFamily.roots window time) owner) :
    Set.Infinite {window : ℕ |
        seam.canonicalPeriodicTailWindowFamily.delivery window owner <
          -(regime.terminalGap / 2)} ∨
      (∃ other, Set.Infinite {window : ℕ |
        ∃ phase : Fin (window + 1),
          regime.terminalGap / 2 <
            quittingPeriodicWindowPhaseStopValue reward
              (seam.canonicalPeriodicTailWindowFamily.roots window) other
              phase -
              seam.canonicalPeriodicTailWindowFamily.delivery window
                other}) := by
  rcases seam.soloWindows_ownerRefusal_or_phaseStop owner hsolo with
    hrefusal | hphase
  · refine Or.inl (hrefusal.mono fun window hwindow => ?_)
    have hzero := quittingPeriodicWindowRefusalValue_eq_zero_of_soloRoots reward
      (seam.canonicalPeriodicTailWindowFamily.roots window) owner (hsolo window)
    simp only [Set.mem_setOf_eq, hzero] at hwindow ⊢
    linarith
  · exact Or.inr hphase

/-- **T4(a), phase-stop branch under a floored owner delivery.**  If the
canonical windows are solo at `owner` and never deliver `owner` less than
`-terminalGap / 2`, the stabilized obstruction is a phase stop. -/
theorem exists_phaseStopObstruction_of_soloWindows
    (seam : QuittingCounterexampleDynamicTailWitness regime) (owner : ι)
    (hsolo : ∀ window time, IsQuittingSoloRoot
      (seam.canonicalPeriodicTailWindowFamily.roots window time) owner)
    (hdelivery : ∀ window, -(regime.terminalGap / 2) ≤
      seam.canonicalPeriodicTailWindowFamily.delivery window owner) :
    ∃ other, Set.Infinite {window : ℕ |
      ∃ phase : Fin (window + 1),
        regime.terminalGap / 2 <
          quittingPeriodicWindowPhaseStopValue reward
            (seam.canonicalPeriodicTailWindowFamily.roots window) other phase -
            seam.canonicalPeriodicTailWindowFamily.delivery window other} := by
  rcases seam.soloWindows_negativeOwnerDelivery_or_phaseStop owner hsolo with
    hnegative | hphase
  · obtain ⟨window, hwindow⟩ := hnegative.nonempty
    exact absurd (hdelivery window) (not_le.2 hwindow)
  · exact hphase

/-- The phase-stop-branch proposition (T4(a)): on the canonical periodic
windows of a seam whose late roots are solo at `owner`, the stabilized
obstruction of `exists_infinite_fixedPlayer_fixedBranch` is the phase-stop
branch, and the obstructing player is a strict solo-preemption out-neighbour
of `owner`.

The phase-stop conjunct alone is the conclusion of
`exists_phaseStopObstruction_of_soloWindows`; what this proposition adds is
the preemption edge at the obstructing coordinate. -/
def QuittingSoloWindowPhaseStopBranch
    (seam : QuittingCounterexampleDynamicTailWitness regime) (owner : ι)
    (margin : ℝ) : Prop :=
  ∃ other, QuittingSoloPreempts reward margin owner other ∧
    Set.Infinite {window : ℕ |
      ∃ phase : Fin (window + 1),
        regime.terminalGap / 2 <
          quittingPeriodicWindowPhaseStopValue reward
            (seam.canonicalPeriodicTailWindowFamily.roots window) other phase -
            seam.canonicalPeriodicTailWindowFamily.delivery window other}

end QuittingCounterexampleDynamicTailWitness

end GameTheory
