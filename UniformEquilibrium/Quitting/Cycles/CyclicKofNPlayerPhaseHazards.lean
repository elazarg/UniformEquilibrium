/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import MathUE.Finset.ProdLtOne
import UniformEquilibrium.Quitting.Cycles.CyclicKofNBellmanBridge

/-!
# Player-and-phase hazards on cyclic `K/N` schedules

This is the fully heterogeneous finite parameterization of a fixed cyclic
support word: every player at every phase has its own hazard, while players
outside the scheduled block are forced to Continue.  Proper positive hazards
on scheduled players still imply automatic playerwise contraction.

As before, canonical infinite terminal evaluation solves every Bellman
policy equation.  The only payoff-dependent feasibility conditions left are
the finitely many exact root-Nash conditions.
-/

namespace GameTheory

namespace CyclicKofNPlayerPhaseHazards

open StochasticGame Math.Probability Math.PMFProduct
open Math.CyclicKofNArithmetic CyclicKofNQuittingSchedule
open CyclicKofNBellmanBridge
open scoped BigOperators Pointwise

noncomputable section

variable {G : Type} [AddGroup G] [Fintype G] [DecidableEq G]

/-- Independent player-and-phase hazards, restricted to the translated
active block at each phase. -/
def cyclicPlayerPhaseRoots
    (A : Finset G)
    (β : Fin (Fintype.card (TranslationPhase A)) → G → ℝ)
    (hβ0 : ∀ phase player,
      player ∈ (cyclicSchedule A).active phase.val → 0 ≤ β phase player)
    (hβ1 : ∀ phase player,
      player ∈ (cyclicSchedule A).active phase.val → β phase player ≤ 1) :
    Fin (Fintype.card (TranslationPhase A)) → G → PMF Bool :=
  fun phase player =>
    if hplayer : player ∈ (cyclicSchedule A).active phase.val then
      quittingHazardCoin (β phase player)
        (hβ0 phase player hplayer) (hβ1 phase player hplayer)
    else PMF.pure false

/-- Fixed-opponent survival factors over precisely the other scheduled
players, with heterogeneous factors. -/
theorem quittingStationaryFixedOpponentsContinueMass_playerPhase
    (A : Finset G)
    (β : Fin (Fintype.card (TranslationPhase A)) → G → ℝ)
    (hβ0 : ∀ phase player,
      player ∈ (cyclicSchedule A).active phase.val → 0 ≤ β phase player)
    (hβ1 : ∀ phase player,
      player ∈ (cyclicSchedule A).active phase.val → β phase player ≤ 1)
    (phase : Fin (Fintype.card (TranslationPhase A))) (who : G) :
    quittingStationaryFixedOpponentsContinueMass
        (cyclicPlayerPhaseRoots A β hβ0 hβ1 phase) who =
      ∏ player ∈ ((cyclicSchedule A).active phase.val).erase who,
        (1 - β phase player) := by
  classical
  unfold quittingStationaryFixedOpponentsContinueMass
    quittingFixedOpponentsContinueMass
  rw [quittingStationaryContinueMass_eq_prod_continueProbability]
  have hfactor : ∀ player : G,
      ((Function.update (cyclicPlayerPhaseRoots A β hβ0 hβ1 phase) who
          (PMF.pure false) player) false).toReal =
        if player ∈ ((cyclicSchedule A).active phase.val).erase who
          then 1 - β phase player else 1 := by
    intro player
    by_cases hplayer : player = who
    · subst player
      simp
    · by_cases hactive : player ∈ (cyclicSchedule A).active phase.val
      · have hactive' :
            player ∈ orbitSchedule A (translationClock A phase.val) := hactive
        simp [cyclicPlayerPhaseRoots, hplayer, hactive']
      · have hactive' :
            player ∉ orbitSchedule A (translationClock A phase.val) := hactive
        simp [cyclicPlayerPhaseRoots, hplayer, hactive']
  simp_rw [hfactor]
  rw [Finset.prod_ite]
  rw [Finset.prod_const_one, mul_one]
  apply Finset.prod_congr
  · ext player
    simp
  · intro player _
    rfl

/-- Heterogeneous positive hazards on scheduled players automatically satisfy
the periodic compiler's contraction condition, including sure-Quit hazards.
No positivity condition is imposed on inactive player-phase pairs. -/
theorem cyclicPlayerPhaseRoots_opponentContracts
    (A : Finset G) (hA : A.Nonempty) (hG : 1 < Fintype.card G)
    (β : Fin (Fintype.card (TranslationPhase A)) → G → ℝ)
    (hβ1 : ∀ phase player,
      player ∈ (cyclicSchedule A).active phase.val → β phase player ≤ 1)
    (hβpos : ∀ phase player,
      player ∈ (cyclicSchedule A).active phase.val → 0 < β phase player)
    (who : G) :
    (∏ phase : Fin (Fintype.card (TranslationPhase A)),
      quittingStationaryFixedOpponentsContinueMass
        (cyclicPlayerPhaseRoots A β
          (fun p player hplayer => (hβpos p player hplayer).le)
          hβ1 phase) who) < 1 := by
  let factor : Fin (Fintype.card (TranslationPhase A)) → ℝ :=
    fun phase => quittingStationaryFixedOpponentsContinueMass
      (cyclicPlayerPhaseRoots A β
        (fun p player hplayer => (hβpos p player hplayer).le)
        hβ1 phase) who
  have hnonnegative : ∀ phase ∈ Finset.univ, 0 ≤ factor phase := by
    intro phase _
    dsimp only [factor]
    rw [quittingStationaryFixedOpponentsContinueMass_playerPhase]
    apply Finset.prod_nonneg
    intro player hplayer
    exact sub_nonneg.mpr
      (hβ1 phase player (Finset.mem_of_mem_erase hplayer))
  have hle : ∀ phase ∈ Finset.univ, factor phase ≤ (1 : ℝ) := by
    intro phase _
    dsimp only [factor]
    rw [quittingStationaryFixedOpponentsContinueMass_playerPhase]
    apply Finset.prod_le_one
    · intro player hplayer
      exact sub_nonneg.mpr
        (hβ1 phase player (Finset.mem_of_mem_erase hplayer))
    · intro player hplayer
      linarith [hβpos phase player (Finset.mem_of_mem_erase hplayer)]
  obtain ⟨phase, opponent, hne, hactive⟩ :=
    exists_ne_mem_cyclicSchedule_active A hA hG who
  have hstrict : factor phase < 1 := by
    let opponents := ((cyclicSchedule A).active phase.val).erase who
    dsimp only [factor]
    rw [quittingStationaryFixedOpponentsContinueMass_playerPhase]
    exact Math.Finset.prod_lt_one_of_mem opponents
      (fun player => 1 - β phase player)
      opponent (Finset.mem_erase.mpr ⟨hne, hactive⟩)
      (fun player hplayer _ => sub_nonneg.mpr
        (hβ1 phase player (Finset.mem_of_mem_erase hplayer)))
      (fun player hplayer _ => by
        linarith [hβpos phase player (Finset.mem_of_mem_erase hplayer)])
      (sub_lt_self 1 (hβpos phase opponent hactive))
  exact Math.Finset.prod_lt_one_of_mem Finset.univ factor phase
    (Finset.mem_univ _)
    (fun other hother _ => hnonnegative other hother)
    (fun other hother _ => hle other hother) hstrict

/-- Canonical terminal values for heterogeneous cyclic hazards. -/
def cyclicPlayerPhaseTerminalValues
    (reward : {S : Finset G // S.Nonempty} → Payoff G)
    (A : Finset G)
    (β : Fin (Fintype.card (TranslationPhase A)) → G → ℝ)
    (hβ0 : ∀ phase player,
      player ∈ (cyclicSchedule A).active phase.val → 0 ≤ β phase player)
    (hβ1 : ∀ phase player,
      player ∈ (cyclicSchedule A).active phase.val → β phase player ≤ 1) :
    Fin (Fintype.card (TranslationPhase A)) → Payoff G :=
  quittingCyclicTerminalValue reward
    (cyclicPlayerPhaseRoots A β hβ0 hβ1)

/-- Finite exact Nash conditions for heterogeneous cyclic hazards. -/
def IsFinitePlayerPhaseNashCertificate
    (reward : {S : Finset G // S.Nonempty} → Payoff G)
    (A : Finset G)
    (β : Fin (Fintype.card (TranslationPhase A)) → G → ℝ)
    (hβ0 : ∀ phase player,
      player ∈ (cyclicSchedule A).active phase.val → 0 ≤ β phase player)
    (hβ1 : ∀ phase player,
      player ∈ (cyclicSchedule A).active phase.val → β phase player ≤ 1) : Prop :=
  ∀ phase,
    IsεQuittingRootNash reward
      (cyclicPlayerPhaseTerminalValues reward A β hβ0 hβ1
        (finRotate (Fintype.card (TranslationPhase A)) phase))
      0 (cyclicPlayerPhaseRoots A β hβ0 hβ1 phase)

/-- **Fully heterogeneous finite compiler.**  A finite collection of exact
root-Nash conditions, one per cyclic phase, produces the canonical terminal
value as a uniform-equilibrium payoff. -/
theorem isUniformEquilibriumPayoff_of_finitePlayerPhaseNashCertificate
    (reward : {S : Finset G // S.Nonempty} → Payoff G)
    (A : Finset G) (hA : A.Nonempty) (hG : 1 < Fintype.card G)
    (β : Fin (Fintype.card (TranslationPhase A)) → G → ℝ)
    (hβ1 : ∀ phase player,
      player ∈ (cyclicSchedule A).active phase.val → β phase player ≤ 1)
    (hβpos : ∀ phase player,
      player ∈ (cyclicSchedule A).active phase.val → 0 < β phase player)
    (hnash : IsFinitePlayerPhaseNashCertificate
      reward A β
        (fun phase player hplayer => (hβpos phase player hplayer).le)
        hβ1)
    (initial : Fin (Fintype.card (TranslationPhase A))) :
    (quittingGame reward).IsUniformEquilibriumPayoff none
      (cyclicPlayerPhaseTerminalValues reward A β
        (fun phase player hplayer => (hβpos phase player hplayer).le)
        hβ1 initial) := by
  apply isUniformEquilibriumPayoff_quittingCyclicTerminalValue_of_certificate
    reward
    (cyclicPlayerPhaseRoots A β
      (fun phase player hplayer => (hβpos phase player hplayer).le)
      hβ1)
    (cyclicPlayerPhaseTerminalValues reward A β
      (fun phase player hplayer => (hβpos phase player hplayer).le)
      hβ1)
    initial
  · intro phase
    exact quittingCyclicTerminalValue_eq_rootSuccessorPayoff
      reward (cyclicPlayerPhaseRoots A β
        (fun p player hplayer => (hβpos p player hplayer).le)
        hβ1) phase
  · exact hnash
  · intro who
    exact cyclicPlayerPhaseRoots_opponentContracts
      A hA hG β hβ1 hβpos who

end

end CyclicKofNPlayerPhaseHazards

end GameTheory
