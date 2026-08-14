/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Research.Quitting.CyclicKofNBellmanBridge

/-!
# Phase-varying hazards on cyclic `K/N` schedules

The arithmetic schedule does not require one common hazard across its whole
orbit.  This file assigns an independent proper hazard to every phase.  The
canonical terminal-value construction still removes all Bellman state
variables, while automatic contraction uses only positivity and properness
of the finitely many phase hazards.
-/

namespace GameTheory

namespace CyclicKofNPhaseHazards

open StochasticGame Math.Probability Math.PMFProduct
open CyclicKofNArithmetic CyclicKofNQuittingSchedule
open CyclicKofNBellmanBridge
open scoped BigOperators Pointwise

noncomputable section

variable {G : Type} [AddGroup G] [Fintype G] [DecidableEq G]

/-- The translated block word with an independent common-on-the-block
hazard at each phase. -/
def cyclicPhaseHazardRoots
    (A : Finset G)
    (β : Fin (Fintype.card (TranslationPhase A)) → ℝ)
    (hβ0 : ∀ phase, 0 ≤ β phase)
    (hβ1 : ∀ phase, β phase ≤ 1) :
    Fin (Fintype.card (TranslationPhase A)) → G → PMF Bool :=
  fun phase => uniformActiveRoot ((cyclicSchedule A).active phase.val)
    (β phase) (hβ0 phase) (hβ1 phase)

/-- Fixed-opponent survival remains a product over the current block. -/
@[simp] theorem quittingStationaryFixedOpponentsContinueMass_phaseHazard
    (A : Finset G)
    (β : Fin (Fintype.card (TranslationPhase A)) → ℝ)
    (hβ0 : ∀ phase, 0 ≤ β phase)
    (hβ1 : ∀ phase, β phase ≤ 1)
    (phase : Fin (Fintype.card (TranslationPhase A))) (who : G) :
    quittingStationaryFixedOpponentsContinueMass
        (cyclicPhaseHazardRoots A β hβ0 hβ1 phase) who =
      ∏ _player ∈ ((cyclicSchedule A).active phase.val).erase who,
        (1 - β phase) := by
  unfold cyclicPhaseHazardRoots
  exact quittingStationaryFixedOpponentsContinueMass_uniformActiveRoot
    ((cyclicSchedule A).active phase.val) (β phase)
      (hβ0 phase) (hβ1 phase) who

/-- Proper positive phase hazards automatically contract every player's
opponent-survival product over one translation orbit. -/
theorem cyclicPhaseHazardRoots_opponentContracts
    (A : Finset G) (hA : A.Nonempty) (hG : 1 < Fintype.card G)
    (β : Fin (Fintype.card (TranslationPhase A)) → ℝ)
    (hβpos : ∀ phase, 0 < β phase)
    (hβlt : ∀ phase, β phase < 1) (who : G) :
    (∏ phase : Fin (Fintype.card (TranslationPhase A)),
      quittingStationaryFixedOpponentsContinueMass
        (cyclicPhaseHazardRoots A β
          (fun phase => (hβpos phase).le)
          (fun phase => (hβlt phase).le) phase) who) < 1 := by
  let factor : Fin (Fintype.card (TranslationPhase A)) → ℝ :=
    fun phase => quittingStationaryFixedOpponentsContinueMass
      (cyclicPhaseHazardRoots A β
        (fun p => (hβpos p).le) (fun p => (hβlt p).le) phase) who
  have hpositive : ∀ phase ∈ Finset.univ, 0 < factor phase := by
    intro phase _
    dsimp only [factor]
    rw [quittingStationaryFixedOpponentsContinueMass_phaseHazard]
    simp only [Finset.prod_const]
    exact pow_pos (by linarith [hβlt phase]) _
  have hle : ∀ phase ∈ Finset.univ, factor phase ≤ (1 : ℝ) := by
    intro phase _
    dsimp only [factor]
    rw [quittingStationaryFixedOpponentsContinueMass_phaseHazard]
    simp only [Finset.prod_const]
    exact pow_le_one₀ (by linarith [hβlt phase])
      (by linarith [hβpos phase])
  have hstrict : ∃ phase ∈ Finset.univ, factor phase < (1 : ℝ) := by
    obtain ⟨phase, opponent, hne, hactive⟩ :=
      exists_ne_mem_cyclicSchedule_active A hA hG who
    have hcard :
        0 < (((cyclicSchedule A).active phase.val).erase who).card :=
      Finset.card_pos.mpr
        ⟨opponent, Finset.mem_erase.mpr ⟨hne, hactive⟩⟩
    refine ⟨phase, Finset.mem_univ _, ?_⟩
    dsimp only [factor]
    rw [quittingStationaryFixedOpponentsContinueMass_phaseHazard]
    simp only [Finset.prod_const]
    exact pow_lt_one₀ (by linarith [hβlt phase])
      (by linarith [hβpos phase]) hcard.ne'
  have hproduct := Finset.prod_lt_prod hpositive hle hstrict
  simpa only [Finset.prod_const_one, Finset.card_univ, one_pow, factor]
    using hproduct

/-- Canonical terminal values for the phase-varying root word. -/
def cyclicPhaseHazardTerminalValues
    (reward : {S : Finset G // S.Nonempty} → Payoff G)
    (A : Finset G)
    (β : Fin (Fintype.card (TranslationPhase A)) → ℝ)
    (hβ0 : ∀ phase, 0 ≤ β phase)
    (hβ1 : ∀ phase, β phase ≤ 1) :
    Fin (Fintype.card (TranslationPhase A)) → Payoff G :=
  quittingCyclicTerminalValue reward
    (cyclicPhaseHazardRoots A β hβ0 hβ1)

/-- The sole payoff-feasibility condition left after canonical policy
evaluation: exact Nash at each phase. -/
def IsFinitePhaseHazardNashCertificate
    (reward : {S : Finset G // S.Nonempty} → Payoff G)
    (A : Finset G)
    (β : Fin (Fintype.card (TranslationPhase A)) → ℝ)
    (hβ0 : ∀ phase, 0 ≤ β phase)
    (hβ1 : ∀ phase, β phase ≤ 1) : Prop :=
  ∀ phase,
    IsεQuittingRootNash reward
      (cyclicPhaseHazardTerminalValues reward A β hβ0 hβ1
        (finRotate (Fintype.card (TranslationPhase A)) phase))
      0 (cyclicPhaseHazardRoots A β hβ0 hβ1 phase)

/-- **Phase-hazard finite compiler.**  Independent phase hazards add finite
feasibility variables without reintroducing Bellman-state variables. -/
theorem isUniformEquilibriumPayoff_of_finitePhaseHazardNashCertificate
    (reward : {S : Finset G // S.Nonempty} → Payoff G)
    (A : Finset G) (hA : A.Nonempty) (hG : 1 < Fintype.card G)
    (β : Fin (Fintype.card (TranslationPhase A)) → ℝ)
    (hβpos : ∀ phase, 0 < β phase)
    (hβlt : ∀ phase, β phase < 1)
    (hnash : IsFinitePhaseHazardNashCertificate reward A β
      (fun phase => (hβpos phase).le)
      (fun phase => (hβlt phase).le))
    (initial : Fin (Fintype.card (TranslationPhase A))) :
    (quittingGame reward).IsUniformEquilibriumPayoff none
      (cyclicPhaseHazardTerminalValues reward A β
        (fun phase => (hβpos phase).le)
        (fun phase => (hβlt phase).le) initial) := by
  apply isUniformEquilibriumPayoff_quittingCyclicTerminalValue_of_certificate
    reward
    (cyclicPhaseHazardRoots A β
      (fun phase => (hβpos phase).le)
      (fun phase => (hβlt phase).le))
    (cyclicPhaseHazardTerminalValues reward A β
      (fun phase => (hβpos phase).le)
      (fun phase => (hβlt phase).le))
    initial
  · intro phase
    exact quittingCyclicTerminalValue_eq_rootSuccessorPayoff
      reward
        (cyclicPhaseHazardRoots A β
          (fun p => (hβpos p).le)
          (fun p => (hβlt p).le)) phase
  · exact hnash
  · intro who
    exact cyclicPhaseHazardRoots_opponentContracts
      A hA hG β hβpos hβlt who

end

end CyclicKofNPhaseHazards

end GameTheory
