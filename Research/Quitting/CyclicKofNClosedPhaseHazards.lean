/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Research.Quitting.CyclicKofNPhaseHazards

/-!
# Cyclic phase hazards with the sure-Quit boundary included

The open condition `β < 1` is stronger than periodic contraction needs.
Allowing `β = 1` is important: a sure-Quit opponent makes the relevant
survival factor zero and hence contracts maximally.

This file proves automatic contraction under `0 < β ≤ 1` and exports the
corresponding finite Nash-only compiler.
-/

namespace GameTheory

namespace CyclicKofNClosedPhaseHazards

open StochasticGame Math.Probability Math.PMFProduct
open CyclicKofNArithmetic CyclicKofNQuittingSchedule
open CyclicKofNBellmanBridge CyclicKofNPhaseHazards
open scoped BigOperators Pointwise

noncomputable section

variable {G : Type} [AddGroup G] [Fintype G] [DecidableEq G]

omit [AddGroup G] [Fintype G] in
/-- A product of heterogeneous factors in `[0,1]` is strictly below one as
soon as one displayed factor is strictly below one. -/
theorem prod_one_sub_lt_one_of_mem
    (s : Finset G) (β : G → ℝ)
    (hβ0 : ∀ player ∈ s, 0 ≤ β player)
    (hβ1 : ∀ player ∈ s, β player ≤ 1)
    (witness : G) (hwitness : witness ∈ s)
    (hpositive : 0 < β witness) :
    (∏ player ∈ s, (1 - β player)) < 1 := by
  let factor : G → ℝ := fun player => 1 - β player
  have hwitness0 : 0 ≤ factor witness := by
    dsimp only [factor]
    linarith [hβ1 witness hwitness]
  have hwitness1 : factor witness < 1 := by
    dsimp only [factor]
    linarith
  have hrest0 : 0 ≤ ∏ player ∈ s.erase witness, factor player := by
    apply Finset.prod_nonneg
    intro player hplayer
    dsimp only [factor]
    exact sub_nonneg.mpr
      (hβ1 player (Finset.mem_of_mem_erase hplayer))
  have hrest1 : (∏ player ∈ s.erase witness, factor player) ≤ 1 := by
    apply Finset.prod_le_one
    · intro player hplayer
      dsimp only [factor]
      exact sub_nonneg.mpr
        (hβ1 player (Finset.mem_of_mem_erase hplayer))
    · intro player hplayer
      dsimp only [factor]
      linarith [hβ0 player (Finset.mem_of_mem_erase hplayer)]
  have hmul : factor witness *
      (∏ player ∈ s.erase witness, factor player) < 1 := by
    calc
      factor witness * (∏ player ∈ s.erase witness, factor player) ≤
          factor witness * 1 :=
        mul_le_mul_of_nonneg_left hrest1 hwitness0
      _ < 1 := by simpa using hwitness1
  have hsplit := Finset.mul_prod_erase s factor hwitness
  simpa only [factor] using hsplit.symm ▸ hmul

/-- Automatic playerwise contraction with the sure-Quit boundary allowed. -/
theorem cyclicPhaseHazardRoots_opponentContracts_closed
    (A : Finset G) (hA : A.Nonempty) (hG : 1 < Fintype.card G)
    (β : Fin (Fintype.card (TranslationPhase A)) → ℝ)
    (hβpos : ∀ phase, 0 < β phase)
    (hβ1 : ∀ phase, β phase ≤ 1) (who : G) :
    (∏ phase : Fin (Fintype.card (TranslationPhase A)),
      quittingStationaryFixedOpponentsContinueMass
        (cyclicPhaseHazardRoots A β
          (fun phase => (hβpos phase).le) hβ1 phase) who) < 1 := by
  let factor : Fin (Fintype.card (TranslationPhase A)) → ℝ :=
    fun phase => quittingStationaryFixedOpponentsContinueMass
      (cyclicPhaseHazardRoots A β
        (fun p => (hβpos p).le) hβ1 phase) who
  have hfactor0 : ∀ phase ∈ Finset.univ, 0 ≤ factor phase := by
    intro phase _
    dsimp only [factor]
    rw [quittingStationaryFixedOpponentsContinueMass_phaseHazard]
    apply Finset.prod_nonneg
    intro player _
    exact sub_nonneg.mpr (hβ1 phase)
  have hfactor1 : ∀ phase ∈ Finset.univ, factor phase ≤ (1 : ℝ) := by
    intro phase _
    dsimp only [factor]
    rw [quittingStationaryFixedOpponentsContinueMass_phaseHazard]
    apply Finset.prod_le_one
    · intro player _
      exact sub_nonneg.mpr (hβ1 phase)
    · intro player _
      linarith [hβpos phase]
  obtain ⟨strictPhase, opponent, hne, hactive⟩ :=
    exists_ne_mem_cyclicSchedule_active A hA hG who
  have hopponent : opponent ∈
      ((cyclicSchedule A).active strictPhase.val).erase who :=
    Finset.mem_erase.mpr ⟨hne, hactive⟩
  have hstrict : factor strictPhase < 1 := by
    dsimp only [factor]
    rw [quittingStationaryFixedOpponentsContinueMass_phaseHazard]
    exact prod_one_sub_lt_one_of_mem
      (((cyclicSchedule A).active strictPhase.val).erase who)
      (fun _player => β strictPhase)
      (fun _ _ => (hβpos strictPhase).le)
      (fun _ _ => hβ1 strictPhase)
      opponent hopponent (hβpos strictPhase)
  have hstrictMem : strictPhase ∈
      (Finset.univ : Finset (Fin (Fintype.card (TranslationPhase A)))) :=
    Finset.mem_univ _
  have hrest0 : 0 ≤ ∏ phase ∈
      (Finset.univ.erase strictPhase), factor phase := by
    apply Finset.prod_nonneg
    intro phase hphase
    exact hfactor0 phase (Finset.mem_univ _)
  have hrest1 : (∏ phase ∈
      (Finset.univ.erase strictPhase), factor phase) ≤ 1 := by
    apply Finset.prod_le_one
    · intro phase hphase
      exact hfactor0 phase (Finset.mem_univ _)
    · intro phase hphase
      exact hfactor1 phase (Finset.mem_univ _)
  have hmul : factor strictPhase *
      (∏ phase ∈ Finset.univ.erase strictPhase, factor phase) < 1 := by
    calc
      factor strictPhase *
          (∏ phase ∈ Finset.univ.erase strictPhase, factor phase) ≤
        factor strictPhase * 1 :=
          mul_le_mul_of_nonneg_left hrest1
            (hfactor0 strictPhase hstrictMem)
      _ < 1 := by simpa using hstrict
  have hsplit := Finset.mul_prod_erase Finset.univ factor hstrictMem
  simpa only [factor] using hsplit.symm ▸ hmul

/-- **Closed-boundary phase-hazard compiler.**  Exact phasewise Nash plus
`0 < β ≤ 1` produces the canonical cyclic uniform-equilibrium payoff. -/
theorem isUniformEquilibriumPayoff_of_finitePhaseHazardNashCertificate_closed
    (reward : {S : Finset G // S.Nonempty} → Payoff G)
    (A : Finset G) (hA : A.Nonempty) (hG : 1 < Fintype.card G)
    (β : Fin (Fintype.card (TranslationPhase A)) → ℝ)
    (hβpos : ∀ phase, 0 < β phase)
    (hβ1 : ∀ phase, β phase ≤ 1)
    (hnash : IsFinitePhaseHazardNashCertificate reward A β
      (fun phase => (hβpos phase).le) hβ1)
    (initial : Fin (Fintype.card (TranslationPhase A))) :
    (quittingGame reward).IsUniformEquilibriumPayoff none
      (cyclicPhaseHazardTerminalValues reward A β
        (fun phase => (hβpos phase).le) hβ1 initial) := by
  apply isUniformEquilibriumPayoff_quittingCyclicTerminalValue_of_certificate
    reward
    (cyclicPhaseHazardRoots A β
      (fun phase => (hβpos phase).le) hβ1)
    (cyclicPhaseHazardTerminalValues reward A β
      (fun phase => (hβpos phase).le) hβ1)
    initial
  · intro phase
    exact quittingCyclicTerminalValue_eq_rootSuccessorPayoff
      reward
        (cyclicPhaseHazardRoots A β
          (fun p => (hβpos p).le) hβ1) phase
  · exact hnash
  · intro who
    exact cyclicPhaseHazardRoots_opponentContracts_closed
      A hA hG β hβpos hβ1 who

end

end CyclicKofNClosedPhaseHazards

end GameTheory
