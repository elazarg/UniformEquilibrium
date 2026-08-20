/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Cycles.CyclicKofNPhaseHazards
import UniformEquilibrium.Quitting.Cycles.CyclicKofNFiniteNashCertificate

/-!
# Cofinite cyclic blocks and the `4/5` normal form

When `K = N - 1`, a `K`-block is uniquely the complement of one player.
Thus the translated-block schedule is exactly a missing-player clock.  Since
`N - 1` and `N` are coprime, the clock has all `N` phases and cannot collapse.

For `4/5`, this leaves five phases.  Under the phase-varying construction it
also leaves five hazard controls.  Full-game Nash tests can still see the
fifth-order term created by the unique inactive player's Quit deviation;
the literal four-movers-only rule stops at degree four.
-/

namespace GameTheory

namespace CyclicKofNCofiniteNormalForm

open StochasticGame Math.Probability Math.PMFProduct
open Math.CyclicKofNArithmetic CyclicKofNQuittingSchedule
open CyclicKofNBellmanBridge CyclicKofNFiniteNashCertificate
open CyclicKofNPhaseHazards
open scoped BigOperators Pointwise

noncomputable section

/-- Every block of size `N - 1` has a unique missing player. -/
theorem existsUnique_missing_of_card_add_one_eq
    {Player : Type} [Fintype Player] [DecidableEq Player]
    (A : Finset Player) (hA : A.card + 1 = Fintype.card Player) :
    ∃! missing, A = Finset.univ.erase missing := by
  have hcomplCard : Aᶜ.card = 1 := by
    rw [Finset.card_compl]
    omega
  obtain ⟨missing, hmissing⟩ := Finset.card_eq_one.mp hcomplCard
  refine ⟨missing, ?_, ?_⟩
  · ext player
    have hplayer := Finset.ext_iff.mp hmissing player
    simp only [Finset.mem_compl, Finset.mem_singleton] at hplayer
    simp only [Finset.mem_erase, Finset.mem_univ, and_true]
    tauto
  · intro other hother
    have hnotmem : other ∉ A := by
      rw [hother]
      simp
    have hmem : other ∈ Aᶜ := Finset.mem_compl.mpr hnotmem
    rw [hmissing] at hmem
    simpa using hmem

variable {G : Type} [AddGroup G] [Fintype G] [DecidableEq G]

/-- Every phase of a translated co-singleton block has a unique missing
player. -/
theorem translationPhase_existsUnique_missing
    (A : Finset G) (hA : A.card + 1 = Fintype.card G)
    (phase : TranslationPhase A) :
    ∃! missing, orbitSchedule A phase = Finset.univ.erase missing := by
  apply existsUnique_missing_of_card_add_one_eq
  change phaseLoad (orbitSchedule A) phase + 1 = Fintype.card G
  rw [orbitSchedule_phaseLoad]
  exact hA

/-- Natural-time version: a co-singleton cyclic schedule is literally a
missing-player clock. -/
theorem cyclicSchedule_existsUnique_missing
    (A : Finset G) (hA : A.card + 1 = Fintype.card G) (time : ℕ) :
    ∃! missing,
      (cyclicSchedule A).active time = Finset.univ.erase missing := by
  simpa [cyclicSchedule_active] using
    translationPhase_existsUnique_missing A hA (translationClock A time)

/-- The missing-player clock has one phase per player; no arithmetic collapse
is possible for any `(N-1)/N` block. -/
theorem cofinite_cyclicSchedule_period_eq_population
    (A : Finset G) (hA : A.card + 1 = Fintype.card G) :
    Fintype.card (TranslationPhase A) = Fintype.card G :=
  card_translationPhase_eq_card_of_cosingleton A hA

/-! ## The `4/5` specialization -/

/-- A `4/5` schedule has five distinct phases. -/
theorem fourOfFive_period_eq_five
    (A : Finset G) (hA : A.card = 4) (hG : Fintype.card G = 5) :
    Fintype.card (TranslationPhase A) = 5 := by
  have hcoprime : Nat.Coprime A.card (Fintype.card G) := by
    rw [hA, hG]
    decide
  simpa [hG] using card_translationPhase_eq_card_of_coprime A hcoprime

/-- At each `4/5` phase exactly one player is missing, uniquely. -/
theorem fourOfFive_existsUnique_missing
    (A : Finset G) (hA : A.card = 4) (hG : Fintype.card G = 5)
    (phase : Fin (Fintype.card (TranslationPhase A))) :
    ∃! missing,
      (cyclicSchedule A).active phase.val = Finset.univ.erase missing := by
  apply cyclicSchedule_existsUnique_missing A
  omega

/-- The phase-hazard parameter type in `4/5` has exactly five elements. -/
theorem fourOfFive_phaseHazardParameterCount
    (A : Finset G) (hA : A.card = 4) (hG : Fintype.card G = 5) :
    Fintype.card (Fin (Fintype.card (TranslationPhase A))) = 5 := by
  simp [fourOfFive_period_eq_five A hA hG]

/-- Concrete `4/5` finite compiler with one positive hazard per missing-player
phase, including sure Quit. The only game-specific assumption is the
five-phase exact Nash certificate. -/
theorem fourOfFive_isUniformEquilibriumPayoff_of_phaseHazardCertificate
    (reward : {S : Finset G // S.Nonempty} → Payoff G)
    (A : Finset G) (hA : A.card = 4) (hG : Fintype.card G = 5)
    (β : Fin (Fintype.card (TranslationPhase A)) → ℝ)
    (hβpos : ∀ phase, 0 < β phase)
    (hβ1 : ∀ phase, β phase ≤ 1)
    (hnash : IsFinitePhaseHazardNashCertificate reward A β
      (fun phase => (hβpos phase).le) hβ1)
    (initial : Fin (Fintype.card (TranslationPhase A))) :
    (quittingGame reward).IsUniformEquilibriumPayoff none
      (cyclicPhaseHazardTerminalValues reward A β
        (fun phase => (hβpos phase).le) hβ1 initial) := by
  have hApos : 0 < A.card := by omega
  have hAnonempty : A.Nonempty := Finset.card_pos.mp hApos
  exact isUniformEquilibriumPayoff_of_finitePhaseHazardNashCertificate
    reward A hAnonempty (by omega) β hβpos hβ1 hnash initial

/-- For any constant-hazard four-active word, the full-game certificate is
exactly the endpoint-layer certificate with `K = 4`, hence with a possible
degree-five outside-entrant term. -/
theorem fourActive_fullCertificate_iff_endpointLayers
    (reward : {S : Finset G // S.Nonempty} → Payoff G)
    (A : Finset G) (hA : A.card = 4)
    (β : ℝ) (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1) :
    IsFiniteCyclicNashCertificate reward A β hβ0 hβ1 ↔
      ∀ phase who,
        ((cyclicPhaseRoots A β hβ0 hβ1 phase) who false).toReal *
            quittingActiveEndpointLayerDifference reward
              (cyclicTerminalValues reward A β hβ0 hβ1
                (finRotate (Fintype.card (TranslationPhase A)) phase))
              ((cyclicSchedule A).active phase.val)
              (cyclicPhaseRoots A β hβ0 hβ1 phase) 4 who ≤ 0 ∧
          -(0 : ℝ) ≤
            ((cyclicPhaseRoots A β hβ0 hβ1 phase) who true).toReal *
              quittingActiveEndpointLayerDifference reward
                (cyclicTerminalValues reward A β hβ0 hβ1
                  (finRotate (Fintype.card (TranslationPhase A)) phase))
                ((cyclicSchedule A).active phase.val)
                (cyclicPhaseRoots A β hβ0 hβ1 phase) 4 who := by
  rw [finiteCyclicNashCertificate_iff_endpointLayerCertificate]
  simp [IsFiniteCyclicEndpointLayerCertificate, hA]

/-- Under the literal four-movers-only rule, a four-active endpoint
certificate uses degree-four layers only. -/
theorem fourActive_restrictedCertificate_iff_degreeFourLayers
    (reward : {S : Finset G // S.Nonempty} → Payoff G)
    (A : Finset G) (hA : A.card = 4)
    (β : ℝ) (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1) :
    IsFiniteCyclicRestrictedEndpointCertificate reward A β hβ0 hβ1 ↔
      ∀ phase who,
        who ∈ (cyclicSchedule A).active phase.val →
          ((cyclicPhaseRoots A β hβ0 hβ1 phase) who false).toReal *
              quittingRestrictedActiveEndpointLayerDifference reward
                (cyclicTerminalValues reward A β hβ0 hβ1
                  (finRotate (Fintype.card (TranslationPhase A)) phase))
                ((cyclicSchedule A).active phase.val)
                (cyclicPhaseRoots A β hβ0 hβ1 phase) 4 who ≤ 0 ∧
            -(0 : ℝ) ≤
              ((cyclicPhaseRoots A β hβ0 hβ1 phase) who true).toReal *
                quittingRestrictedActiveEndpointLayerDifference reward
                  (cyclicTerminalValues reward A β hβ0 hβ1
                    (finRotate (Fintype.card (TranslationPhase A)) phase))
                  ((cyclicSchedule A).active phase.val)
                  (cyclicPhaseRoots A β hβ0 hβ1 phase) 4 who := by
  simpa [hA] using
    finiteCyclicRestrictedEndpointCertificate_iff_degreeKLayers
      reward A β hβ0 hβ1

end

end CyclicKofNCofiniteNormalForm

end GameTheory
