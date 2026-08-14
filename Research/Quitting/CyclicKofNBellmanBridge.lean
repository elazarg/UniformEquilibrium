/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Research.Quitting.CyclicKofNQuittingSchedule
import UniformEquilibrium.Quitting.Cycles.PeriodicCompiler

/-!
# Exact Bellman closure for cyclic `K/N` schedules

The cyclic-support construction by itself is payoff-free.  This file records
the missing game-facing seam: once payoff states close around the finite
translation orbit and every phase is an exact one-stage Nash root, the
production periodic compiler controls arbitrary behavioral deviations.

The contraction hypothesis required by that compiler is not additional
payoff data here.  Positive common hazard and the occurrence of an active
opponent somewhere in the orbit force it automatically.
-/

namespace GameTheory

namespace CyclicKofNBellmanBridge

open StochasticGame Math.Probability Math.PMFProduct
open CyclicKofNArithmetic CyclicKofNQuittingSchedule
open scoped BigOperators Pointwise

noncomputable section

variable {G : Type} [AddGroup G] [Fintype G] [DecidableEq G]

/-- The finite root word underlying the natural-time cyclic schedule. -/
def cyclicPhaseRoots (A : Finset G) (β : ℝ)
    (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1) :
    Fin (Fintype.card (TranslationPhase A)) → G → PMF Bool :=
  fun phase => cyclicRoots A β hβ0 hβ1 phase.val

omit [AddGroup G] in
@[simp] theorem quittingStationaryFixedOpponentsContinueMass_uniformActiveRoot
    (active : Finset G) (β : ℝ) (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1)
    (who : G) :
    quittingStationaryFixedOpponentsContinueMass
        (uniformActiveRoot active β hβ0 hβ1) who =
      ∏ _player ∈ active.erase who, (1 - β) := by
  classical
  unfold quittingStationaryFixedOpponentsContinueMass
    quittingFixedOpponentsContinueMass
  rw [quittingStationaryContinueMass_eq_prod_continueProbability]
  have hfactor : ∀ player : G,
      ((Function.update (uniformActiveRoot active β hβ0 hβ1) who
          (PMF.pure false) player) false).toReal =
        if player ∈ active.erase who then 1 - β else 1 := by
    intro player
    by_cases hplayer : player = who
    · subst player
      simp
    · by_cases hactive : player ∈ active
      · simp [uniformActiveRoot, quittingActiveRoot, hplayer, hactive]
      · simp [uniformActiveRoot, quittingActiveRoot, hplayer, hactive]
  simp_rw [hfactor]
  rw [Finset.prod_ite]
  rw [Finset.prod_const_one, mul_one]
  apply Finset.prod_congr
  · ext player
    simp
  · intro player _
    rfl

/-- Every player occurs in some phase of a nonempty translated block. -/
theorem exists_mem_cyclicSchedule_active
    (A : Finset G) (hA : A.Nonempty) (player : G) :
    ∃ phase : Fin (Fintype.card (TranslationPhase A)),
      player ∈ (cyclicSchedule A).active phase.val := by
  obtain ⟨member, hmember⟩ := hA
  let block : TranslationPhase A :=
    ⟨(player - member) +ᵥ A, ⟨player - member, rfl⟩⟩
  have hplayer : player ∈ orbitSchedule A block := by
    change player ∈ (player - member) +ᵥ A
    have htranslated :=
      (Finset.vadd_mem_vadd_finset_iff (s := A) (b := member)
        (player - member)).2 hmember
    simpa only [vadd_eq_add, sub_add_cancel] using htranslated
  obtain ⟨time, htime, hclock⟩ := translationClock_surjective_period A block
  refine ⟨⟨time, htime⟩, ?_⟩
  rw [cyclicSchedule_active, hclock]
  exact hplayer

/-- If the population has at least two players, every player faces a
positive-hazard opponent somewhere in one turn of a nonempty cyclic block. -/
theorem exists_ne_mem_cyclicSchedule_active
    (A : Finset G) (hA : A.Nonempty) (hG : 1 < Fintype.card G)
    (who : G) :
    ∃ phase : Fin (Fintype.card (TranslationPhase A)),
      ∃ opponent ≠ who,
        opponent ∈ (cyclicSchedule A).active phase.val := by
  obtain ⟨opponent, hopponent⟩ := Fintype.exists_ne_of_one_lt_card hG who
  obtain ⟨phase, hphase⟩ := exists_mem_cyclicSchedule_active A hA opponent
  exact ⟨phase, opponent, hopponent, hphase⟩

/-- A phase containing an active opponent has strictly contracting
fixed-opponent Continue mass under a proper positive common hazard. -/
theorem quittingStationaryFixedOpponentsContinueMass_cyclicPhaseRoots_lt_one
    (A : Finset G) (β : ℝ) (hβpos : 0 < β) (hβlt : β < 1)
    (who : G) (phase : Fin (Fintype.card (TranslationPhase A)))
    (hopponent : ∃ opponent ≠ who,
      opponent ∈ (cyclicSchedule A).active phase.val) :
    quittingStationaryFixedOpponentsContinueMass
        (cyclicPhaseRoots A β hβpos.le hβlt.le phase) who < 1 := by
  obtain ⟨opponent, hne, hactive⟩ := hopponent
  have hcard : 0 < (((cyclicSchedule A).active phase.val).erase who).card :=
    Finset.card_pos.mpr ⟨opponent, Finset.mem_erase.mpr ⟨hne, hactive⟩⟩
  change quittingStationaryFixedOpponentsContinueMass
      (uniformActiveRoot ((cyclicSchedule A).active phase.val)
        β hβpos.le hβlt.le) who < 1
  rw [quittingStationaryFixedOpponentsContinueMass_uniformActiveRoot]
  simp only [Finset.prod_const]
  exact pow_lt_one₀ (by linarith) (by linarith) hcard.ne'

/-- The translated word automatically satisfies the production compiler's
playerwise contraction condition. -/
theorem cyclicPhaseRoots_opponentContracts
    (A : Finset G) (hA : A.Nonempty) (hG : 1 < Fintype.card G)
    (β : ℝ) (hβpos : 0 < β) (hβlt : β < 1) (who : G) :
    (∏ phase : Fin (Fintype.card (TranslationPhase A)),
      quittingStationaryFixedOpponentsContinueMass
        (cyclicPhaseRoots A β hβpos.le hβlt.le phase) who) < 1 := by
  let factor : Fin (Fintype.card (TranslationPhase A)) → ℝ :=
    fun phase => quittingStationaryFixedOpponentsContinueMass
      (cyclicPhaseRoots A β hβpos.le hβlt.le phase) who
  have hpositive : ∀ phase ∈ Finset.univ, 0 < factor phase := by
    intro phase _
    dsimp only [factor, cyclicPhaseRoots, cyclicRoots]
    rw [quittingStationaryFixedOpponentsContinueMass_uniformActiveRoot]
    simp only [Finset.prod_const]
    exact pow_pos (by linarith) _
  have hle : ∀ phase ∈ Finset.univ, factor phase ≤ (1 : ℝ) := by
    intro phase _
    dsimp only [factor, cyclicPhaseRoots, cyclicRoots]
    rw [quittingStationaryFixedOpponentsContinueMass_uniformActiveRoot]
    simp only [Finset.prod_const]
    exact pow_le_one₀ (by linarith) (by linarith)
  have hstrict : ∃ phase ∈ Finset.univ, factor phase < (1 : ℝ) := by
    obtain ⟨phase, opponent, hne, hactive⟩ :=
      exists_ne_mem_cyclicSchedule_active A hA hG who
    refine ⟨phase, Finset.mem_univ _, ?_⟩
    exact quittingStationaryFixedOpponentsContinueMass_cyclicPhaseRoots_lt_one
      A β hβpos hβlt who phase ⟨opponent, hne, hactive⟩
  have hproduct := Finset.prod_lt_prod hpositive hle hstrict
  simpa only [Finset.prod_const_one, Finset.card_univ, one_pow, factor]
    using hproduct

/-! ## State-matched Bellman closure -/

/-- **Cyclic `K/N` Bellman compiler.**  A finite word of exact
Nash--Bellman edges whose physical roots are the translated common-hazard
blocks delivers its initial Bellman value as a uniform-equilibrium payoff.

The hypotheses deliberately expose the two pieces absent from the bare
schedule: `hroot` is literal root provenance and `hedge` is payoff feasibility
with exact successor-state matching.  The conclusion invokes the production
periodic compiler, whose terminal-Nash proof ranges over arbitrary behavioral
deviations. -/
theorem isUniformEquilibriumPayoff_of_cyclicNashBellmanCycle
    (reward : {S : Finset G // S.Nonempty} → Payoff G)
    (A : Finset G) (hA : A.Nonempty) (hG : 1 < Fintype.card G)
    (β : ℝ) (hβpos : 0 < β) (hβlt : β < 1)
    (point : Fin (Fintype.card (TranslationPhase A)) →
      QuittingNashBellmanPoint G)
    (initial : Fin (Fintype.card (TranslationPhase A)))
    (hroot : ∀ phase, quittingRootOfSimplex (point phase).2 =
      cyclicPhaseRoots A β hβpos.le hβlt.le phase)
    (hedge : ∀ phase, IsQuittingNashBellmanEdge reward
      (point phase)
      (point (finRotate (Fintype.card (TranslationPhase A)) phase))) :
    (quittingGame reward).IsUniformEquilibriumPayoff none
      (point initial).1 := by
  let cycle := cyclicPhaseRoots A β hβpos.le hβlt.le
  let value : Fin (Fintype.card (TranslationPhase A)) → Payoff G :=
    fun phase => (point phase).1
  have hpolicy : ∀ phase,
      value phase = quittingRootSuccessorPayoff reward
        (value (finRotate (Fintype.card (TranslationPhase A)) phase))
        (cycle phase) := by
    intro phase
    have hstep := (hedge phase).1
    rw [hroot phase] at hstep
    exact hstep
  have hnash : ∀ phase,
      IsεQuittingRootNash reward
        (value (finRotate (Fintype.card (TranslationPhase A)) phase)) 0
        (cycle phase) := by
    intro phase
    apply (isZeroQuittingRootEndpointNash_iff_isZeroQuittingRootNash
      reward _ _).mp
    have hlocal := (hedge phase).2
    rw [hroot phase] at hlocal
    exact hlocal
  have hcontracts : ∀ who,
      (∏ phase : Fin (Fintype.card (TranslationPhase A)),
        quittingStationaryFixedOpponentsContinueMass
          (cycle phase) who) < 1 := by
    intro who
    exact cyclicPhaseRoots_opponentContracts
      A hA hG β hβpos hβlt who
  have huniform :=
    isUniformEquilibriumPayoff_quittingCyclicTerminalValue_of_certificate
      reward cycle value initial hpolicy hnash hcontracts
  have hvalue := eq_quittingCyclicTerminalValue_of_rootSuccessorPayoff
    reward cycle value hpolicy hcontracts
  have hinitial : quittingCyclicTerminalValue reward cycle initial =
      (point initial).1 := by
    exact (congrFun hvalue initial).symm
  rw [hinitial] at huniform
  exact huniform

end

end CyclicKofNBellmanBridge

end GameTheory
