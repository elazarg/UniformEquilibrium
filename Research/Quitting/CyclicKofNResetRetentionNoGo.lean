/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Research.Quitting.CyclicKofNBellmanBridge
import Research.Quitting.StoppingLawRetentionChain

/-!
# Retained singleton atoms obstruct cyclic role rotation

The cyclic Bellman bridge requires literal identification of each phase root
with the corresponding translated block.  The existing global-retention
reset chain cannot supply that identification in the saturated one-active
regime.  A positive singleton atom is retained through every reset and the
one-active cap therefore locks its owner, whereas a nontrivial translated
singleton orbit necessarily activates a different player in some phase.

This is a game-facing obstruction: the retained object is a chronological
terminal atom of actual behavior profiles, not an abstract support label.
It rules out using the current retention theorem as a producer of the
`hroot` premise of `isUniformEquilibriumPayoff_of_cyclicNashBellmanCycle`.
-/

namespace GameTheory

namespace CyclicKofNResetRetentionNoGo

open StochasticGame Math.Probability Math.PMFProduct
open CyclicKofNArithmetic CyclicKofNQuittingSchedule
open CyclicKofNBellmanBridge

noncomputable section

variable {G : Type} [AddGroup G] [Fintype G] [DecidableEq G]

/-- **Retained-owner no-go for translated singleton cycles.**  A globally
half-retaining reset chain which stays one-active at a fixed chronological
stage and starts with a positive singleton atom cannot have its phase roots
identified with one full translated singleton word of proper positive
hazards when the population has at least two players. -/
theorem not_forall_liveRoot_eq_cyclicPhaseRoots_of_oneActive_resetChain
    (reward : {S : Finset G // S.Nonempty} → Payoff G)
    (profiles : ℕ → (quittingGame reward).BehaviorProfile)
    (hstep : ∀ n, RetainsAllQuittingStageAtoms reward (1 / 2)
      (profiles n) (profiles (n + 1)))
    (time : ℕ) (owner : G)
    (hpositive : 0 < quittingStageCoalitionMass reward (profiles 0) time
      (quittingSingletonTerminal owner))
    (hone : ∀ phase, HasQuittingSupportCardAtMost 1
      (quittingProfileLiveRoot reward (profiles phase) time))
    (A : Finset G) (hAcard : A.card = 1)
    (hG : 1 < Fintype.card G)
    (β : ℝ) (hβpos : 0 < β) (hβlt : β < 1) :
    ¬ ∀ phase : Fin (Fintype.card (TranslationPhase A)),
      quittingProfileLiveRoot reward (profiles phase.val) time =
        cyclicPhaseRoots A β hβpos.le hβlt.le phase := by
  intro hidentify
  have hA : A.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨phase, opponent, hopponentNe, hopponentActive⟩ :=
    exists_ne_mem_cyclicSchedule_active A hA hG owner
  have hlocked :=
    quittingPositiveSingletonStageSupport_eq_singleton_of_oneActive_resetChain
      reward profiles hstep time owner hpositive hone phase.val
  have hownerStage : owner ∈
      quittingPositiveSingletonStageSupport reward (profiles phase.val) time := by
    rw [hlocked]
    simp
  have hownerHazard : owner ∈ quittingPositiveHazardSupport
      (quittingProfileLiveRoot reward (profiles phase.val) time) :=
    quittingPositiveSingletonStageSupport_subset_positiveHazardSupport
      reward (profiles phase.val) time hownerStage
  rw [hidentify phase] at hownerHazard
  change owner ∈ quittingPositiveHazardSupport
      (cyclicRoots A β hβpos.le hβlt.le phase.val) at hownerHazard
  unfold cyclicRoots at hownerHazard
  rw [quittingPositiveHazardSupport_uniformActiveRoot
    _ β hβpos.le hβlt.le hβpos] at hownerHazard
  have hcard : ((cyclicSchedule A).active phase.val).card ≤ 1 := by
    rw [card_cyclicSchedule_active, hAcard]
  have heq : owner = opponent :=
    Finset.card_le_one.mp hcard owner hownerHazard opponent hopponentActive
  exact hopponentNe heq.symm

end

end CyclicKofNResetRetentionNoGo

end GameTheory
