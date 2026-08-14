/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Research.Quitting.CyclicKofNBellmanBridge
import Research.Quitting.StoppingLawRetentionChain

/-!
# Global retention cannot generate a rotating proper block orbit

The singleton no-go does not depend on the one-active cap.  At one fixed
chronological stage, global half-retention preserves any initially positive
singleton terminal atom through every reset.  Hence its owner has positive
Quit hazard at every profile in the chain.

But every proper translated block orbit contains a phase omitting any chosen
owner.  Therefore no globally retaining reset chain can have its fixed-time
live roots identified with one full translated common-hazard orbit of a
proper block, for any `K < N`.

The conclusion clarifies the construction boundary: cyclic rotation must
come from changing chronological slots, state matching, or a different
splicing mechanism.  It cannot arise from repeatedly resetting one retained
slot.
-/

namespace GameTheory

namespace CyclicKofNResetRetentionGeneralNoGo

open StochasticGame Math.Probability Math.PMFProduct
open CyclicKofNArithmetic CyclicKofNQuittingSchedule
  CyclicKofNBellmanBridge
open scoped Pointwise

noncomputable section

variable {G : Type} [AddGroup G] [Fintype G] [DecidableEq G]

/-- Every proper translated block orbit has a phase omitting any prescribed
player. -/
theorem exists_not_mem_cyclicSchedule_active
    (A : Finset G) (hproper : A ≠ Finset.univ) (player : G) :
    ∃ phase : Fin (Fintype.card (TranslationPhase A)),
      player ∉ (cyclicSchedule A).active phase.val := by
  have hmissing : ∃ missing : G, missing ∉ A := by
    by_contra hnone
    push Not at hnone
    exact hproper (Finset.eq_univ_iff_forall.mpr hnone)
  obtain ⟨missing, hmissingA⟩ := hmissing
  let block : TranslationPhase A :=
    ⟨(player - missing) +ᵥ A, ⟨player - missing, rfl⟩⟩
  have hplayer : player ∉ orbitSchedule A block := by
    change player ∉ (player - missing) +ᵥ A
    intro hmem
    have htranslated :
        (player - missing) + missing ∈ (player - missing) +ᵥ A := by
      simpa only [sub_add_cancel] using hmem
    exact hmissingA
      ((Finset.vadd_mem_vadd_finset_iff (s := A) (b := missing)
        (player - missing)).mp htranslated)
  obtain ⟨time, htime, hclock⟩ :=
    translationClock_surjective_period A block
  refine ⟨⟨time, htime⟩, ?_⟩
  rw [cyclicSchedule_active, hclock]
  exact hplayer

/-- **General retained-owner no-go.**  At a fixed chronological time, a
globally half-retaining reset chain starting with a positive singleton atom
cannot trace a full cyclic word of any proper translated block with positive
common hazard. -/
theorem not_forall_liveRoot_eq_cyclicPhaseRoots_of_proper_resetChain
    (reward : {S : Finset G // S.Nonempty} → Payoff G)
    (profiles : ℕ → (quittingGame reward).BehaviorProfile)
    (hstep : ∀ n, RetainsAllQuittingStageAtoms reward (1 / 2)
      (profiles n) (profiles (n + 1)))
    (time : ℕ) (owner : G)
    (hpositive : 0 < quittingStageCoalitionMass reward (profiles 0) time
      (quittingSingletonTerminal owner))
    (A : Finset G) (hproper : A ≠ Finset.univ)
    (β : ℝ) (hβpos : 0 < β) (hβlt : β < 1) :
    ¬ ∀ phase : Fin (Fintype.card (TranslationPhase A)),
      quittingProfileLiveRoot reward (profiles phase.val) time =
        cyclicPhaseRoots A β hβpos.le hβlt.le phase := by
  intro hidentify
  obtain ⟨phase, hownerInactive⟩ :=
    exists_not_mem_cyclicSchedule_active A hproper owner
  have hstagePositive := stageCoalitionMass_pos_of_resetChain
    reward profiles hstep 0 phase.val
      (quittingSingletonTerminal owner) time hpositive
  have hownerStage : owner ∈
      quittingPositiveSingletonStageSupport reward
        (profiles phase.val) time := by
    simpa [quittingPositiveSingletonStageSupport] using hstagePositive
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
  exact hownerInactive hownerHazard

/-- Cardinal version: any nonempty `K`-block in an `N`-player population
with `K < N` is proper, so the general no-go applies directly. -/
theorem not_forall_liveRoot_eq_cyclicPhaseRoots_of_card_lt
    (reward : {S : Finset G // S.Nonempty} → Payoff G)
    (profiles : ℕ → (quittingGame reward).BehaviorProfile)
    (hstep : ∀ n, RetainsAllQuittingStageAtoms reward (1 / 2)
      (profiles n) (profiles (n + 1)))
    (time : ℕ) (owner : G)
    (hpositive : 0 < quittingStageCoalitionMass reward (profiles 0) time
      (quittingSingletonTerminal owner))
    (A : Finset G) (hcard : A.card < Fintype.card G)
    (β : ℝ) (hβpos : 0 < β) (hβlt : β < 1) :
    ¬ ∀ phase : Fin (Fintype.card (TranslationPhase A)),
      quittingProfileLiveRoot reward (profiles phase.val) time =
        cyclicPhaseRoots A β hβpos.le hβlt.le phase := by
  have hproper : A ≠ Finset.univ := by
    intro hA
    rw [hA, Finset.card_univ] at hcard
    exact (Nat.lt_irrefl _ hcard)
  exact not_forall_liveRoot_eq_cyclicPhaseRoots_of_proper_resetChain
    reward profiles hstep time owner hpositive A hproper β hβpos hβlt

end

end CyclicKofNResetRetentionGeneralNoGo

end GameTheory
