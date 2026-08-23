/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Cycles.CyclicKofNPhaseHazards
import UniformEquilibrium.Diagnostics.Quitting.StoppingLaw.TerminalSemanticStoppingLawRetentionChain

/-!
# Supported-root obstruction for positive-retention reset chains

Stopping-law retention on the finite orbit prefix preserves one selected
initially positive singleton chronological atom. Therefore its owner keeps
positive Quit hazard at that fixed chronological time through every
represented phase.

This prevents a reset chain from tracing a full orbit of any proper
cyclic block.  No common-hazard assumption is needed: it is enough that each
candidate root be supported inside its scheduled active block.  In
particular, the obstruction applies to phase-varying hazards.
-/

namespace GameTheory

namespace CyclicKofNSupportedRootRetentionNoGo

open StochasticGame Math.Probability Math.PMFProduct
open Math.CyclicKofNArithmetic CyclicKofNQuittingSchedule
open CyclicKofNPhaseHazards
open scoped Pointwise

noncomputable section

variable {G : Type} [AddGroup G] [Fintype G] [DecidableEq G]

/-- **Supported-root retained-owner no-go.** At a fixed chronological time,
finite positive-factor retention of one positive singleton atom prevents a
reset chain from tracing a full orbit of roots supported by a proper rotating
block. -/
theorem not_forall_liveRoot_eq_supportedCyclicWord_of_proper_resetChain
    (reward : {S : Finset G // S.Nonempty} → Payoff G)
    (profiles : ℕ → (quittingGame reward).BehaviorProfile)
    (time : ℕ) (owner : G)
    (hpositive : 0 < quittingStageCoalitionMass reward (profiles 0) time
      (quittingSingletonTerminal owner))
    (A : Finset G) (factor : ℝ) (hfactor : 0 < factor)
    (hstep : RetainsQuittingStageAtomOnInterval reward factor
      profiles 0 (Fintype.card (TranslationPhase A) - 1)
        (quittingSingletonTerminal owner) time)
    (hproper : A ≠ Finset.univ)
    (roots : Fin (Fintype.card (TranslationPhase A)) → G → PMF Bool)
    (hsupport : ∀ phase,
      IsQuittingActiveRoot ((cyclicSchedule A).active phase.val)
        (roots phase)) :
    ¬ ∀ phase,
      quittingProfileLiveRoot reward (profiles phase.val) time = roots phase := by
  intro hidentify
  obtain ⟨phase, hownerInactive⟩ :=
    exists_not_mem_cyclicSchedule_active A hproper owner
  have hphaseRetention :=
    RetainsQuittingStageAtomOnInterval.mono_steps
      reward factor profiles 0 (quittingSingletonTerminal owner) time hstep
        (Nat.le_sub_one_of_lt phase.isLt)
  have hstagePositive := stageCoalitionMass_pos_of_resetChain
    reward profiles factor hfactor 0 phase.val
      (quittingSingletonTerminal owner) time hphaseRetention hpositive
  have hownerStage : owner ∈
      quittingPositiveSingletonStageSupport reward
        (profiles phase.val) time := by
    simpa [quittingPositiveSingletonStageSupport] using hstagePositive
  have hownerHazard : owner ∈ quittingPositiveHazardSupport
      (quittingProfileLiveRoot reward (profiles phase.val) time) :=
    quittingPositiveSingletonStageSupport_subset_positiveHazardSupport
      reward (profiles phase.val) time hownerStage
  rw [hidentify phase] at hownerHazard
  have hhazardPositive : 0 < hazardOfRoot (roots phase) owner := by
    simpa [quittingPositiveHazardSupport] using hownerHazard
  have hhazardZero : hazardOfRoot (roots phase) owner = 0 :=
    hazardOfRoot_eq_zero_of_isQuittingActiveRoot
      (hsupport phase) hownerInactive
  rw [hhazardZero] at hhazardPositive
  exact (lt_irrefl 0) hhazardPositive

/-- Cardinal form for any proper `K < N` block. -/
theorem not_forall_liveRoot_eq_supportedCyclicWord_of_card_lt
    (reward : {S : Finset G // S.Nonempty} → Payoff G)
    (profiles : ℕ → (quittingGame reward).BehaviorProfile)
    (time : ℕ) (owner : G)
    (hpositive : 0 < quittingStageCoalitionMass reward (profiles 0) time
      (quittingSingletonTerminal owner))
    (A : Finset G) (factor : ℝ) (hfactor : 0 < factor)
    (hstep : RetainsQuittingStageAtomOnInterval reward factor
      profiles 0 (Fintype.card (TranslationPhase A) - 1)
        (quittingSingletonTerminal owner) time)
    (hcard : A.card < Fintype.card G)
    (roots : Fin (Fintype.card (TranslationPhase A)) → G → PMF Bool)
    (hsupport : ∀ phase,
      IsQuittingActiveRoot ((cyclicSchedule A).active phase.val)
        (roots phase)) :
    ¬ ∀ phase,
      quittingProfileLiveRoot reward (profiles phase.val) time = roots phase := by
  have hproper : A ≠ Finset.univ := by
    intro hA
    rw [hA, Finset.card_univ] at hcard
    exact (Nat.lt_irrefl _ hcard)
  exact not_forall_liveRoot_eq_supportedCyclicWord_of_proper_resetChain
    reward profiles time owner hpositive A factor hfactor hstep hproper roots hsupport

/-- Every phase-varying cyclic root word is supported by its scheduled
block, so the abstract no-go applies directly. -/
theorem not_forall_liveRoot_eq_cyclicPhaseHazardRoots_of_card_lt
    (reward : {S : Finset G // S.Nonempty} → Payoff G)
    (profiles : ℕ → (quittingGame reward).BehaviorProfile)
    (time : ℕ) (owner : G)
    (hpositive : 0 < quittingStageCoalitionMass reward (profiles 0) time
      (quittingSingletonTerminal owner))
    (A : Finset G) (factor : ℝ) (hfactor : 0 < factor)
    (hstep : RetainsQuittingStageAtomOnInterval reward factor
      profiles 0 (Fintype.card (TranslationPhase A) - 1)
        (quittingSingletonTerminal owner) time)
    (hcard : A.card < Fintype.card G)
    (β : Fin (Fintype.card (TranslationPhase A)) → ℝ)
    (hβ0 : ∀ phase, 0 ≤ β phase)
    (hβ1 : ∀ phase, β phase ≤ 1) :
    ¬ ∀ phase,
      quittingProfileLiveRoot reward (profiles phase.val) time =
        cyclicPhaseHazardRoots A β hβ0 hβ1 phase := by
  apply not_forall_liveRoot_eq_supportedCyclicWord_of_card_lt
    reward profiles time owner hpositive A factor hfactor hstep hcard
      (cyclicPhaseHazardRoots A β hβ0 hβ1)
  intro phase
  exact isQuittingActiveRoot_uniformActiveRoot
    ((cyclicSchedule A).active phase.val) (β phase)
      (hβ0 phase) (hβ1 phase)

end

end CyclicKofNSupportedRootRetentionNoGo

end GameTheory
