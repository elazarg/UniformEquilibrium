/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Research.Quitting.CyclicKofNBellmanBridge
import Research.Quitting.ActiveSetSupport

/-!
# Finite Nash certificates for cyclic `K/N` quitting schedules

For a fixed cyclic root word there is no need to guess a compatible word of
Bellman values.  The infinite terminal evaluation of the root word is the
canonical solution of every policy-evaluation equation.  Consequently a
cyclic uniform-equilibrium certificate consists only of one exact root-Nash
condition at each phase.

The second half rewrites those remaining conditions as endpoint-layer
inequalities.  This makes the support-size dependence explicit: a block of
size `K` gives degree at most `K` for Continue and degree at most `K + 1` for
the full-game Quit deviation of a player outside the block.
-/

namespace GameTheory

namespace CyclicKofNFiniteNashCertificate

open StochasticGame Math.Probability Math.PMFProduct
open CyclicKofNArithmetic CyclicKofNQuittingSchedule
open CyclicKofNBellmanBridge
open scoped BigOperators Pointwise

noncomputable section

variable {G : Type} [AddGroup G] [Fintype G] [DecidableEq G]

/-- The canonical Bellman value word selected by the cyclic root word. -/
def cyclicTerminalValues
    (reward : {S : Finset G // S.Nonempty} → Payoff G)
    (A : Finset G) (β : ℝ) (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1) :
    Fin (Fintype.card (TranslationPhase A)) → Payoff G :=
  quittingCyclicTerminalValue reward (cyclicPhaseRoots A β hβ0 hβ1)

/-- The residual finite certificate after the Bellman values have been
eliminated: exact one-stage Nash at every cyclic phase, evaluated against the
canonical value of the next phase. -/
def IsFiniteCyclicNashCertificate
    (reward : {S : Finset G // S.Nonempty} → Payoff G)
    (A : Finset G) (β : ℝ) (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1) : Prop :=
  ∀ phase,
    IsεQuittingRootNash reward
      (cyclicTerminalValues reward A β hβ0 hβ1
        (finRotate (Fintype.card (TranslationPhase A)) phase))
      0 (cyclicPhaseRoots A β hβ0 hβ1 phase)

/-- Canonical cyclic terminal values satisfy the Bellman policy equations
identically; this is not part of the finite feasibility problem. -/
theorem cyclicTerminalValues_eq_rootSuccessorPayoff
    (reward : {S : Finset G // S.Nonempty} → Payoff G)
    (A : Finset G) (β : ℝ) (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1)
    (phase : Fin (Fintype.card (TranslationPhase A))) :
    cyclicTerminalValues reward A β hβ0 hβ1 phase =
      quittingRootSuccessorPayoff reward
        (cyclicTerminalValues reward A β hβ0 hβ1
          (finRotate (Fintype.card (TranslationPhase A)) phase))
        (cyclicPhaseRoots A β hβ0 hβ1 phase) := by
  exact quittingCyclicTerminalValue_eq_rootSuccessorPayoff
    reward (cyclicPhaseRoots A β hβ0 hβ1) phase

/-- **Bellman-state elimination.**  For a nontrivial population and a
nonempty translated block with proper positive hazard, the finite Nash
certificate alone produces a uniform-equilibrium payoff. -/
theorem isUniformEquilibriumPayoff_of_finiteCyclicNashCertificate
    (reward : {S : Finset G // S.Nonempty} → Payoff G)
    (A : Finset G) (hA : A.Nonempty) (hG : 1 < Fintype.card G)
    (β : ℝ) (hβpos : 0 < β) (hβlt : β < 1)
    (hnash : IsFiniteCyclicNashCertificate reward A β hβpos.le hβlt.le)
    (initial : Fin (Fintype.card (TranslationPhase A))) :
    (quittingGame reward).IsUniformEquilibriumPayoff none
      (cyclicTerminalValues reward A β hβpos.le hβlt.le initial) := by
  apply isUniformEquilibriumPayoff_quittingCyclicTerminalValue_of_certificate
    reward
    (cyclicPhaseRoots A β hβpos.le hβlt.le)
    (cyclicTerminalValues reward A β hβpos.le hβlt.le)
    initial
  · intro phase
    exact cyclicTerminalValues_eq_rootSuccessorPayoff
      reward A β hβpos.le hβlt.le phase
  · exact hnash
  · intro who
    exact cyclicPhaseRoots_opponentContracts A hA hG β hβpos hβlt who

/-! ## Endpoint-layer form of the residual certificate -/

/-- The full-game endpoint-layer certificate.  The inserted outsider in the
first sum is exactly why its general degree bound is `A.card + 1`. -/
def IsFiniteCyclicEndpointLayerCertificate
    (reward : {S : Finset G // S.Nonempty} → Payoff G)
    (A : Finset G) (β : ℝ) (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1) : Prop :=
  ∀ phase who,
    ((cyclicPhaseRoots A β hβ0 hβ1 phase) who false).toReal *
        quittingActiveEndpointLayerDifference reward
          (cyclicTerminalValues reward A β hβ0 hβ1
            (finRotate (Fintype.card (TranslationPhase A)) phase))
          ((cyclicSchedule A).active phase.val)
          (cyclicPhaseRoots A β hβ0 hβ1 phase) A.card who ≤ 0 ∧
      -(0 : ℝ) ≤ ((cyclicPhaseRoots A β hβ0 hβ1 phase) who true).toReal *
        quittingActiveEndpointLayerDifference reward
          (cyclicTerminalValues reward A β hβ0 hβ1
            (finRotate (Fintype.card (TranslationPhase A)) phase))
          ((cyclicSchedule A).active phase.val)
          (cyclicPhaseRoots A β hβ0 hβ1 phase) A.card who

/-- **Exact finite reduction.**  The residual cyclic Nash certificate is
equivalent to finitely many scalar endpoint inequalities.  Continue uses
layers `0,...,K`; a Quit deviation uses `0,...,K+1` only because an inactive
player is allowed to enter the quitting support in the full game. -/
theorem finiteCyclicNashCertificate_iff_endpointLayerCertificate
    (reward : {S : Finset G // S.Nonempty} → Payoff G)
    (A : Finset G) (β : ℝ) (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1) :
    IsFiniteCyclicNashCertificate reward A β hβ0 hβ1 ↔
      IsFiniteCyclicEndpointLayerCertificate reward A β hβ0 hβ1 := by
  unfold IsFiniteCyclicNashCertificate
    IsFiniteCyclicEndpointLayerCertificate
  constructor
  · intro hnash phase
    have hroot : IsQuittingActiveRoot
        ((cyclicSchedule A).active phase.val)
        (cyclicPhaseRoots A β hβ0 hβ1 phase) := by
      simpa [cyclicPhaseRoots, cyclicRoots] using
        isQuittingActiveRoot_uniformActiveRoot
          ((cyclicSchedule A).active phase.val) β hβ0 hβ1
    have hcard : ((cyclicSchedule A).active phase.val).card ≤ A.card :=
      (card_cyclicSchedule_active A phase.val).le
    exact (isεQuittingRootNash_iff_activeEndpointLayerInequalities
      reward
      (cyclicTerminalValues reward A β hβ0 hβ1
        (finRotate (Fintype.card (TranslationPhase A)) phase))
      ((cyclicSchedule A).active phase.val)
      (cyclicPhaseRoots A β hβ0 hβ1 phase) 0 hroot hcard).mp
        (hnash phase)
  · intro hlayers phase
    have hroot : IsQuittingActiveRoot
        ((cyclicSchedule A).active phase.val)
        (cyclicPhaseRoots A β hβ0 hβ1 phase) := by
      simpa [cyclicPhaseRoots, cyclicRoots] using
        isQuittingActiveRoot_uniformActiveRoot
          ((cyclicSchedule A).active phase.val) β hβ0 hβ1
    have hcard : ((cyclicSchedule A).active phase.val).card ≤ A.card :=
      (card_cyclicSchedule_active A phase.val).le
    exact (isεQuittingRootNash_iff_activeEndpointLayerInequalities
      reward
      (cyclicTerminalValues reward A β hβ0 hβ1
        (finRotate (Fintype.card (TranslationPhase A)) phase))
      ((cyclicSchedule A).active phase.val)
      (cyclicPhaseRoots A β hβ0 hβ1 phase) 0 hroot hcard).mpr
        (hlayers phase)

/-- Endpoint feasibility for the literal one-at-a-time / `K`-at-a-time
rule, where only members of the scheduled block may move. -/
def IsFiniteCyclicRestrictedEndpointCertificate
    (reward : {S : Finset G // S.Nonempty} → Payoff G)
    (A : Finset G) (β : ℝ) (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1) : Prop :=
  ∀ phase,
    IsεQuittingRestrictedActiveEndpointNash reward
      (cyclicTerminalValues reward A β hβ0 hβ1
        (finRotate (Fintype.card (TranslationPhase A)) phase))
      ((cyclicSchedule A).active phase.val) 0
      (cyclicPhaseRoots A β hβ0 hβ1 phase)

/-- In the restricted-move game, the same cyclic certificate contains only
degree-`K` layer expressions. -/
theorem finiteCyclicRestrictedEndpointCertificate_iff_degreeKLayers
    (reward : {S : Finset G // S.Nonempty} → Payoff G)
    (A : Finset G) (β : ℝ) (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1) :
    IsFiniteCyclicRestrictedEndpointCertificate
        reward A β hβ0 hβ1 ↔
      ∀ phase who,
        who ∈ (cyclicSchedule A).active phase.val →
          ((cyclicPhaseRoots A β hβ0 hβ1 phase) who false).toReal *
              quittingRestrictedActiveEndpointLayerDifference reward
                (cyclicTerminalValues reward A β hβ0 hβ1
                  (finRotate (Fintype.card (TranslationPhase A)) phase))
                ((cyclicSchedule A).active phase.val)
                (cyclicPhaseRoots A β hβ0 hβ1 phase) A.card who ≤ 0 ∧
            -(0 : ℝ) ≤ ((cyclicPhaseRoots A β hβ0 hβ1 phase) who true).toReal *
              quittingRestrictedActiveEndpointLayerDifference reward
                (cyclicTerminalValues reward A β hβ0 hβ1
                  (finRotate (Fintype.card (TranslationPhase A)) phase))
                ((cyclicSchedule A).active phase.val)
                (cyclicPhaseRoots A β hβ0 hβ1 phase) A.card who := by
  unfold IsFiniteCyclicRestrictedEndpointCertificate
  constructor
  · intro hnash phase
    have hroot : IsQuittingActiveRoot
        ((cyclicSchedule A).active phase.val)
        (cyclicPhaseRoots A β hβ0 hβ1 phase) := by
      simpa [cyclicPhaseRoots, cyclicRoots] using
        isQuittingActiveRoot_uniformActiveRoot
          ((cyclicSchedule A).active phase.val) β hβ0 hβ1
    have hcard : ((cyclicSchedule A).active phase.val).card ≤ A.card :=
      (card_cyclicSchedule_active A phase.val).le
    exact (isεQuittingRestrictedActiveEndpointNash_iff_degreeKLayerInequalities
      reward
      (cyclicTerminalValues reward A β hβ0 hβ1
        (finRotate (Fintype.card (TranslationPhase A)) phase))
      ((cyclicSchedule A).active phase.val)
      (cyclicPhaseRoots A β hβ0 hβ1 phase) 0 hroot hcard).mp
        (hnash phase)
  · intro hlayers phase
    have hroot : IsQuittingActiveRoot
        ((cyclicSchedule A).active phase.val)
        (cyclicPhaseRoots A β hβ0 hβ1 phase) := by
      simpa [cyclicPhaseRoots, cyclicRoots] using
        isQuittingActiveRoot_uniformActiveRoot
          ((cyclicSchedule A).active phase.val) β hβ0 hβ1
    have hcard : ((cyclicSchedule A).active phase.val).card ≤ A.card :=
      (card_cyclicSchedule_active A phase.val).le
    exact (isεQuittingRestrictedActiveEndpointNash_iff_degreeKLayerInequalities
      reward
      (cyclicTerminalValues reward A β hβ0 hβ1
        (finRotate (Fintype.card (TranslationPhase A)) phase))
      ((cyclicSchedule A).active phase.val)
      (cyclicPhaseRoots A β hβ0 hβ1 phase) 0 hroot hcard).mpr
        (hlayers phase)

end

end CyclicKofNFiniteNashCertificate

end GameTheory
