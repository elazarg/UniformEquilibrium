/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Research.Quitting.ConcentratedSingleton.StrategicDispatch
import UniformEquilibrium.Diagnostics.Quitting.StoppingLaw.StaticStrategicCompression

/-!
# Tentative compression of the concentrated singleton handoff

The complete relabeled concentrated-singleton dispatch compresses to a static
atomic handoff or exact player deletion.  Its tail-escape and
fixed-owner-join-loss arms share a positive collision gap: the reset owner
strictly gains by joining the named singleton exit.

This theorem remains in Research with the rich packet-level dispatch that it
consumes.  The independently useful static compression interface lives in
`StoppingLaw.StaticStrategicCompression`.
-/

noncomputable section

namespace GameTheory

variable {iota : Type} [Fintype iota] [DecidableEq iota]

/-- **Full concentrated-singleton compression.**  Every arm of the relabeled
concentrated singleton handoff is already either an exact player deletion or
the same static atomic-toggle handoff.  In the tail-escape and
fixed-owner-join-loss arms, the reset owner is the strict joiner of the
singleton exit of `other`. -/
theorem QuittingTerminalExploitabilityWitness.concentratedSingletonStrategicDispatch_compress
    {reward : {S : Finset iota // S.Nonempty} → Payoff iota}
    (witness : QuittingTerminalExploitabilityWitness reward)
    {profiles : ℕ → (quittingGame reward).BehaviorProfile}
    {owner : iota} {terminal : {S : Finset iota // S.Nonempty}}
    {cutoff : ℕ → ℕ} {scale : ℕ → ℝ}
    (packet : QuittingReprojectionConcentratedPacket
      reward profiles owner terminal cutoff scale)
    (other : iota)
    (hdispatch : HasQuittingConcentratedSingletonStrategicDispatch
      witness packet other) :
    HasQuittingStaticAtomicToggleHandoff reward ∨
      HasQuittingExactPlayerDeletionAtGap reward other
        witness.terminalGap := by
  classical
  obtain ⟨_terminal, _endpoint, _static, hstrategic⟩ := hdispatch
  rcases hstrategic with hatomic | hpunishment | hdeletion | htail | hloss
  · exact Or.inl hatomic
  · exact witness.singletonStaticStrategicDispatch_compress other
      (Or.inr (Or.inl hpunishment))
  · exact Or.inr hdeletion
  · dsimp [HasQuittingConcentratedSingletonOwnerTailEscape] at htail
    have hstrict : quittingSoloReward reward other owner <
        quittingSingletonCollisionReward reward other owner :=
      sub_pos.mp htail.1
    have hownerNe : owner ≠ other := by
      intro heq
      subst owner
      simp [quittingSingletonCollisionReward, quittingSoloReward] at hstrict
    exact Or.inl
      (witness.hasStaticAtomicToggleHandoff_of_strictSingletonJoiner
        other owner hownerNe hstrict)
  · dsimp [HasQuittingConcentratedSingletonFixedOwnerJoinLoss] at hloss
    have hstrict : quittingSoloReward reward other owner <
        quittingSingletonCollisionReward reward other owner :=
      sub_pos.mp hloss.1
    have hownerNe : owner ≠ other := by
      intro heq
      subst owner
      simp [quittingSingletonCollisionReward, quittingSoloReward] at hstrict
    exact Or.inl
      (witness.hasStaticAtomicToggleHandoff_of_strictSingletonJoiner
        other owner hownerNe hstrict)

end GameTheory
