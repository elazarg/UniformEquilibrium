/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Root.LiteralRootStackSurvival
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticPositiveSlopeRectangle
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticResetIncidenceReturn

/-!
# Exact transport of terminal atoms through a common literal prefix

The exact-prefix chronology and the stopping-law atom decoder meet through a
simple affine identity.  If the same finite root word is placed in front of
every endpoint of a payoff difference or four-profile rectangle, all fresh
prefix absorption cancels.  The old terminal atom is multiplied by exactly
the joint survival of the word.

Thus the multi-active conclusion that joint survival tends to one really does
preserve the fixed literal atom through the exact prefix stack.  This is a
terminal-law transport statement; it does not assert that the same roots stay
exact Nash after changing the suffix endpoint.
-/

noncomputable section

namespace GameTheory

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- A common literal root stack scales the difference of two old outcome-law
coordinates by exactly its joint survival. -/
theorem quittingTerminalOutcomeMass_literalRootStack_sub_eq
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : List (ι → PMF Bool))
    (first second : (quittingGame reward).BehaviorProfile)
    (outcome : QuittingTerminalOutcome ι) :
    quittingTerminalOutcomeMass reward
          (quittingLiteralRootStackProfile reward roots first) outcome -
        quittingTerminalOutcomeMass reward
          (quittingLiteralRootStackProfile reward roots second) outcome =
      quittingLiteralRootStackJointSurvival roots *
        (quittingTerminalOutcomeMass reward first outcome -
          quittingTerminalOutcomeMass reward second outcome) := by
  induction roots with
  | nil => simp [quittingLiteralRootStackJointSurvival]
  | cons root roots ih =>
      simp only [quittingLiteralRootStackProfile_cons,
        quittingTerminalOutcomeMass_rootThenContinuation]
      cases outcome <;>
        simp only [quittingLiteralRootStackJointSurvival, List.map_cons,
          List.prod_cons] at ih ⊢ <;>
        linear_combination (quittingStationaryContinueMass root) * ih

/-- The same cancellation holds for a four-law rectangle. -/
theorem quittingTerminalOutcomeMass_literalRootStack_rectangle_eq
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : List (ι → PMF Bool))
    (x00 x01 x10 x11 : (quittingGame reward).BehaviorProfile)
    (outcome : QuittingTerminalOutcome ι) :
    quittingTerminalOutcomeMass reward
          (quittingLiteralRootStackProfile reward roots x11) outcome -
        quittingTerminalOutcomeMass reward
          (quittingLiteralRootStackProfile reward roots x10) outcome -
        quittingTerminalOutcomeMass reward
          (quittingLiteralRootStackProfile reward roots x01) outcome +
        quittingTerminalOutcomeMass reward
          (quittingLiteralRootStackProfile reward roots x00) outcome =
      quittingLiteralRootStackJointSurvival roots *
        (quittingTerminalOutcomeMass reward x11 outcome -
          quittingTerminalOutcomeMass reward x10 outcome -
          quittingTerminalOutcomeMass reward x01 outcome +
          quittingTerminalOutcomeMass reward x00 outcome) := by
  induction roots with
  | nil => simp [quittingLiteralRootStackJointSurvival]
  | cons root roots ih =>
      simp only [quittingLiteralRootStackProfile_cons,
        quittingTerminalOutcomeMass_rootThenContinuation]
      cases outcome <;>
        simp only [quittingLiteralRootStackJointSurvival, List.map_cons,
          List.prod_cons] at ih ⊢ <;>
        linear_combination (quittingStationaryContinueMass root) * ih

/-- **Common-prefix atom transport.**  Both two-profile payoff atoms and
four-profile rectangle atoms are transported exactly by the joint-survival
factor of a common literal root stack. -/
theorem quittingTerminalAtoms_literalRootStack_eq_jointSurvival_mul
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : List (ι → PMF Bool))
    (x00 x01 x10 x11 : (quittingGame reward).BehaviorProfile)
    (observer : ι) (outcome : QuittingTerminalOutcome ι) :
    quittingTerminalPayoffDifferenceAtom reward
          (quittingLiteralRootStackProfile reward roots x00)
          (quittingLiteralRootStackProfile reward roots x01)
          observer outcome =
        quittingLiteralRootStackJointSurvival roots *
          quittingTerminalPayoffDifferenceAtom reward x00 x01 observer
            outcome ∧
      quittingTerminalPayoffRectangleAtom reward
          (quittingLiteralRootStackProfile reward roots x00)
          (quittingLiteralRootStackProfile reward roots x01)
          (quittingLiteralRootStackProfile reward roots x10)
          (quittingLiteralRootStackProfile reward roots x11)
          observer outcome =
        quittingLiteralRootStackJointSurvival roots *
          quittingTerminalPayoffRectangleAtom reward x00 x01 x10 x11
            observer outcome := by
  constructor
  · unfold quittingTerminalPayoffDifferenceAtom
    rw [quittingTerminalOutcomeMass_literalRootStack_sub_eq]
    ring
  · unfold quittingTerminalPayoffRectangleAtom
    rw [quittingTerminalOutcomeMass_literalRootStack_rectangle_eq]
    ring

end GameTheory
