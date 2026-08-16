/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticPositiveSlopeAtom

/-!
# Terminal atom alternatives from a stopping-law debt slope

This module packages the literal prescribed-atom or pure-time-rectangle
alternative produced by a positive stopping-law debt slope.  The proposition
is independent of any counterexample regime, selected frontier, or
asymptotic tangent family.
-/

noncomputable section

namespace GameTheory

open Math.Probability
open scoped Topology

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The literal output of the positive coordinate-slope decoder, packaged so
it can be transported along the fixed subsequence of a counterexample
frontier. -/
def HasQuittingStoppingLawDebtSlopeAtomAlternative
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (mover observer : ι)
    (target : (quittingGame reward).BehaviorStrategy mover)
    (charge : ℝ) : Prop :=
  (∃ terminal : {S : Finset ι // S.Nonempty},
    charge / 2 ≤
      (Fintype.card (QuittingTerminalOutcome ι) : ℝ) *
        quittingTerminalPayoffDifferenceAtom reward profile
          (Function.update profile mover target) observer (some terminal)) ∨
  ((∃ terminal : {S : Finset ι // S.Nonempty},
      charge / 4 ≤
        (Fintype.card (QuittingTerminalOutcome ι) : ℝ) *
          quittingTerminalPayoffDifferenceAtom reward
            (Function.update (Function.update profile mover target) observer
              (quittingPureTimeBehaviorStrategy reward observer none))
            (Function.update profile observer
              (quittingPureTimeBehaviorStrategy reward observer none))
            observer (some terminal)) ∨
    ∃ stop : ℕ, ∃ terminal : {S : Finset ι // S.Nonempty},
      charge / 4 ≤
        (Fintype.card (QuittingTerminalOutcome ι) : ℝ) *
          quittingTerminalPayoffDifferenceAtom reward
            (Function.update (Function.update profile mover target) observer
              (quittingPureTimeBehaviorStrategy reward observer (some stop)))
            (Function.update profile observer
              (quittingPureTimeBehaviorStrategy reward observer (some stop)))
            observer (some terminal))

end GameTheory
