/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Boundary.Holonomy.Transport
import UniformEquilibrium.Quitting.Cycles.CycleMismatchContraction

/-!
# Max-affine transport of quitting companion maps

The scalar companion map of a quitting root is the action of its max-affine
boundary label. Consequently, a finite backward Bellman recursion is the
action of the chronological product of its one-stage labels. This identifies
the game-semantic recursion with the generic path action while retaining the
explicit floor, shift, and survival coefficients supplied by boundary
holonomy.
-/

noncomputable section

namespace GameTheory

open Math.Probability Math.ProbabilityMassFunction

variable {ι : Type} [Fintype ι] [DecidableEq ι]

@[simp] theorem quittingCompanionLabel_apply
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι) (time : ℕ)
    (continuation : ℝ) :
    (quittingCompanionLabel reward roots who time).apply continuation =
      quittingRootCompanionMap reward (roots time) who continuation := by
  rfl

/-- A finite companion composite is the action of its chronological composite
label. -/
theorem quittingCompanionComposite_eq_compList_apply
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι) : ∀ start fuel continuation,
    quittingCompanionComposite reward roots who start fuel continuation =
      (Math.MaxAffineTransport.Label.compList
        (quittingCompanionLabelList reward roots who start fuel)).apply
          continuation := by
  intro start fuel
  induction fuel generalizing start with
  | zero => simp [quittingCompanionLabelList]
  | succ fuel ih =>
      intro continuation
      rw [quittingCompanionComposite_succ, ih (start + 1),
        quittingCompanionLabelList]
      symm
      rw [Math.MaxAffineTransport.Label.apply_compList_append_singleton
        _ _ (quittingCompanionLabel_slope_nonneg reward roots who start)]
      exact quittingCompanionLabel_apply reward roots who start _

end GameTheory

end
