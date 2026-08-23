/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Root.SuccessorCertificate

/-!
# Nashifying a marked sure-Quit coordinate

These are finite one-stage root facts.  A coordinate that is prescribed to
Quit surely needs only its own endpoint inequality; endpoint inequalities for
the remaining coordinates then assemble into a full endpoint Nash root.
The exact statement is the zero-error specialization.  No minimum, tail, or
chronological provenance hypothesis is part of this local interface.
-/

noncomputable section

namespace GameTheory

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- On one fixed, co-realized row, a marked sure-Quit inequality plus the
endpoint `ε`-Nash inequalities for every other coordinate gives full root
endpoint `ε`-Nash. -/
theorem isεQuittingRootEndpointNash_of_marked_sureQuit_of_others
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : Payoff ι) (root : ι → PMF Bool) (marked : ι) (ε : ℝ)
    (hε : 0 ≤ ε) (hsure : root marked = PMF.pure true)
    (hmarked : -ε ≤
      quittingRootEndpointDifference reward tail root marked)
    (hothers : ∀ other, other ≠ marked →
      (root other false).toReal *
            quittingRootEndpointDifference reward tail root other ≤ ε ∧
        -ε ≤ (root other true).toReal *
            quittingRootEndpointDifference reward tail root other) :
    IsεQuittingRootEndpointNash reward tail ε root := by
  intro who
  by_cases hwho : who = marked
  · subst who
    rw [hsure]
    simpa using And.intro hε hmarked
  · exact hothers who hwho

/-- Exact same-row control of every unmarked coordinate turns the marked
sure-exit row into a full exact Nash root. -/
theorem isZeroQuittingRootNash_of_marked_sureQuit_of_others
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : Payoff ι) (root : ι → PMF Bool) (marked : ι)
    (hsure : root marked = PMF.pure true)
    (hmarked : 0 ≤
      quittingRootEndpointDifference reward tail root marked)
    (hothers : ∀ other, other ≠ marked →
      (root other false).toReal *
            quittingRootEndpointDifference reward tail root other ≤ 0 ∧
        0 ≤ (root other true).toReal *
            quittingRootEndpointDifference reward tail root other) :
    IsεQuittingRootNash reward tail 0 root := by
  apply (isZeroQuittingRootEndpointNash_iff_isZeroQuittingRootNash
    reward tail root).mp
  exact isεQuittingRootEndpointNash_of_marked_sureQuit_of_others
    reward tail root marked 0 (by norm_num) hsure (by simpa using hmarked)
    (by simpa using hothers)

end GameTheory
