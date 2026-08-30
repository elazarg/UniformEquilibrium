/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import MathUE.ProbabilityMassFunction.Simplex

/-!
# Simplex coordinates for quitting roots

This module owns the low topological model of a product quitting root and the
exact conversions between Boolean PMFs and their simplex coordinates.  It has
no Nash, Bellman, cycle, or diagnostic dependency.
-/

noncomputable section

namespace GameTheory

open Math.ProbabilityMassFunction

variable {ι : Type} [Fintype ι]

/-- Product of Boolean mixed-action simplices used as a topological model of
quitting roots. -/
abbrev QuittingRootSimplex (ι : Type) [Fintype ι] :=
  ∀ _ : ι, stdSimplex ℝ Bool

/-- Convert simplex coordinates to the corresponding profile of finite
probability mass functions. -/
def quittingRootOfSimplex (root : QuittingRootSimplex ι) :
    ι → PMF Bool :=
  fun who => (stdSimplexEquiv (α := Bool)).symm (root who)

/-- Convert a product root to its Boolean simplex coordinates. -/
def quittingSimplexOfRoot (root : ι → PMF Bool) : QuittingRootSimplex ι :=
  fun who => stdSimplexEquiv (root who)

@[simp] theorem quittingRootOfSimplex_apply_toReal
    (root : QuittingRootSimplex ι) (who : ι) (action : Bool) :
    ((quittingRootOfSimplex root who) action).toReal = root who action := by
  simp [quittingRootOfSimplex, stdSimplexEquiv_symm_apply]

@[simp] theorem quittingRootOfSimplex_simplexOfRoot (root : ι → PMF Bool) :
    quittingRootOfSimplex (quittingSimplexOfRoot root) = root := by
  funext who
  exact (stdSimplexEquiv (α := Bool)).symm_apply_apply (root who)

@[simp] theorem quittingSimplexOfRoot_rootOfSimplex
    (root : QuittingRootSimplex ι) :
    quittingSimplexOfRoot (quittingRootOfSimplex root) = root := by
  funext who
  exact (stdSimplexEquiv (α := Bool)).apply_symm_apply (root who)

end GameTheory
