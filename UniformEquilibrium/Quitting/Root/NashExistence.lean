/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Boundary.Repair.ComplementarityClosed

/-!
# Exact finite quitting-root Nash existence

Every finite one-stage quitting game with a fixed continuation payoff has an
exact mixed Nash root.  This is the `PMF Bool` interface to the simplex-valued
existence theorem.
-/

noncomputable section

namespace GameTheory

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}

/-- Finite mixed Nash existence in the root-Nash formulation. -/
theorem exists_isZeroQuittingRootNash
    (tail : Payoff ι) :
    ∃ root : ι → PMF Bool, IsεQuittingRootNash reward tail 0 root := by
  obtain ⟨simplexRoot, hendpoint⟩ :=
    exists_isZeroQuittingRootEndpointNash_simplex reward tail
  refine ⟨quittingRootOfSimplex simplexRoot, ?_⟩
  exact (isZeroQuittingRootEndpointNash_iff_isZeroQuittingRootNash
    reward tail (quittingRootOfSimplex simplexRoot)).mp hendpoint

end GameTheory
