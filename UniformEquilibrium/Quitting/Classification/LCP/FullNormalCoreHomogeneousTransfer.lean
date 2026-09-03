/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Classification.LCP.NormalCore

/-!
# Homogeneous singleton feasibility on a full normal core

When the recursively normal core is all players, its principal matrix is the
full matrix up to the canonical subtype reindexing. This module records the
corresponding equivalence of homogeneous singleton feasibility.
-/

noncomputable section

namespace GameTheory
namespace QuittingLCPClassification

open Math.LinearProgramming

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Canonical identification of a full normal-core subtype with the ambient
player type. -/
def fullNormalCoreEquiv (M : ι → ι → ℝ)
    (hcore : normalCore M = Finset.univ) : normalCore M ≃ ι where
  toFun player := player.1
  invFun player := ⟨player, by rw [hcore]; exact Finset.mem_univ player⟩
  left_inv _ := Subtype.ext rfl
  right_inv _ := rfl

/-- Reindexing the normal-player principal along the canonical full-core
equivalence recovers the ambient matrix literally. -/
theorem reindex_normalPlayerMatrix_fullNormalCoreEquiv
    (M : ι → ι → ℝ) (hcore : normalCore M = Finset.univ) :
    reindexMatrix (fullNormalCoreEquiv M hcore) (normalPlayerMatrix M) = M := by
  funext receiver owner
  rfl

/-- Homogeneous singleton feasibility is unchanged when a full normal core is
viewed as its principal subtype. -/
theorem singletonLCPFeasible_normalPlayerMatrix_iff_of_normalCore_eq_univ
    (M : ι → ι → ℝ) (hcore : normalCore M = Finset.univ) :
    SingletonLCPFeasible (normalPlayerMatrix M) ↔ SingletonLCPFeasible M := by
  rw [← singletonLCPFeasible_reindexMatrix_iff
    (fullNormalCoreEquiv M hcore) (normalPlayerMatrix M),
    reindex_normalPlayerMatrix_fullNormalCoreEquiv]

end QuittingLCPClassification
end GameTheory
