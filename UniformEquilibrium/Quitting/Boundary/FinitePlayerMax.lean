/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Mathlib.Data.Finset.BooleanAlgebra
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Real.Basic

/-!
# Maximum over a nonempty finite player type

This module owns the small finite-type maximum used by quitting boundary and
terminal exploitability interfaces.  It is independent of every game-semantic
construction despite retaining its established namespace and declarations.
-/

noncomputable section

namespace GameTheory.QuittingBoundaryHolonomy

variable {ι : Type}

/-- Maximum of a real-valued quantity over the nonempty finite player set. -/
def finitePlayerMax [Fintype ι] [Nonempty ι] (f : ι → ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty f

theorem finitePlayerMax_le [Fintype ι] [Nonempty ι]
    {f : ι → ℝ} {bound : ℝ}
    (hf : ∀ who, f who ≤ bound) : finitePlayerMax f ≤ bound := by
  dsimp [finitePlayerMax]
  exact Finset.sup'_le Finset.univ_nonempty f (fun who _ ↦ hf who)

theorem le_finitePlayerMax [Fintype ι] [Nonempty ι]
    (f : ι → ℝ) (who : ι) :
    f who ≤ finitePlayerMax f := by
  dsimp [finitePlayerMax]
  exact Finset.le_sup' f (Finset.mem_univ who)

end GameTheory.QuittingBoundaryHolonomy
