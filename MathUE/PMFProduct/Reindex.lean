/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import MathUE.PMFProduct.Basic

/-!
# Reindexing independent product PMFs

An independent finite product commutes with transporting its coordinates
through an equivalence.  The action-space equivalence is kept explicit so the
lemma also applies to dependent game-level transports whose implementation is
definitionally coordinate precomposition.
-/

namespace Math.PMFProduct

open Math.Probability Math.ProbabilityMassFunction

/-- Push an independent product forward through a reindexing equivalence. -/
theorem pmfPi_map_precompEquiv {ι κ B : Type*} [Fintype ι] [Fintype κ]
    (e : ι ≃ κ) (E : (ι → B) ≃ (κ → B))
    (hE : ∀ action who, E action who = action (e.symm who))
    (root : ι → PMF B) :
    PMF.map E (pmfPi root) = pmfPi (fun who => root (e.symm who)) := by
  have hEsymm : ∀ (action : κ → B) (who : ι),
      E.symm action who = action (e who) := by
    intro action who
    have h := hE (E.symm action) (e who)
    rw [Equiv.apply_symm_apply, Equiv.symm_apply_apply] at h
    exact h.symm
  ext action
  rw [map_equiv_apply, pmfPi_apply, pmfPi_apply]
  refine Fintype.prod_equiv e _ _ fun who => ?_
  simp [hEsymm]

end Math.PMFProduct
