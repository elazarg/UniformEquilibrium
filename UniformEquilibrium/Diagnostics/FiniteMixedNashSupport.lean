/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.ProofView.Concepts.Existence.NashExistenceMixed

/-!
# Support indifference in finite mixed Nash equilibria

This module records the finite normal-form complementarity fact used by the
finite-deadline timing regressions: every pure action assigned positive mass
by a mixed Nash equilibrium has zero mixed gain.
-/

noncomputable section

namespace GameTheory
namespace KernelGame

open Math.Probability

/-- Every supported pure action in a finite mixed Nash equilibrium has zero
mixed gain. -/
theorem mixedGain_eq_zero_of_mem_support
    {I : Type} [Fintype I] [DecidableEq I]
    (G : KernelGame I) [Finite G.Outcome]
    [∀ who, Finite (G.Strategy who)]
    (mixed : ∀ who, PMF (G.Strategy who))
    (hnash : G.mixedExtension.IsNash mixed)
    (who : I) (action : G.Strategy who)
    (haction : mixed who action ≠ 0) :
    G.mixedGain mixed who action = 0 := by
  letI : Fintype (G.Strategy who) := Fintype.ofFinite _
  have hgain : ∀ choice : G.Strategy who,
      G.mixedGain mixed who choice ≤ 0 :=
    fun choice ↦ (G.isNash_iff_gains_nonpos mixed).mp hnash who choice
  have hweighted := G.weighted_gain_sum_zero mixed who
  unfold Math.Probability.expect at hweighted
  rw [tsum_fintype] at hweighted
  have hterm :
      (mixed who action).toReal * G.mixedGain mixed who action = 0 :=
    (Finset.sum_eq_zero_iff_of_nonpos (fun choice _ ↦
      mul_nonpos_of_nonneg_of_nonpos ENNReal.toReal_nonneg
        (hgain choice))).mp hweighted action (Finset.mem_univ action)
  have hmass : 0 < (mixed who action).toReal :=
    ENNReal.toReal_pos haction (PMF.apply_ne_top _ _)
  exact (mul_eq_zero.mp hterm).resolve_left hmass.ne'

end KernelGame
end GameTheory
