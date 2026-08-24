/-
Copyright (c) 2026 UniformEquilibrium contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: UniformEquilibrium contributors
-/

import GameTheory.Analysis.Nash

/-!
# Compact mixed-Nash carrier for an induced finite face game

The strict-toggle persistent-base residual minimizes a continuous excess over
the complete mixed-Nash set of a finite binary game.  The Nash existence
theorem supplies nonemptiness; its closed-graph proof also gives compactness
of the exact equilibrium carrier in the same mixed-polytope coordinates.
-/

noncomputable section

namespace GameTheory

open GameTheory.Math.Probability

universe uι us uo

variable {ι : Type uι} [Fintype ι] [DecidableEq ι]
variable {F : GameForm ι} [∀ who, Fintype (F.sig.Strategy who)]

/-- Exact mixed Nash points represented in the compact product of strategy
simplices used by the finite-game existence proof. -/
def mixedNashPolytopeSet
    (utility : F.sig.Outcome → ι → ℝ) : Set (mixedPolytope F.sig) :=
  {point | point.1 ∈ bestReplies F utility point.1}

/-- The exact mixed-Nash carrier is closed. -/
theorem isClosed_mixedNashPolytopeSet
    (utility : F.sig.Outcome → ι → ℝ) :
    IsClosed (mixedNashPolytopeSet utility) := by
  have hmap : Continuous fun point : mixedPolytope F.sig =>
      (point, point.1) :=
    continuous_id.prodMk continuous_subtype_val
  exact (closedGraph_bestReplies utility).preimage hmap

/-- The exact mixed-Nash carrier is compact. -/
theorem isCompact_mixedNashPolytopeSet
    (utility : F.sig.Outcome → ι → ℝ) :
    IsCompact (mixedNashPolytopeSet utility) := by
  letI : CompactSpace (mixedPolytope F.sig) :=
    isCompact_iff_compactSpace.mp (isCompact_mixedPolytope F.sig)
  exact (isClosed_mixedNashPolytopeSet utility).isCompact

/-- The exact mixed-Nash carrier is nonempty for nonempty finite action sets. -/
theorem mixedNashPolytopeSet_nonempty
    [∀ who, Nonempty (F.sig.Strategy who)]
    (utility : F.sig.Outcome → ι → ℝ) :
    (mixedNashPolytopeSet utility).Nonempty := by
  obtain ⟨profile, hnash⟩ := exists_isNash_mixed utility
  let point : mixedPolytope F.sig := ⟨probs F.sig profile,
    fun who _ => (profile who).prob_mem_stdSimplex⟩
  refine ⟨point, ?_⟩
  change point.1 ∈ bestReplies F utility point.1
  change probs F.sig profile ∈ bestReplies F utility (probs F.sig profile)
  exact (probs_mem_bestReplies_self_iff_isNash utility profile).mpr hnash

/-- A continuous semantic excess on the full Nash carrier either accepts an
exact Nash point or has a strictly positive attained gap on every Nash point. -/
theorem exists_mixedNash_nonpos_or_pos_gap
    [∀ who, Nonempty (F.sig.Strategy who)]
    (utility : F.sig.Outcome → ι → ℝ)
    (excess : mixedPolytope F.sig → ℝ) (hexcess : Continuous excess) :
    (∃ point ∈ mixedNashPolytopeSet utility, excess point ≤ 0) ∨
      ∃ gamma : ℝ, 0 < gamma ∧
        ∀ point ∈ mixedNashPolytopeSet utility, gamma ≤ excess point := by
  obtain ⟨minimizer, hminimizer, hminimal⟩ :=
    (isCompact_mixedNashPolytopeSet utility).exists_isMinOn
      (mixedNashPolytopeSet_nonempty utility) hexcess.continuousOn
  by_cases haccept : excess minimizer ≤ 0
  · exact Or.inl ⟨minimizer, hminimizer, haccept⟩
  · exact Or.inr ⟨excess minimizer, lt_of_not_ge haccept,
      fun point hpoint => hminimal hpoint⟩

end GameTheory
