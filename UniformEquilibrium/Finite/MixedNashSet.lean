/-
Copyright (c) 2026 UniformEquilibrium contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: UniformEquilibrium contributors
-/

import GameTheory.Analysis.Nash

/-!
# Compact mixed-Nash carrier for a finite game

A continuous excess can be minimized over the complete mixed-Nash set
of a finite game. Kakutani's theorem supplies nonemptiness, and the closed
graph of the best-reply correspondence gives compactness of the carrier in
mixed-polytope coordinates.
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
  let : CompactSpace (mixedPolytope F.sig) :=
    isCompact_iff_compactSpace.mp (isCompact_mixedPolytope F.sig)
  exact (isClosed_mixedNashPolytopeSet utility).isCompact

/-- The exact mixed-Nash carrier is nonempty for nonempty finite action sets. -/
theorem mixedNashPolytopeSet_nonempty
    [∀ who, Nonempty (F.sig.Strategy who)]
    (utility : F.sig.Outcome → ι → ℝ) :
    (mixedNashPolytopeSet utility).Nonempty := by
  obtain ⟨point, hpoint⟩ :=
    kakutani_fixed_point (mixedPolytope F.sig) (convex_mixedPolytope F.sig)
      (isCompact_mixedPolytope F.sig) (mixedPolytope_nonempty F.sig)
      (fun x => bestReplies F utility x.1) (closedGraph_bestReplies utility)
      (fun x => ⟨bestReplies_subset utility x.1, convex_bestReplies utility x.1,
        bestReplies_nonempty utility x.1⟩)
  exact ⟨point, hpoint⟩

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
