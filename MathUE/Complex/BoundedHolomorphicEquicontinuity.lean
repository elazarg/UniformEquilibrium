/-
Copyright (c) 2026 Yury Kudryashov. All rights reserved.
Released under Apache-2.0; see LICENSES/APACHE_2_0.txt.
Authors: Yury Kudryashov

Adapted from the bounded-family equicontinuity proofs in
https://github.com/urkud/mathlib4/tree/d43061d911b1aeae0788591da437a3b115098962
under Mathlib/Analysis/Complex/RiemannMapping.lean (PR33505).
-/
module

public import Mathlib.Analysis.Complex.Schwarz
public import Mathlib.Topology.UniformSpace.Equicontinuity

/-! # Equicontinuity of uniformly bounded holomorphic families

The actual Schwarz estimate controls displacement uniformly in the family.
Both source and target may be arbitrary complex normed spaces; no completeness
or finite-dimensionality is required.
-/

public section

namespace Math.ComplexAnalysis

open Set Metric Filter
open scoped _root_.Topology

theorem uniformEquicontinuousOn_of_thickening_subset_of_forall_norm_le
    {ι E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    {family : ι → E → F} {s U : Set E} {radius : ℝ}
    (hradius : 0 < radius) (hthickening : thickening radius s ⊆ U)
    (hanalytic : ∀ i, DifferentiableOn ℂ (family i) U)
    (hbound : ∃ bound, ∀ i, ∀ z ∈ U, ‖family i z‖ ≤ bound) :
    UniformEquicontinuousOn family s := by
  have hsubset : s ⊆ U := (self_subset_thickening hradius s).trans hthickening
  rw [(uniformity_basis_dist.inf_principal (s ×ˢ s)).uniformEquicontinuousOn_iff
    uniformity_basis_dist_le]
  intro ε hε
  obtain ⟨bound, hbound⟩ := hbound
  obtain ⟨δ, hδ, hδbound⟩ := exists_pos_mul_lt hε (2 * bound / radius)
  refine ⟨min δ radius, by positivity, ?_⟩
  simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, prodMk_mem_set_prod_eq]
  rintro x y ⟨hdist, hx, hy⟩ i
  rw [lt_min_iff] at hdist
  rw [thickening_eq_biUnion_ball, iUnion₂_subset_iff] at hthickening
  calc
    dist (family i x) (family i y) ≤ (2 * bound / radius) * dist x y := by
      apply Complex.dist_le_div_mul_dist_of_mapsTo_ball
      · exact (hanalytic i).mono (hthickening y hy)
      · intro z hz
        rw [mem_closedBall, two_mul]
        exact (dist_le_norm_add_norm _ _).trans
          (add_le_add (hbound i z (hthickening y hy hz)) (hbound i y (hsubset hy)))
      · exact hdist.2
    _ ≤ ε := by
      grw [hdist.1]
      · exact hδbound.le
      · have hnonnegative := (norm_nonneg (family i x)).trans (hbound i x (hsubset hx))
        positivity

theorem equicontinuousAt_of_forall_norm_le
    {ι E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    {family : ι → E → F} {U : Set E} {point : E} (hU : U ∈ 𝓝 point)
    (hanalytic : ∀ i, DifferentiableOn ℂ (family i) U)
    (hbound : ∃ bound, ∀ i, ∀ z ∈ U, ‖family i z‖ ≤ bound) :
    EquicontinuousAt family point := by
  obtain ⟨radius, hradius, hball⟩ := nhds_basis_ball.mem_iff.mp hU
  have hthickening : thickening (radius / 2) (ball point (radius / 2)) ⊆ U := by
    grw [Metric.thickening_ball]
    rwa [add_halves]
  have hwithin :=
    (uniformEquicontinuousOn_of_thickening_subset_of_forall_norm_le
      (by positivity) hthickening hanalytic hbound).equicontinuousOn point (by simpa)
  rwa [EquicontinuousWithinAt,
    nhdsWithin_eq_nhds.mpr (ball_mem_nhds point (by positivity))] at hwithin

end Math.ComplexAnalysis
