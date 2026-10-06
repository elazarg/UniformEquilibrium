import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Topology.NhdsWithin
import Mathlib.Topology.Constructions
import Mathlib.Order.Filter.Finite
import Mathlib.Tactic.Linarith

/-! # Pasting maps on a shrinking family of closed patches

This is the continuity argument in Fischer--Zastrow, *The fundamental groups
of subsets of closed surfaces inject into their first shape groups*, Theorem 15,
final proof paragraph (Algebraic & Geometric Topology 5 (2005), p. 1665).
https://msp.org/agt/2005/5-4/agt-v5-n4-p18-s.pdf

There may be infinitely many patches accumulating at a fixed point. A finite
exceptional family is controlled by continuity and closedness; all other patches
have small displacement because the map preserves them. No local finiteness,
disjointness or compactness is assumed. This does not construct the planar disks
or component retractions, and does not prove Sorin's Proposition 11.
-/

namespace Math.Topology

open Set Filter
open scoped _root_.Topology

/-- A patch-preserving map which is the identity off the patch interiors is
continuous when its closed patches form a null family and its restriction to
each patch is continuous. The auxiliary parameter space is arbitrary. -/
theorem continuous_of_null_closed_patches
    {X T ι : Type*} [PseudoMetricSpace X] [TopologicalSpace T]
    (patch : ι → Set X) (map : X × T → X)
    (hclosed : ∀ i, IsClosed (patch i))
    (hcontinuous : ∀ i, ContinuousOn map (patch i ×ˢ (Set.univ : Set T)))
    (hfixed : ∀ point : X × T,
      (∀ i, point.1 ∉ interior (patch i)) → map point = point.1)
    (hpreserves : ∀ i (point : X × T), point.1 ∈ patch i → map point ∈ patch i)
    (hnull : ∀ ε : ℝ, 0 < ε → ∃ exceptional : Finset ι,
      ∀ i ∉ exceptional, ∀ x ∈ patch i, ∀ y ∈ patch i, dist x y < ε) :
    Continuous map := by
  classical
  apply continuous_iff_continuousAt.mpr
  intro point
  by_cases hinterior : ∃ i, point.1 ∈ interior (patch i)
  · obtain ⟨i, hi⟩ := hinterior
    apply (hcontinuous i point ⟨interior_subset hi, Set.mem_univ _⟩).continuousAt
    have hneighborhood : patch i ∈ 𝓝 point.1 := mem_interior_iff_mem_nhds.mp hi
    exact Filter.mem_of_superset
      (continuous_fst.continuousAt.preimage_mem_nhds hneighborhood)
      (fun _ h => ⟨h, Set.mem_univ _⟩)
  · have hpoint : map point = point.1 := hfixed point (not_exists.mp hinterior)
    apply Metric.continuousAt_iff'.mpr
    intro ε hε
    obtain ⟨exceptional, hsmall⟩ := hnull (ε / 2) (half_pos hε)
    have hfinite : ∀ᶠ other in 𝓝 point, ∀ i ∈ exceptional,
        other.1 ∈ patch i → dist (map other) (map point) < ε := by
      apply exceptional.eventually_all.mpr
      intro i _hi
      by_cases hmem : point.1 ∈ patch i
      · have hwithin := Metric.continuousWithinAt_iff'.mp
          (hcontinuous i point ⟨hmem, Set.mem_univ _⟩) ε hε
        filter_upwards [eventually_nhdsWithin_iff.mp hwithin] with other hother hmemOther
        exact hother ⟨hmemOther, Set.mem_univ _⟩
      · have houtside : ∀ᶠ other in 𝓝 point, other.1 ∉ patch i :=
          continuous_fst.continuousAt.preimage_mem_nhds
            ((hclosed i).isOpen_compl.mem_nhds hmem)
        filter_upwards [houtside] with other hother hmemOther
        exact (hother hmemOther).elim
    have hnear : ∀ᶠ other : X × T in 𝓝 point, dist other.1 point.1 < ε / 2 :=
      Metric.continuousAt_iff'.mp continuous_fst.continuousAt (ε / 2) (half_pos hε)
    filter_upwards [hfinite, hnear] with other hother hdist
    by_cases hpatch : ∃ i, other.1 ∈ patch i
    · obtain ⟨i, hi⟩ := hpatch
      by_cases hexceptional : i ∈ exceptional
      · exact hother i hexceptional hi
      · rw [hpoint]
        exact (dist_triangle (map other) other.1 point.1).trans_lt
          (by have hmove := hsmall i hexceptional (map other)
                (hpreserves i other hi) other.1 hi
              linarith)
    · have hotherFixed : map other = other.1 := hfixed other (by
        intro i hi
        exact hpatch ⟨i, interior_subset hi⟩)
      rw [hpoint, hotherFixed]
      exact hdist.trans (half_lt_self hε)

end Math.Topology
