import Mathlib.Analysis.Convex.Caratheodory
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Data.Fintype.EquivFin
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional

/-!
# Compact convex hulls in finite dimension

Carathéodory bounds the number of points in a convex combination. The hull is
therefore a finite union of continuous images of compact coefficient/point sets.
The original compact set need not be finite.
-/

open Set
open scoped BigOperators Topology

namespace Math.Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

private def combinationCoefficients (m : ℕ) : Set (Fin m → ℝ) :=
  Set.Icc 0 1 ∩ {weights | ∑ i, weights i = 1}

private def combinationImage (K : Set E) (m : ℕ) : Set E :=
  (fun pair : (Fin m → ℝ) × (Fin m → E) => ∑ i, pair.1 i • pair.2 i) ''
    (combinationCoefficients m ×ˢ Set.pi Set.univ (fun _ => K))

private theorem combinationImage_isCompact (K : Set E) (hK : IsCompact K) (m : ℕ) :
    IsCompact (combinationImage K m) := by
  have hweights : IsCompact (combinationCoefficients m) :=
    (isCompact_Icc : IsCompact (Set.Icc (0 : Fin m → ℝ) 1)).inter_right
      (isClosed_eq (continuous_finsetSum _ fun i _ => continuous_apply i) continuous_const)
  exact (hweights.prod (isCompact_univ_pi fun _ => hK)).image
    (continuous_finsetSum _ fun i _ =>
      ((continuous_apply i).comp continuous_fst).smul
        ((continuous_apply i).comp continuous_snd))

private theorem combinationImage_subset (K : Set E) (m : ℕ) :
    combinationImage K m ⊆ convexHull ℝ K := by
  rintro point ⟨⟨weights, points⟩, ⟨hweights, hpoints⟩, rfl⟩
  exact (convex_convexHull ℝ K).sum_mem
    (fun i _ => hweights.1.1 i) hweights.2
    (fun i _ => subset_convexHull ℝ K (hpoints i (Set.mem_univ i)))

variable [FiniteDimensional ℝ E]

/-- The convex hull of an arbitrary compact set in a finite-dimensional real
normed space is compact. In particular, the input need not be a finite set. -/
theorem isCompact_convexHull_of_finiteDimensional {K : Set E} (hK : IsCompact K) :
    IsCompact (convexHull ℝ K) := by
  classical
  let dimension := Module.finrank ℝ E
  have hhull : convexHull ℝ K =
      ⋃ m : Fin (dimension + 2), combinationImage K m.val := by
    apply Set.Subset.antisymm
    · intro point hpoint
      let t := Caratheodory.minCardFinsetOfMemConvexHull hpoint
      have htK : (t : Set E) ⊆ K :=
        Caratheodory.minCardFinsetOfMemConvexHull_subseteq hpoint
      have hind : AffineIndependent ℝ ((↑) : t → E) :=
        Caratheodory.affineIndependent_minCardFinsetOfMemConvexHull hpoint
      have hcard : t.card ≤ dimension + 1 := by
        have h := hind.card_le_finrank_succ.trans
          (Nat.add_le_add_right (Submodule.finrank_le _) 1)
        simpa only [Fintype.card_coe, dimension] using h
      obtain ⟨weights, hweights, hsum, hvalue⟩ :=
        Finset.mem_convexHull'.mp
          (Caratheodory.mem_minCardFinsetOfMemConvexHull hpoint)
      let e : t ≃ Fin t.card := t.equivFin
      let points : Fin t.card → E := fun i => (e.symm i : E)
      let weights' : Fin t.card → ℝ := fun i => weights (points i)
      have hsum' : ∑ i, weights' i = 1 := by
        calc
          ∑ i, weights' i = ∑ a : t, weights a := by
            simpa only [weights', points] using
              e.symm.sum_comp (fun a : t => weights (a : E))
          _ = ∑ a ∈ t, weights a := t.sum_coe_sort (fun a : E => weights a)
          _ = 1 := hsum
      have hvalue' : ∑ i, weights' i • points i = point := by
        calc
          ∑ i, weights' i • points i = ∑ a : t, weights a • (a : E) :=
            by simpa only [weights', points] using
              e.symm.sum_comp (fun a : t => weights (a : E) • (a : E))
          _ = ∑ a ∈ t, weights a • a :=
            t.sum_coe_sort (fun a : E => weights a • a)
          _ = point := hvalue
      refine Set.mem_iUnion.mpr ⟨⟨t.card, by omega⟩, ?_⟩
      refine ⟨(weights', points), ⟨⟨⟨?_, ?_⟩, hsum'⟩, ?_⟩, hvalue'⟩
      · intro i
        exact hweights _ (e.symm i).property
      · intro i
        change weights' i ≤ (1 : ℝ)
        have hle : weights' i ≤ ∑ j, weights' j :=
          Finset.single_le_sum (fun j _ => hweights _ (e.symm j).property)
            (Finset.mem_univ i)
        simpa only [hsum'] using hle
      · intro i _
        exact htK (e.symm i).property
    · refine Set.iUnion_subset fun m => combinationImage_subset K m.val
  rw [hhull]
  exact isCompact_iUnion fun m => combinationImage_isCompact K hK m.val

end Math.Topology
