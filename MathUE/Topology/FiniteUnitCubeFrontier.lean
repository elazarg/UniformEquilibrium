import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.MetricSpace.Pseudo.Pi
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Topology.Order.Real
import Mathlib.Tactic.Linarith

/-!
# A frontier estimate inside a finite unit cube

A coordinate rectangle joining an inside and an outside point is preconnected.
If both endpoints lie in a sup-metric closed ball, the rectangle does too.
The existing connectedness theorem therefore supplies a frontier point in
that ball, without a new path or intermediate-value construction.
-/

namespace Math

open Set

/-- A finite unit-cube ball containing points on both sides of an open set
has its center in the corresponding closed frontier thickening. -/
theorem mem_cthickening_frontier_of_unitCube_endpoints
    {ι : Type*} [Fintype ι]
    (region : Set (ι → Set.Icc (0 : ℝ) 1)) (hopen : IsOpen region)
    (center first second : ι → Set.Icc (0 : ℝ) 1) (radius : ℝ)
    (hfirst : first ∈ region) (hsecond : second ∉ region)
    (hfirstDist : dist center first ≤ radius) (hsecondDist : dist center second ≤ radius) :
    center ∈ Metric.cthickening radius (frontier region) := by
  classical
  let rectangle : Set (ι → Set.Icc (0 : ℝ) 1) := Set.univ.pi
    (fun coordinate => Set.Icc (min (first coordinate) (second coordinate))
      (max (first coordinate) (second coordinate)))
  have hconnected : IsPreconnected rectangle :=
    isPreconnected_univ_pi (fun _ => isPreconnected_Icc)
  have hfirstRect : first ∈ rectangle := by
    intro coordinate _
    exact ⟨min_le_left _ _, le_max_left _ _⟩
  have hsecondRect : second ∈ rectangle := by
    intro coordinate _
    exact ⟨min_le_right _ _, le_max_right _ _⟩
  have hcrossing : ∃ point ∈ rectangle, point ∈ frontier region := by
    by_contra hfailure
    push Not at hfailure
    have hsubset : rectangle ⊆ region :=
      hconnected.subset_of_closure_inter_subset hopen ⟨first, hfirstRect, hfirst⟩ (by
        intro point hpoint
        by_contra hout
        apply hfailure point hpoint.2
        exact ⟨hpoint.1, by simpa only [hopen.interior_eq] using hout⟩)
    exact hsecond (hsubset hsecondRect)
  obtain ⟨point, hpointRect, hpointFrontier⟩ := hcrossing
  apply Metric.mem_cthickening_of_dist_le center point radius (frontier region) hpointFrontier
  have hradius : 0 ≤ radius := dist_nonneg.trans hfirstDist
  rw [dist_pi_le_iff hradius] at hfirstDist hsecondDist ⊢
  intro coordinate
  have hbounds := hpointRect coordinate (Set.mem_univ coordinate)
  have hfirstCoordinate := hfirstDist coordinate
  have hsecondCoordinate := hsecondDist coordinate
  change |(center coordinate : ℝ) - (first coordinate : ℝ)| ≤ radius at hfirstCoordinate
  change |(center coordinate : ℝ) - (second coordinate : ℝ)| ≤ radius at hsecondCoordinate
  change |(center coordinate : ℝ) - (point coordinate : ℝ)| ≤ radius
  rw [abs_le] at hfirstCoordinate hsecondCoordinate ⊢
  have hlow : min (first coordinate : ℝ) (second coordinate : ℝ) ≤
      (point coordinate : ℝ) := hbounds.1
  have hhigh : (point coordinate : ℝ) ≤
      max (first coordinate : ℝ) (second coordinate : ℝ) := hbounds.2
  rcases le_total (first coordinate : ℝ) (second coordinate : ℝ) with horder | horder
  · rw [min_eq_left horder] at hlow
    rw [max_eq_right horder] at hhigh
    constructor <;> linarith
  · rw [min_eq_right horder] at hlow
    rw [max_eq_left horder] at hhigh
    constructor <;> linarith

end Math
