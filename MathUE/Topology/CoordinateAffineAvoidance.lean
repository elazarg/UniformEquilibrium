import Mathlib.Topology.Baire.Lemmas
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic.Linarith

/-! # Avoiding coordinate-affine zero sets

A nonzero slope in one actual coordinate makes the nonzero locus dense.
Continuity supplies openness; finite intersections use the existing finite
open-dense intersection theorem, without multivariate polynomial theory.
-/

namespace Math.Topology

open Set

variable {ι : Type*} [DecidableEq ι]

theorem dense_nonzero_of_coordinate_affine
    (field : (ι → ℝ) → ℝ) (coordinate : ι) (slope : ℝ) (hslope : slope ≠ 0)
    (hvariation : ∀ point rate,
      field (Function.update point coordinate (point coordinate + rate)) =
        field point + slope * rate) :
    Dense {point | field point ≠ 0} := by
  rw [dense_iff_inter_open]
  rintro region hregion ⟨point, hpoint⟩
  by_cases hnonzero : field point ≠ 0
  · exact ⟨point, hpoint, hnonzero⟩
  have hzero : field point = 0 := not_ne_iff.mp hnonzero
  let path : ℝ → ι → ℝ :=
    fun rate => Function.update point coordinate (point coordinate + rate)
  have hpath : Continuous path := by
    apply continuous_pi
    intro who
    by_cases heq : who = coordinate
    · subst who
      have h : Continuous (fun rate : ℝ => point coordinate + rate) :=
        continuous_const.add continuous_id
      simpa only [path, Function.update_self] using h
    · simpa only [path, Function.update_of_ne heq] using
        (continuous_const : Continuous (fun _ : ℝ => point who))
  have hpathZero : path 0 = point := by
    simp [path]
  have hopen : IsOpen (path ⁻¹' region) := hregion.preimage hpath
  have hmem : (0 : ℝ) ∈ path ⁻¹' region := by
    simpa only [mem_preimage, hpathZero] using hpoint
  obtain ⟨radius, hpositive, hball⟩ := Metric.isOpen_iff.mp hopen 0 hmem
  have hsmall : radius / 2 ∈ Metric.ball (0 : ℝ) radius := by
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos (by linarith)]
    linarith
  refine ⟨path (radius / 2), hball hsmall, ?_⟩
  change field (Function.update point coordinate (point coordinate + radius / 2)) ≠ 0
  rw [hvariation, hzero, zero_add]
  exact mul_ne_zero hslope (ne_of_gt (by linarith))

omit [DecidableEq ι] in
theorem isOpen_nonzero_of_continuous
    (field : (ι → ℝ) → ℝ) (hfield : Continuous field) :
    IsOpen {point | field point ≠ 0} := by
  exact (isClosed_singleton.preimage hfield).isOpen_compl

theorem dense_iInter_nonzero_of_coordinate_affine
    {κ : Type*} [Finite κ] (field : κ → (ι → ℝ) → ℝ)
    (coordinate : κ → ι) (slope : κ → ℝ)
    (hcontinuous : ∀ index, Continuous (field index))
    (hslope : ∀ index, slope index ≠ 0)
    (hvariation : ∀ index point rate,
      field index (Function.update point (coordinate index) (point (coordinate index) + rate)) =
        field index point + slope index * rate) :
    Dense (⋂ index, {point | field index point ≠ 0}) := by
  rw [← sInter_range]
  apply (finite_range _).dense_sInter
  · rintro _ ⟨index, rfl⟩
    exact isOpen_nonzero_of_continuous _ (hcontinuous index)
  · rintro _ ⟨index, rfl⟩
    exact dense_nonzero_of_coordinate_affine _ _ _ (hslope index) (hvariation index)

end Math.Topology
