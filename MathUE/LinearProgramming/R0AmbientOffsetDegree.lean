import MathUE.LinearProgramming.R0AmbientDegree
import MathUE.Topology.AmbientDegreeHomotopyNormalization

/-!
# Intrinsic total degree for bounded-offset minimum maps

The existing R0 bound/homotopy theorem constructs one scalar chart and an
inner bounded open ambient box containing every zero for every bounded
offset. The intrinsic operation in that actual source computes the same
R0 integer. Offset minus one is included by the literal unit bound.
No finite or regular root hypothesis or supplied degree equality is added.
-/

noncomputable section

namespace Math.LinearProgramming

open Set Math.Topology

variable {n : ℕ}

/-- One sufficiently large actual ambient source computes the total intrinsic
degree of every bounded-offset minimum map and contains its entire zero fiber. -/
theorem exists_radius_above_ambientDegree_lcpMinMap_eq_r0Degree
    (matrix : Matrix (Fin n) (Fin n) ℝ) (hR0 : IsR0Matrix matrix)
    (bound minimumRadius : ℝ) :
    ∃ (radius : ℝ) (_hradius : 0 < radius), minimumRadius < radius ∧
      ∀ offset : Fin n → ℝ, (∀ who, |offset who| ≤ bound) →
      ∃ hfrontier : ∀ point ∈ frontier (Math.affineRootRegion 0 radius),
        lcpMinMap matrix offset point ≠ 0,
        (∀ point, lcpMinMap matrix offset point = 0 →
          point ∈ Math.affineRootRegion 0 radius) ∧
        ambientDegree (lcpMinMap matrix offset) (Math.affineRootRegion 0 radius) 0
          (isOpen_affineRootRegion 0 radius) (isBounded_affineRootRegion 0 radius)
          (continuous_lcpMinMap matrix offset).continuousOn hfrontier = r0Degree matrix hR0 := by
  obtain ⟨radius, hradius, habove, hfamily⟩ :=
    exists_radius_above_lcpMinBoxProblem_localDegree_eq_r0Degree
      matrix hR0 bound minimumRadius
  refine ⟨radius, hradius, habove, ?_⟩
  intro offset hoffset
  obtain ⟨hisolating, hbound, hlocal⟩ := hfamily offset hoffset
  have hzerosInside (point : Fin n → ℝ) (hzero : lcpMinMap matrix offset point = 0) :
      point ∈ Math.affineRootRegion 0 radius := by
    have hroot := (lcpMinMap_eq_zero_iff matrix offset point).mp hzero
    intro who
    have hupper := hbound point hroot who
    have hnonneg := hroot.weight_nonneg who
    change 0 - radius / 2 < point who ∧ point who < 0 + radius / 2
    constructor <;> linarith
  have hfrontier : ∀ point ∈ frontier (Math.affineRootRegion 0 radius),
      lcpMinMap matrix offset point ≠ 0 := by
    intro point hpoint hzero
    have hin := hzerosInside point hzero
    exact hpoint.2 (by
      simpa only [(isOpen_affineRootRegion 0 radius).interior_eq] using hin)
  have hwidth : ∀ _ : Fin n, -radius < radius := by intro _; linarith
  have hclosure : closure (Math.affineRootRegion (0 : Fin n → ℝ) radius) ⊆
      {point | ∀ who, -radius < point who ∧ point who < radius} := by
    simpa only [Pi.zero_apply, zero_sub, zero_add] using
      closure_affineRootRegion_subset (0 : Fin n → ℝ) hradius
  have hpreimage : rectangularCubePoint (fun _ : Fin n => -radius) (fun _ => radius) ⁻¹'
      Math.affineRootRegion 0 radius = diagonalCentralRegion n := by
    simpa only [Pi.zero_apply, zero_sub, zero_add] using
      Math.preimage_affineRootRegion (0 : Fin n → ℝ) hradius
  have hcomputed := ambientDegree_eq_of_extension (lcpMinMap matrix offset)
    (Math.affineRootRegion 0 radius) 0
    (isOpen_affineRootRegion 0 radius) (isBounded_affineRootRegion 0 radius)
    (continuous_lcpMinMap matrix offset).continuousOn hfrontier
    (fun _ => -radius) (fun _ => radius) hwidth hclosure (lcpMinMap matrix offset)
    (continuous_lcpMinMap matrix offset).continuousOn (fun _ _ => rfl)
  refine ⟨hfrontier, hzerosInside, ?_⟩
  have hactual :
      ambientDegree (lcpMinMap matrix offset) (Math.affineRootRegion 0 radius) 0
        (isOpen_affineRootRegion 0 radius) (isBounded_affineRootRegion 0 radius)
        (continuous_lcpMinMap matrix offset).continuousOn hfrontier =
      (lcpMinBoxProblem matrix offset 0 radius hradius).localDegree
        (diagonalCentralRegion n) hisolating := by
    simpa only [sub_zero, hpreimage, lcpMinBoxProblem,
      Pi.zero_apply, zero_sub, zero_add] using hcomputed
  exact hactual.trans hlocal

/-- In particular the packet's literal offset minus one has the intrinsic R0
total degree on a constructed sufficiently large bounded open source. -/
theorem exists_radius_ambientDegree_lcpMinMap_neg_one_eq_r0Degree
    (matrix : Matrix (Fin n) (Fin n) ℝ) (hR0 : IsR0Matrix matrix) (minimumRadius : ℝ) :
    ∃ (radius : ℝ) (_hradius : 0 < radius), minimumRadius < radius ∧
      ∃ hfrontier : ∀ point ∈ frontier (Math.affineRootRegion 0 radius),
        lcpMinMap matrix (fun _ => -1) point ≠ 0,
        (∀ point, lcpMinMap matrix (fun _ => -1) point = 0 →
          point ∈ Math.affineRootRegion 0 radius) ∧
        ambientDegree (lcpMinMap matrix (fun _ => -1)) (Math.affineRootRegion 0 radius) 0
          (isOpen_affineRootRegion 0 radius) (isBounded_affineRootRegion 0 radius)
          (continuous_lcpMinMap matrix (fun _ => -1)).continuousOn hfrontier =
            r0Degree matrix hR0 := by
  obtain ⟨radius, hradius, habove, hall⟩ :=
    exists_radius_above_ambientDegree_lcpMinMap_eq_r0Degree matrix hR0 1 minimumRadius
  exact ⟨radius, hradius, habove, hall (fun _ => -1) (by intro _; norm_num)⟩

end Math.LinearProgramming
