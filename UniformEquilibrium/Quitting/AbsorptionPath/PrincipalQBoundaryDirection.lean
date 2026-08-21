/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.AbsorptionPath.PrincipalQDirection

/-!
# Principal-Q directions on the nonnegative boundary

The face direction supplied by a principal projective-Q hypothesis extends by
zero to the ambient coordinate simplex.  Its matrix residual points inward at
every zero coordinate and is tangent at at least one zero coordinate.  This is
the finite-dimensional tangency input to the viability step for continuous
absorption paths.
-/

noncomputable section

namespace GameTheory.QuittingLCPClassification

open Finset Math.LinearProgramming Set
open scoped Topology

/-- The boundary of the nonnegative orthant, in coordinate form. -/
def IsNonnegativeBoundary {ι : Type} (q : ι → ℝ) : Prop :=
  (∀ i, 0 ≤ q i) ∧ ∃ i, q i = 0

/-- The zero coordinates of a vector. -/
def zeroCoordinates {ι : Type} [Fintype ι] [DecidableEq ι]
    (q : ι → ℝ) : Finset ι :=
  Finset.univ.filter fun i => q i = 0

private theorem zeroCoordinates_nonempty
    {ι : Type} [Fintype ι] [DecidableEq ι] {q : ι → ℝ}
    (hq : IsNonnegativeBoundary q) : (zeroCoordinates q).Nonempty := by
  obtain ⟨i, hi⟩ := hq.2
  exact ⟨i, by simp [zeroCoordinates, hi]⟩

private theorem map_subtype_val_apply
    {ι : Type} [Fintype ι] [DecidableEq ι]
    {players : Finset ι} (weight : stdSimplex ℝ players) (i : ι) :
    stdSimplex.map Subtype.val weight i =
      if hi : i ∈ players then weight ⟨i, hi⟩ else 0 := by
  classical
  rw [stdSimplex.map_coe, FunOnFinite.linearMap_apply_apply]
  by_cases hi : i ∈ players
  · rw [dif_pos hi]
    refine Finset.sum_eq_single
      (s := Finset.univ.filter fun player : players => player.1 = i)
      ⟨i, hi⟩ ?_ ?_
    · intro other hother hne
      have heq : other = ⟨i, hi⟩ := by
        apply Subtype.ext
        exact (Finset.mem_filter.mp hother).2
      exact (hne heq).elim
    · intro hnot
      exact (hnot (by simp)).elim
  · rw [dif_neg hi]
    apply Finset.sum_eq_zero
    intro player hplayer
    have heq : player.1 = i := (Finset.mem_filter.mp hplayer).2
    exact (hi (heq ▸ player.property)).elim

/-- An ambient simplex direction supported on the zero face of `q`, pointing
inward there and tangent in at least one zero coordinate. -/
structure NonnegativeBoundaryDirection {ι : Type} [Fintype ι]
    (M : ι → ι → ℝ) (q : ι → ℝ) where
  weight : stdSimplex ℝ ι
  supported_on_zero : ∀ i, weight i ≠ 0 → q i = 0
  residual_nonneg_on_zero : ∀ i, q i = 0 →
    0 ≤ singletonLCPResidual M weight i
  residual_zero_on_zero : ∃ i, q i = 0 ∧
    singletonLCPResidual M weight i = 0

/-- Complete projective-Q control on principal faces supplies an inward,
tangent simplex direction at every point of the nonnegative boundary. -/
theorem exists_nonnegativeBoundaryDirection
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (M : ι → ι → ℝ) (hdiag : ∀ i, M i i = 0)
    (hQ : IsProjectiveQBarMatrix M) (q : ι → ℝ)
    (hq : IsNonnegativeBoundary q) :
    Nonempty (NonnegativeBoundaryDirection M q) := by
  let players := zeroCoordinates q
  have hplayers : players.Nonempty := zeroCoordinates_nonempty hq
  obtain ⟨direction⟩ :=
    exists_principalQDirection M hdiag players hplayers (hQ players hplayers)
  let weight : stdSimplex ℝ ι := stdSimplex.map Subtype.val direction.weight
  have hweight (i : ι) : weight i =
      if hi : i ∈ players then direction.weight ⟨i, hi⟩ else 0 := by
    exact map_subtype_val_apply direction.weight i
  have hresidual (i : ι) (hi : i ∈ players) :
      singletonLCPResidual M weight i =
        singletonLCPResidual (principalMatrix M players)
          direction.weight ⟨i, hi⟩ := by
    change (∑ owner, weight owner * M i owner) =
      ∑ owner : players, direction.weight owner * M i owner
    calc
      (∑ owner, weight owner * M i owner) =
          ∑ owner ∈ players, weight owner * M i owner := by
        symm
        apply Finset.sum_subset (Finset.subset_univ players)
        intro owner _ hnotmem
        rw [hweight]
        simp [hnotmem]
      _ = ∑ owner : players,
          direction.weight owner * M i owner := by
        rw [← Finset.sum_attach players]
        apply Finset.sum_congr rfl
        intro owner _
        rw [hweight]
        simp
  refine ⟨⟨weight, ?_, ?_, ?_⟩⟩
  · intro i hi
    rw [hweight] at hi
    split at hi
    · simpa [players, zeroCoordinates] using ‹i ∈ players›
    · exact (hi rfl).elim
  · intro i hi
    have hip : i ∈ players := by simp [players, zeroCoordinates, hi]
    rw [hresidual i hip]
    exact direction.residual_nonneg ⟨i, hip⟩
  · obtain ⟨who, hzero⟩ := direction.residual_zero
    refine ⟨who.1, ?_, ?_⟩
    · have := who.property
      simpa only [players, zeroCoordinates, Finset.mem_filter,
        Finset.mem_univ, true_and] using this
    · rw [hresidual who.1 who.property]
      exact hzero

/-- An inward tangent direction admits a strictly positive Euler step that
stays on the boundary.  The step is a convex combination of the current
boundary point and the direction's matrix residual. -/
theorem NonnegativeBoundaryDirection.exists_boundary_step
    {ι : Type} [Fintype ι] [DecidableEq ι]
    {M : ι → ι → ℝ} {q : ι → ℝ}
    (direction : NonnegativeBoundaryDirection M q)
    (hq : IsNonnegativeBoundary q) {stepBound : ℝ} (hstepBound : 0 < stepBound) :
    ∃ α : ℝ, 0 < α ∧ α < stepBound ∧ α < 1 ∧
      IsNonnegativeBoundary (fun i =>
        (1 - α) * q i + α * singletonLCPResidual M direction.weight i) := by
  let residual : ι → ℝ := fun i =>
    singletonLCPResidual M direction.weight i
  have hevent (i : ι) : ∀ᶠ α : ℝ in nhdsWithin 0 (Ioi 0),
      0 ≤ (1 - α) * q i + α * residual i := by
    by_cases hi : q i = 0
    · filter_upwards [self_mem_nhdsWithin] with α hα
      simp only [hi, mul_zero, zero_add]
      exact mul_nonneg hα.le (direction.residual_nonneg_on_zero i hi)
    · have hqi : 0 < q i := lt_of_le_of_ne (hq.1 i) (Ne.symm hi)
      have hcontinuous : ContinuousAt
          (fun α : ℝ => (1 - α) * q i + α * residual i) 0 := by
        fun_prop
      have hatZero : 0 < (1 - (0 : ℝ)) * q i + 0 * residual i := by
        simpa using hqi
      have hpositive : ∀ᶠ α : ℝ in 𝓝 0,
          0 < (1 - α) * q i + α * residual i :=
        hcontinuous.tendsto (eventually_gt_nhds hatZero)
      exact (hpositive.filter_mono inf_le_left).mono fun _ h => h.le
  have hall : ∀ᶠ α : ℝ in nhdsWithin 0 (Ioi 0), ∀ i,
      0 ≤ (1 - α) * q i + α * residual i :=
    ((Filter.eventually_all_finite Set.finite_univ).2
      fun i _ => hevent i).mono fun _ h i => h i (Set.mem_univ i)
  have hlt : ∀ᶠ α : ℝ in nhdsWithin 0 (Ioi 0), α < 1 :=
    (eventually_lt_nhds zero_lt_one).filter_mono inf_le_left
  have hpos : ∀ᶠ α : ℝ in nhdsWithin 0 (Ioi 0), 0 < α :=
    self_mem_nhdsWithin
  have hbound : ∀ᶠ α : ℝ in nhdsWithin 0 (Ioi 0), α < stepBound :=
    (eventually_lt_nhds hstepBound).filter_mono inf_le_left
  obtain ⟨α, hα, hαlt, hαbound, hαpos⟩ :=
    (hall.and (hlt.and (hbound.and hpos))).exists
  refine ⟨α, hαpos, hαbound, hαlt, hα, ?_⟩
  obtain ⟨i, hqi, hri⟩ := direction.residual_zero_on_zero
  refine ⟨i, ?_⟩
  change (1 - α) * q i +
    α * singletonLCPResidual M direction.weight i = 0
  rw [hqi, hri]
  ring

/-- The endpoint step can be chosen so that the entire affine segment up to
it remains on the nonnegative boundary. This is the local polygonal arc used
by adaptive Euler constructions, not merely a feasible endpoint. -/
theorem NonnegativeBoundaryDirection.exists_boundary_segment
    {ι : Type} [Fintype ι] [DecidableEq ι]
    {M : ι → ι → ℝ} {q : ι → ℝ}
    (direction : NonnegativeBoundaryDirection M q)
    (hq : IsNonnegativeBoundary q) {stepBound : ℝ} (hstepBound : 0 < stepBound) :
    ∃ α : ℝ, 0 < α ∧ α < stepBound ∧ α < 1 ∧
      ∀ β ∈ Set.Icc (0 : ℝ) α, IsNonnegativeBoundary (fun i =>
        (1 - β) * q i + β * singletonLCPResidual M direction.weight i) := by
  obtain ⟨α, hα, hαbound, hαone, hendpoint⟩ :=
    direction.exists_boundary_step hq hstepBound
  refine ⟨α, hα, hαbound, hαone, ?_⟩
  intro β hβ
  constructor
  · intro i
    change 0 ≤ (1 - β) * q i +
      β * singletonLCPResidual M direction.weight i
    let endpoint :=
      (1 - α) * q i + α * singletonLCPResidual M direction.weight i
    have hratioNonneg : 0 ≤ β / α := div_nonneg hβ.1 hα.le
    have hratioLe : β / α ≤ 1 := (div_le_one hα).2 hβ.2
    have hconvex : (1 - β / α) * q i + (β / α) * endpoint =
        (1 - β) * q i + β * singletonLCPResidual M direction.weight i := by
      dsimp [endpoint]
      field_simp [ne_of_gt hα]
      ring
    rw [← hconvex]
    exact add_nonneg
      (mul_nonneg (sub_nonneg.mpr hratioLe) (hq.1 i))
      (mul_nonneg hratioNonneg (hendpoint.1 i))
  · obtain ⟨i, hqi, hresidual⟩ := direction.residual_zero_on_zero
    refine ⟨i, ?_⟩
    change (1 - β) * q i +
      β * singletonLCPResidual M direction.weight i = 0
    rw [hqi, hresidual]
    ring

end GameTheory.QuittingLCPClassification
