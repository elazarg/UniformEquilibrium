/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.Order.ProjIcc
import FixedPointTheorems.brouwer

/-!
# Poincare--Miranda on a finite cube

A continuous finite-coordinate map whose coordinates point inward on the two
opposite faces has a zero in the unit cube.  Strict inward-pointing on one or
both families of faces locates the zero in the corresponding open faces.

The proof is the standard Brouwer reduction: add the vector field and project
each coordinate back to `[0, 1]`.
-/

noncomputable section

open Set

namespace Math
namespace Topology

variable {ι : Type*} [Fintype ι]

/-- **Poincare--Miranda on the unit cube.** If every coordinate of a
continuous vector field is nonnegative on its lower face and nonpositive on
its upper face, then the field vanishes somewhere in the cube. -/
theorem exists_cube_zero_of_opposite_face_signs
    (F : (ι → ℝ) → ι → ℝ) (hF : Continuous F)
    (hlower : ∀ x ∈ Icc (fun _ => 0) (fun _ => 1), ∀ i,
      x i = 0 → 0 ≤ F x i)
    (hupper : ∀ x ∈ Icc (fun _ => 0) (fun _ => 1), ∀ i,
      x i = 1 → F x i ≤ 0) :
    ∃ x ∈ Icc (fun _ => 0) (fun _ => 1), ∀ i, F x i = 0 := by
  classical
  let cube : Set (ι → ℝ) := Icc (fun _ => 0) (fun _ => 1)
  have hcubeConvex : Convex ℝ cube := convex_Icc _ _
  have hcubeCompact : IsCompact cube := isCompact_Icc
  have hzeroMem : (fun _ : ι => (0 : ℝ)) ∈ cube := by
    change (fun _ : ι => (0 : ℝ)) ∈
      Icc (fun _ => 0) (fun _ => 1)
    exact ⟨fun _ => le_rfl, fun _ => zero_le_one⟩
  have hcubeNonempty : cube.Nonempty := ⟨_, hzeroMem⟩
  let project : cube → cube := fun x =>
    ⟨fun i => Set.projIcc 0 1 zero_le_one (x.1 i + F x.1 i),
      by
        change (fun i =>
          (Set.projIcc 0 1 zero_le_one (x.1 i + F x.1 i) : ℝ)) ∈
            Icc (fun _ => 0) (fun _ => 1)
        exact
          ⟨fun i => (Set.projIcc 0 1 zero_le_one (x.1 i + F x.1 i)).2.1,
            fun i => (Set.projIcc 0 1 zero_le_one (x.1 i + F x.1 i)).2.2⟩⟩
  have hproject : Continuous project := by
    refine continuous_induced_rng.2 (continuous_pi fun i => ?_)
    exact continuous_subtype_val.comp (continuous_projIcc.comp
      (((continuous_apply i).comp continuous_subtype_val).add
        ((continuous_apply i).comp (hF.comp continuous_subtype_val))))
  obtain ⟨x, hx⟩ :=
    brouwer_fixed_point cube hcubeConvex hcubeCompact hcubeNonempty
      ⟨project, hproject⟩
  have hcoordinate : ∀ i,
      Set.projIcc 0 1 zero_le_one (x.1 i + F x.1 i) = x.1 i := by
    intro i
    exact congrFun (congrArg Subtype.val hx) i
  refine ⟨x.1, x.2, fun i => ?_⟩
  by_cases hzero : x.1 i = 0
  · have hle : x.1 i + F x.1 i ≤ 0 := by
      exact (Set.projIcc_eq_left zero_lt_one).mp (by
        simpa [hzero] using hcoordinate i)
    have hnonneg := hlower x.1 x.2 i hzero
    linarith
  by_cases hone : x.1 i = 1
  · have hge : 1 ≤ x.1 i + F x.1 i := by
      exact (Set.projIcc_eq_right zero_lt_one).mp (by
        simpa [hone] using hcoordinate i)
    have hnonpos := hupper x.1 x.2 i hone
    linarith
  have hxpos : 0 < x.1 i := lt_of_le_of_ne (x.2.1 i) (Ne.symm hzero)
  have hxlt : x.1 i < 1 := lt_of_le_of_ne (x.2.2 i) hone
  have hsumPos : 0 < x.1 i + F x.1 i := by
    by_contra hnot
    have hproj := Set.projIcc_of_le_left zero_le_one (le_of_not_gt hnot)
    have hc := hcoordinate i
    rw [congrArg Subtype.val hproj] at hc
    exact (ne_of_gt hxpos) hc.symm
  have hsumLt : x.1 i + F x.1 i < 1 := by
    by_contra hnot
    have hproj := Set.projIcc_of_right_le zero_le_one (le_of_not_gt hnot)
    have hc := hcoordinate i
    rw [congrArg Subtype.val hproj] at hc
    exact (ne_of_lt hxlt) hc.symm
  have hproj := Set.projIcc_of_mem zero_le_one ⟨hsumPos.le, hsumLt.le⟩
  have hc := hcoordinate i
  rw [congrArg Subtype.val hproj] at hc
  linarith

/-- Strict lower-face signs force every coordinate of the Poincare--Miranda
zero to be positive. -/
theorem exists_cube_zero_pos_of_opposite_face_signs
    (F : (ι → ℝ) → ι → ℝ) (hF : Continuous F)
    (hlower : ∀ x ∈ Icc (fun _ => 0) (fun _ => 1), ∀ i,
      x i = 0 → 0 < F x i)
    (hupper : ∀ x ∈ Icc (fun _ => 0) (fun _ => 1), ∀ i,
      x i = 1 → F x i ≤ 0) :
    ∃ x ∈ Icc (fun _ => 0) (fun _ => 1),
      (∀ i, 0 < x i) ∧ ∀ i, F x i = 0 := by
  obtain ⟨x, hx, hzero⟩ := exists_cube_zero_of_opposite_face_signs F hF
    (fun y hy i hi => (hlower y hy i hi).le) hupper
  refine ⟨x, hx, ?_, hzero⟩
  intro i
  exact lt_of_le_of_ne (hx.1 i) fun hi =>
    (hlower x hx i hi.symm).ne' (hzero i)

/-- Strict signs on both families of faces force an interior zero. -/
theorem exists_cube_zero_interior_of_strict_opposite_face_signs
    (F : (ι → ℝ) → ι → ℝ) (hF : Continuous F)
    (hlower : ∀ x ∈ Icc (fun _ => 0) (fun _ => 1), ∀ i,
      x i = 0 → 0 < F x i)
    (hupper : ∀ x ∈ Icc (fun _ => 0) (fun _ => 1), ∀ i,
      x i = 1 → F x i < 0) :
    ∃ x ∈ Icc (fun _ => 0) (fun _ => 1),
      (∀ i, 0 < x i ∧ x i < 1) ∧ ∀ i, F x i = 0 := by
  obtain ⟨x, hx, hxpos, hzero⟩ :=
    exists_cube_zero_pos_of_opposite_face_signs F hF hlower
      (fun y hy i hi => (hupper y hy i hi).le)
  refine ⟨x, hx, fun i => ⟨hxpos i, ?_⟩, hzero⟩
  exact lt_of_le_of_ne (hx.2 i) fun hi =>
    (hupper x hx i hi).ne (hzero i)

end Topology
end Math
