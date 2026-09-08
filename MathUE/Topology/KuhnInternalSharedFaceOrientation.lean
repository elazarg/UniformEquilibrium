import MathUE.Topology.OrientedSimplexFacetDeterminant
import MathUE.Topology.KuhnSimplexGeometry

/-!
# Opposite orientations at an internal Kuhn deletion

The pinned cumulative coordinate-change count identifies each step of an
actual top-dimensional Kuhn simplex as one unit coordinate increment. Two
distinct parents with the same internal deletion therefore exchange the two
increments surrounding that deletion. Their actual missing vertices are
reflected across the common neighboring vertices, so the inherited signed
facet determinants cancel. Unit-volume normalization is not asserted here.
-/

noncomputable section

namespace Math.KuhnSharedFace

open OrientedSimplexFacet

/-- The missing vertices of two distinct actual internal-deletion parents are
reflected across the two common neighboring vertices. -/
theorem internalParents_missingVertex_reflection
    (cube : SpernerCube) (lower upper : Fin (cube.n + 1) → cube.G)
    (hlower : simplex cube cube.n lower) (hupper : simplex cube cube.n upper)
    (before : Fin cube.n) (hbefore : before.val + 1 < cube.n)
    (hdistinct : lower ≠ upper)
    (hface : ∀ kept, lower (before.succ.succAbove kept) =
      upper (before.succ.succAbove kept)) :
    let after : Fin cube.n := ⟨before.val + 1, hbefore⟩
    (fun coordinate => ((lower before.succ coordinate).val : ℤ)) +
        (fun coordinate => ((upper before.succ coordinate).val : ℤ)) =
      (fun coordinate => ((lower before.castSucc coordinate).val : ℤ)) +
        (fun coordinate => ((lower after.succ coordinate).val : ℤ)) := by
  let after : Fin cube.n := ⟨before.val + 1, hbefore⟩
  have hmiddle : after.castSucc = before.succ := Fin.ext rfl
  have hafter : after.succ ≠ before.succ := by
    intro h
    have hvalue := congrArg Fin.val h
    simp only [Fin.val_succ, after] at hvalue
    omega
  have hequal_away (index : Fin (cube.n + 1)) (hne : index ≠ before.succ) :
      lower index = upper index := by
    obtain ⟨kept, hkept⟩ := Fin.exists_succAbove_eq hne
    rw [← hkept]
    exact hface kept
  have hleft := hequal_away before.castSucc (Fin.ne_of_lt before.castSucc_lt_succ)
  have hright := hequal_away after.succ hafter
  have hmissing : lower before.succ ≠ upper before.succ := by
    intro h
    apply hdistinct
    funext index
    by_cases heq : index = before.succ
    · simpa only [heq] using h
    · exact hequal_away index heq
  let firstAxis := spernerChainStep hlower rfl before
  have hfirst := KuhnSimplex.integerCoordinate_eq_add_stepIndicator hlower rfl before
  change ∀ coordinate, ((lower before.succ coordinate).val : ℤ) =
    ((lower before.castSucc coordinate).val : ℤ) +
      if coordinate = firstAxis then 1 else 0 at hfirst
  let secondAxis := spernerChainStep hupper rfl before
  have hsecond := KuhnSimplex.integerCoordinate_eq_add_stepIndicator hupper rfl before
  change ∀ coordinate, ((upper before.succ coordinate).val : ℤ) =
    ((upper before.castSucc coordinate).val : ℤ) +
      if coordinate = secondAxis then 1 else 0 at hsecond
  let lastAxis := spernerChainStep hlower rfl after
  have hlast := KuhnSimplex.integerCoordinate_eq_add_stepIndicator hlower rfl after
  change ∀ coordinate, ((lower after.succ coordinate).val : ℤ) =
    ((lower after.castSucc coordinate).val : ℤ) +
      if coordinate = lastAxis then 1 else 0 at hlast
  simp only [hmiddle] at hlast
  have haxes : firstAxis ≠ secondAxis := by
    intro heq
    apply hmissing
    funext coordinate
    apply Fin.ext
    have h1 := hfirst coordinate
    have h2 := hsecond coordinate
    rw [← hleft, ← heq] at h2
    exact_mod_cast h1.trans h2.symm
  have hlastAxis : lastAxis = secondAxis := by
    by_contra hne
    have h1 := hfirst secondAxis
    have h2 := hsecond secondAxis
    have h3 := hlast secondAxis
    have hmono := monotone_1_of_simplex cube upper hupper
      before.succ after.succ (by
        apply Fin.le_iff_val_le_val.mpr
        dsimp [after]
        omega) secondAxis
    have hmonoInt : ((upper before.succ secondAxis).val : ℤ) ≤
        ((upper after.succ secondAxis).val : ℤ) := by exact_mod_cast hmono
    rw [← hleft] at h2
    rw [← hright] at hmonoInt
    simp only [Ne.symm haxes, Ne.symm hne, if_false, if_true, add_zero] at h1 h2 h3
    omega
  funext coordinate
  have h1 := hfirst coordinate
  have h2 := hsecond coordinate
  have h3 := hlast coordinate
  rw [← hleft] at h2
  rw [hlastAxis] at h3
  simp only [Pi.add_apply]
  change ((lower before.succ coordinate).val : ℤ) +
      ((upper before.succ coordinate).val : ℤ) =
    ((lower before.castSucc coordinate).val : ℤ) + ((lower after.succ coordinate).val : ℤ)
  omega

/-- The two actual internal-deletion parents have cancelling inherited signed
determinants, with the same omitted index and the same ordered face. -/
theorem internalParents_signed_determinant_add_eq_zero
    (cube : SpernerCube) (lower upper : Fin (cube.n + 1) → cube.G)
    (hlower : simplex cube cube.n lower) (hupper : simplex cube cube.n upper)
    (before : Fin cube.n) (hbefore : before.val + 1 < cube.n)
    (hdistinct : lower ≠ upper)
    (hface : ∀ kept, lower (before.succ.succAbove kept) =
      upper (before.succ.succAbove kept)) :
    (-1) ^ (before.succ : ℕ) *
        determinant (fun vertex coordinate => ((lower vertex coordinate).val : ℤ)) +
      (-1) ^ (before.succ : ℕ) *
        determinant (fun vertex coordinate => ((upper vertex coordinate).val : ℤ)) = 0 := by
  let after : Fin cube.n := ⟨before.val + 1, hbefore⟩
  have hafter : after.succ ≠ before.succ := by
    intro h
    have hvalue := congrArg Fin.val h
    simp only [Fin.val_succ, after] at hvalue
    omega
  obtain ⟨left, hleft⟩ :=
    Fin.exists_succAbove_eq (Fin.ne_of_lt before.castSucc_lt_succ)
  obtain ⟨right, hright⟩ := Fin.exists_succAbove_eq hafter
  have hreflection := internalParents_missingVertex_reflection
    cube lower upper hlower hupper before hbefore hdistinct hface
  have h := facetDeterminant_add_eq_zero_of_reflection
    (fun kept coordinate => ((lower (before.succ.succAbove kept) coordinate).val : ℤ))
    (fun coordinate => ((lower before.succ coordinate).val : ℤ))
    (fun coordinate => ((upper before.succ coordinate).val : ℤ)) left right (by
      simpa only [hleft, hright] using hreflection)
  have hlowerFace := facetDeterminant_delete
    (fun vertex coordinate => ((lower vertex coordinate).val : ℤ)) before.succ
  have hupperFace := facetDeterminant_delete
    (fun vertex coordinate => ((upper vertex coordinate).val : ℤ)) before.succ
  rw [hlowerFace] at h
  have hfaceCast :
      (fun (kept : Fin cube.n) coordinate =>
        ((lower (before.succ.succAbove kept) coordinate).val : ℤ)) =
      (fun (kept : Fin cube.n) coordinate =>
        ((upper (before.succ.succAbove kept) coordinate).val : ℤ)) := by
    funext kept coordinate
    rw [hface]
  rw [hfaceCast, hupperFace] at h
  exact h

end Math.KuhnSharedFace
