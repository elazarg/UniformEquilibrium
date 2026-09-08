import MathUE.Topology.OrientedSimplexFacetDeterminant
import FixedPointTheorems.cubical_sperner_prep

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

/-- Every actual full-dimensional Kuhn edge increments exactly one coordinate by one. -/
theorem exists_unitCoordinateStep_of_simplex
    (cube : SpernerCube) (vertices : Fin (cube.n + 1) → cube.G)
    (hsimplex : simplex cube cube.n vertices) (step : Fin cube.n) :
    ∃ axis : Fin cube.n, ∀ coordinate,
      (vertices step.succ coordinate).val = (vertices step.castSucc coordinate).val +
        if coordinate = axis then 1 else 0 := by
  have hcumulative : ∀ index, ccc_fun cube vertices index = index :=
    is_id_of_strict_mono _ _ (ccc_fun_strict_mono cube vertices hsimplex)
  have hbefore := congrArg Fin.val (hcumulative step.castSucc)
  have hafter := congrArg Fin.val (hcumulative step.succ)
  have hadd := ccc_add cube vertices hsimplex 0 step.castSucc step.succ
    ⟨Fin.zero_le _, Fin.castSucc_le_succ step⟩
  have hcount : coord_change_count cube (vertices step.castSucc) (vertices step.succ) = 1 := by
    dsimp only [ccc_fun] at hbefore hafter
    simp only [Fin.val_castSucc, Fin.val_succ] at hbefore hafter
    omega
  obtain ⟨axis, haxis⟩ := Finset.card_eq_one.mp hcount
  refine ⟨axis, fun coordinate => ?_⟩
  have hmem : vertices step.castSucc coordinate ≠ vertices step.succ coordinate ↔
      coordinate = axis := by
    have h := Finset.ext_iff.mp haxis coordinate
    simpa only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton] using h
  by_cases hequal : coordinate = axis
  · have hne := hmem.mpr hequal
    have hmono := monotone_1_of_simplex cube vertices hsimplex
      step.castSucc step.succ (Fin.castSucc_le_succ step) coordinate
    have hbound := le_add_one_of_simplex cube vertices hsimplex
      step.succ step.castSucc coordinate
    have hvalne : (vertices step.castSucc coordinate).val ≠
        (vertices step.succ coordinate).val := fun h => hne (Fin.ext h)
    rw [if_pos hequal]
    omega
  · have heq : vertices step.castSucc coordinate = vertices step.succ coordinate :=
      not_not.mp (fun h => hequal (hmem.mp h))
    simp only [hequal, if_false, add_zero, heq]

/-- Integer-coordinate form of the same actual unit step. -/
theorem exists_integerUnitCoordinateStep_of_simplex
    (cube : SpernerCube) (vertices : Fin (cube.n + 1) → cube.G)
    (hsimplex : simplex cube cube.n vertices) (step : Fin cube.n) :
    ∃ axis : Fin cube.n, ∀ coordinate,
      ((vertices step.succ coordinate).val : ℤ) =
        ((vertices step.castSucc coordinate).val : ℤ) +
          if coordinate = axis then 1 else 0 := by
  obtain ⟨axis, haxis⟩ := exists_unitCoordinateStep_of_simplex cube vertices hsimplex step
  refine ⟨axis, fun coordinate => ?_⟩
  have h := haxis coordinate
  split_ifs at h ⊢ <;> exact_mod_cast h

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
  obtain ⟨firstAxis, hfirst⟩ :=
    exists_integerUnitCoordinateStep_of_simplex cube lower hlower before
  obtain ⟨secondAxis, hsecond⟩ :=
    exists_integerUnitCoordinateStep_of_simplex cube upper hupper before
  obtain ⟨lastAxis, hlast⟩ :=
    exists_integerUnitCoordinateStep_of_simplex cube lower hlower after
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
