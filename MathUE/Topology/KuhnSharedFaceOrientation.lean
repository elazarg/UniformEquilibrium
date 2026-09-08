import MathUE.Topology.KuhnEndpointSharedFaceOrientation
import MathUE.Topology.KuhnInternalSharedFaceOrientation

/-!
# Signed determinant cancellation across every shared Kuhn face

The pinned deletion and cumulative-coordinate-count characterizations classify
two distinct parents as an opposite-endpoint pair or a common internal
deletion. The corresponding source-derived reflection theorems give integer
cancellation. This file does not recount parents or normalize cell volumes.
-/

noncomputable section

namespace Math.KuhnSharedFace

open OrientedSimplexFacet

/-- The pinned dimension-indexed insertion is the ordinary order-preserving
deletion embedding after the explicit dimension cast. -/
theorem insertIndex_eq_succAbove_cast
    (cube : SpernerCube) {dimension : ℕ} (hdimension : dimension + 1 = cube.n)
    (omitted : Fin (cube.n + 1)) (kept : Fin (dimension + 1)) :
    @insert_index cube dimension hdimension omitted kept =
      omitted.succAbove (Fin.cast hdimension kept) := by
  apply Fin.ext
  by_cases hlt : kept.val < omitted.val
  · simp [insert_index, Fin.succAbove, hlt, Fin.lt_def]
  · simp [insert_index, Fin.succAbove, hlt, Fin.lt_def]

/-- Same-endpoint deletion is injective on actual full Kuhn simplices. -/
theorem parents_eq_of_same_endpoint_deletion
    (cube : SpernerCube) {dimension : ℕ} (hdimension : dimension + 1 = cube.n)
    (lower upper : Fin (cube.n + 1) → cube.G)
    (hlower : simplex cube cube.n lower) (hupper : simplex cube cube.n upper)
    (omitted : Fin (cube.n + 1)) (hendpoint : omitted = 0 ∨ omitted = Fin.last cube.n)
    (hface : @delete_vertex cube dimension hdimension omitted lower =
      @delete_vertex cube dimension hdimension omitted upper) : lower = upper := by
  apply (@same_delete_index_eq_iff cube dimension hdimension lower upper omitted hface).mpr
  have hlast : Fin.last cube.n ≠ 0 := by
    intro h
    have hvalue := congrArg Fin.val h
    simp only [Fin.val_last, Fin.val_zero] at hvalue
    omega
  rcases hendpoint with rfl | rfl
  · obtain ⟨kept, hkept⟩ :=
      @almost_surjective_of_insert_index cube dimension hdimension 0 (Fin.last cube.n) hlast
    have hrow := congrFun hface kept
    change lower (@insert_index cube dimension hdimension 0 kept) =
      upper (@insert_index cube dimension hdimension 0 kept) at hrow
    rw [← hkept] at hrow
    funext coordinate
    apply Fin.ext
    have hlow := last_eq_first_add_one cube lower hlower coordinate
    have hupp := last_eq_first_add_one cube upper hupper coordinate
    rw [hrow] at hlow
    omega
  · obtain ⟨kept, hkept⟩ :=
      @almost_surjective_of_insert_index cube dimension hdimension (Fin.last cube.n) 0
        hlast.symm
    have hrow := congrFun hface kept
    change lower (@insert_index cube dimension hdimension (Fin.last cube.n) kept) =
      upper (@insert_index cube dimension hdimension (Fin.last cube.n) kept) at hrow
    rw [← hkept] at hrow
    funext coordinate
    apply Fin.ext
    rw [last_eq_first_add_one cube lower hlower, last_eq_first_add_one cube upper hupper, hrow]

/-- Distinct parents sharing an ordered face have opposite endpoint omissions
or the same genuinely internal omission. -/
theorem sharedFace_omission_cases
    (cube : SpernerCube) {dimension : ℕ} (hdimension : dimension + 1 = cube.n)
    (lower upper : Fin (cube.n + 1) → cube.G)
    (hlower : simplex cube cube.n lower) (hupper : simplex cube cube.n upper)
    (first second : Fin (cube.n + 1)) (hdistinct : lower ≠ upper)
    (hface : @delete_vertex cube dimension hdimension first lower =
      @delete_vertex cube dimension hdimension second upper) :
    (first = 0 ∧ second = Fin.last cube.n) ∨
      (first = Fin.last cube.n ∧ second = 0) ∨
      (first = second ∧ first ≠ 0 ∧ first ≠ Fin.last cube.n) := by
  have hsimplex := @delete_vertex_simplex cube dimension hdimension lower hlower first
  obtain ⟨missing, hmissing⟩ :=
    @ccc_fun_is_insert_index cube dimension hdimension _ hsimplex
  have hfirst := @delete_vertex_ccc_fun_match cube dimension hdimension
    lower hlower first missing hmissing
  have hmissingUpper : ccc_fun cube
      (@delete_vertex cube dimension hdimension second upper) =
      @insert_index cube dimension hdimension missing := by rwa [← hface]
  have hsecond := @delete_vertex_ccc_fun_match cube dimension hdimension
    upper hupper second missing hmissingUpper
  by_cases hfirstZero : first = 0
  · by_cases hsecondZero : second = 0
    · subst first
      subst second
      exact False.elim (hdistinct (parents_eq_of_same_endpoint_deletion cube hdimension
        lower upper hlower hupper 0 (Or.inl rfl) hface))
    · exact Or.inl ⟨hfirstZero, (hsecond.2 hsecondZero).trans (hfirst.1 hfirstZero)⟩
  · by_cases hsecondZero : second = 0
    · exact Or.inr (Or.inl
        ⟨(hfirst.2 hfirstZero).trans (hsecond.1 hsecondZero), hsecondZero⟩)
    · have hequal : first = second :=
        (hfirst.2 hfirstZero).trans (hsecond.2 hsecondZero).symm
      have hfirstLast : first ≠ Fin.last cube.n := by
        intro hlast
        subst second
        exact hdistinct (parents_eq_of_same_endpoint_deletion cube hdimension
          lower upper hlower hupper first (Or.inr hlast) hface)
      exact Or.inr (Or.inr ⟨hequal, hfirstZero, hfirstLast⟩)

/-- Every pair of distinct actual parents of the same ordered face has
cancelling signed affine determinants, with its literal deletion indices. -/
theorem sharedFace_signed_determinant_add_eq_zero
    (cube : SpernerCube) {dimension : ℕ} (hdimension : dimension + 1 = cube.n)
    (lower upper : Fin (cube.n + 1) → cube.G)
    (hlower : simplex cube cube.n lower) (hupper : simplex cube cube.n upper)
    (first second : Fin (cube.n + 1)) (hdistinct : lower ≠ upper)
    (hface : @delete_vertex cube dimension hdimension first lower =
      @delete_vertex cube dimension hdimension second upper) :
    (-1) ^ (first : ℕ) *
        determinant (fun vertex coordinate => ((lower vertex coordinate).val : ℤ)) +
      (-1) ^ (second : ℕ) *
        determinant (fun vertex coordinate => ((upper vertex coordinate).val : ℤ)) = 0 := by
  have hpositive : 0 < cube.n := by omega
  have hstandard : ∀ kept : Fin cube.n, lower (first.succAbove kept) =
      upper (second.succAbove kept) := by
    intro kept
    have h := congrFun hface (Fin.cast hdimension.symm kept)
    simp only [delete_vertex, insertIndex_eq_succAbove_cast] at h
    have hcast : Fin.cast hdimension (Fin.cast hdimension.symm kept) = kept := Fin.ext rfl
    rwa [hcast] at h
  rcases sharedFace_omission_cases cube hdimension lower upper hlower hupper
    first second hdistinct hface with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨hequal, hzero, hlast⟩
  · simp only [Fin.succAbove_zero, Fin.succAbove_last] at hstandard
    simpa only [Fin.val_zero, pow_zero, one_mul, Fin.val_last] using
      endpointParents_signed_determinant_add_eq_zero cube hpositive
        lower upper hlower hupper hstandard
  · simp only [Fin.succAbove_zero, Fin.succAbove_last] at hstandard
    simpa only [Fin.val_zero, pow_zero, one_mul, Fin.val_last, add_comm] using
      endpointParents_signed_determinant_add_eq_zero cube hpositive
        upper lower hupper hlower (fun kept => (hstandard kept).symm)
  · subst second
    obtain ⟨before, hbeforeIndex⟩ := Fin.exists_succ_eq_of_ne_zero hzero
    have hbefore : before.val + 1 < cube.n := by
      have h := Fin.val_lt_last hlast
      simpa only [← hbeforeIndex, Fin.val_succ] using h
    subst first
    exact internalParents_signed_determinant_add_eq_zero cube lower upper hlower hupper
      before hbefore hdistinct hstandard

/-- Literal incidence supplies both deletion indices and their signed
cancellation; the caller need not choose an oriented incidence witness. -/
theorem exists_sharedFace_signed_determinant_cancellation
    (cube : SpernerCube) {dimension : ℕ} (hdimension : dimension + 1 = cube.n)
    (face : Fin (dimension + 1) → cube.G)
    (lower upper : Fin (cube.n + 1) → cube.G)
    (hlower : is_face cube face lower) (hupper : is_face cube face upper)
    (hdistinct : lower ≠ upper) :
    ∃ first second : Fin (cube.n + 1),
      face = @delete_vertex cube dimension hdimension first lower ∧
      face = @delete_vertex cube dimension hdimension second upper ∧
      (-1) ^ (first : ℕ) *
          determinant (fun vertex coordinate => ((lower vertex coordinate).val : ℤ)) +
        (-1) ^ (second : ℕ) *
          determinant (fun vertex coordinate => ((upper vertex coordinate).val : ℤ)) = 0 := by
  obtain ⟨first, hfirst⟩ :=
    (@child_simplex_char cube dimension hdimension face lower hlower.2.1).mp hlower
  obtain ⟨second, hsecond⟩ :=
    (@child_simplex_char cube dimension hdimension face upper hupper.2.1).mp hupper
  exact ⟨first, second, hfirst, hsecond,
    sharedFace_signed_determinant_add_eq_zero cube hdimension lower upper hlower.2.1 hupper.2.1
      first second hdistinct (hfirst.symm.trans hsecond)⟩

end Math.KuhnSharedFace
