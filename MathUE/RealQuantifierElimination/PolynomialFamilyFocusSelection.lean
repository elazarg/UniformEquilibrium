import MathUE.RealQuantifierElimination.PolynomialFamilyReplacement

/-!
# Executable maximum-length polynomial-family focus

Selection compares only formal list lengths.  Coefficients need no decidable
equality, and the resulting zipper retains the exact original order.
-/

namespace MathUE.RealQuantifierElimination

open Math

/-- Select the first family member of maximal formal length and return its
exact list zipper. -/
def focusMaximum? :
    List (DensePolynomial A) → Option (PolynomialFamilyFocus A)
  | [] => none
  | polynomial :: family =>
      match focusMaximum? family with
      | none => some ⟨[], polynomial, family⟩
      | some tailFocus =>
          if tailFocus.selected.length ≤ polynomial.length then
            some ⟨[], polynomial, family⟩
          else
            some ⟨polynomial :: tailFocus.before,
              tailFocus.selected, tailFocus.after⟩

theorem focusMaximum?_eq_none_iff (family : List (DensePolynomial A)) :
    focusMaximum? family = none ↔ family = [] := by
  induction family with
  | nil => simp [focusMaximum?]
  | cons polynomial family ih =>
      cases hfocus : focusMaximum? family with
      | none => simp [focusMaximum?, hfocus]
      | some focus =>
          by_cases hle : focus.selected.length ≤ polynomial.length <;>
            simp [focusMaximum?, hfocus, hle]

/-- A successful focus reassembles to the original family and its selected
member bounds every original member's formal length. -/
theorem focusMaximum?_spec
    {family : List (DensePolynomial A)} {focus : PolynomialFamilyFocus A}
    (hfocus : focusMaximum? family = some focus) :
    focus.original = family ∧
      ∀ polynomial ∈ family, polynomial.length ≤ focus.selected.length := by
  induction family generalizing focus with
  | nil => simp [focusMaximum?] at hfocus
  | cons polynomial family ih =>
      cases htail : focusMaximum? family with
      | none =>
          have hfamily : family = [] :=
            (focusMaximum?_eq_none_iff family).mp htail
          subst family
          simp only [focusMaximum?, Option.some.injEq] at hfocus
          subst focus
          exact ⟨rfl, by simp⟩
      | some tailFocus =>
          have htailSpec := ih htail
          by_cases htailLe : tailFocus.selected.length ≤ polynomial.length
          · simp only [focusMaximum?, htail, htailLe, ↓reduceIte,
              Option.some.injEq] at hfocus
            subst focus
            refine ⟨rfl, ?_⟩
            intro member hmember
            rw [List.mem_cons] at hmember
            rcases hmember with rfl | hmember
            · exact le_rfl
            · exact (htailSpec.2 member hmember).trans htailLe
          · simp only [focusMaximum?, htail, htailLe, ↓reduceIte,
              Option.some.injEq] at hfocus
            subst focus
            refine ⟨?_, ?_⟩
            · simpa only [PolynomialFamilyFocus.original, List.cons_append] using
                congrArg (List.cons polynomial) htailSpec.1
            · intro member hmember
              rw [List.mem_cons] at hmember
              rcases hmember with rfl | hmember
              · exact Nat.le_of_lt (Nat.lt_of_not_ge htailLe)
              · exact htailSpec.2 member hmember

/-- Every nonempty family has an executable maximum-length focus. -/
theorem focusMaximum?_isSome {family : List (DensePolynomial A)} (hfamily : family ≠ []) :
    (focusMaximum? family).isSome := by
  rw [Option.isSome_iff_ne_none]
  exact fun hnone => hfamily ((focusMaximum?_eq_none_iff family).mp hnone)

/-- Dependent success form used by recursive producers. -/
theorem exists_focusMaximum_of_ne_nil
    {family : List (DensePolynomial A)} (hfamily : family ≠ []) :
    ∃ focus, focusMaximum? family = some focus ∧
      focus.original = family ∧
      ∀ polynomial ∈ focus.retained,
        polynomial.length ≤ focus.selected.length := by
  cases hfocus : focusMaximum? family with
  | none =>
      exact (hfamily ((focusMaximum?_eq_none_iff family).mp hfocus)).elim
  | some focus =>
      have hspec := focusMaximum?_spec hfocus
      refine ⟨focus, rfl, hspec.1, ?_⟩
      intro polynomial hretained
      apply hspec.2 polynomial
      rw [← hspec.1]
      simp only [PolynomialFamilyFocus.original, PolynomialFamilyFocus.retained,
        List.mem_append, List.mem_cons] at hretained ⊢
      exact hretained.elim Or.inl fun hafter => Or.inr (Or.inr hafter)

end MathUE.RealQuantifierElimination
