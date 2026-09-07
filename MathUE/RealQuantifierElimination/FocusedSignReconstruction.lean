import MathUE.Polynomial.SignDiagramReconstruction
import MathUE.RealQuantifierElimination.PolynomialFamilyReplacement

/-!
# Restoring a reconstructed polynomial to its original column position
-/

namespace MathUE.OrderedRealSignDiagram

/-- Move the reconstructed first column past the original prefix. -/
def restoreSelectedColumn (prefixLength : ℕ) : List SignType → List SignType
  | [] => []
  | selected :: row => row.take prefixLength ++ selected :: row.drop prefixLength

theorem RowOn.restoreSelectedColumn {selected : Polynomial ℝ}
    {before after : List (Polynomial ℝ)} {cell : Set ℝ} {row : List SignType}
    (h : RowOn (selected :: (before ++ after)) cell row) :
    RowOn (before ++ selected :: after) cell (restoreSelectedColumn before.length row) := by
  cases h with
  | cons hs hr =>
      have hbefore := List.forall₂_take before.length hr
      have hafter := List.forall₂_drop before.length hr
      simp only [List.take_left] at hbefore
      simp only [List.drop_left] at hafter
      exact List.rel_append hbefore (List.Forall₂.cons hs hafter)

theorem ReducedRealizes.restoreSelectedColumn {selected : Polynomial ℝ}
    {before after : List (Polynomial ℝ)} {rows : List (List SignType)}
    (h : ReducedRealizes (selected :: (before ++ after)) rows) :
    ReducedRealizes (before ++ selected :: after)
      (rows.map (restoreSelectedColumn before.length)) := by
  obtain ⟨cuts, hrealizes, hroots⟩ := h
  refine ⟨cuts, ⟨hrealizes.1, ?_⟩, ?_⟩
  · apply List.forall₂_map_right_iff.mpr
    exact hrealizes.2.imp fun _ _ hr => hr.restoreSelectedColumn
  · intro x
    rw [hroots]
    simp only [List.mem_cons, List.mem_append]
    constructor <;> rintro ⟨q, hq, hn, hz⟩ <;> refine ⟨q, ?_, hn, hz⟩
    · rcases hq with hq | hq | hq
      · exact Or.inr (Or.inl hq)
      · exact Or.inl hq
      · exact Or.inr (Or.inr hq)
    · rcases hq with hq | hq | hq
      · exact Or.inr (Or.inl hq)
      · exact Or.inl hq
      · exact Or.inr (Or.inr hq)

end MathUE.OrderedRealSignDiagram

namespace MathUE.RealQuantifierElimination

open Math.DensePolynomial OrderedRealSignDiagram

variable {A : Type*} [Zero A] [One A] [Add A] [Neg A] [Mul A]

/-- A trimmed nonconstant dense input has a derivative with nonzero formal leading
coefficient after evaluation; this is not an extra sign branch or oracle. -/
theorem derivative_leadingCoeff_ne_zero (e : Evaluator A ℝ)
    (p : Math.DensePolynomial A) (hdegree : 1 < p.length)
    (hleading : e (leadingCoeff p) ≠ 0) : e (leadingCoeff (derivative p)) ≠ 0 := by
  have hd : 0 < (toPolynomial e p).natDegree := by
    rw [toPolynomial_natDegree_eq e p hleading]
    omega
  have hn := Polynomial.derivative_ne_zero.mpr hd.ne'
  have hc := toPolynomial_coeff_length_sub_one e (derivative p)
  rw [toPolynomial_derivative] at hc
  have hi : (derivative p).length - 1 = (toPolynomial e p).derivative.natDegree := by
    rw [length_derivative, Polynomial.natDegree_derivative,
      toPolynomial_natDegree_eq e p hleading]
  rw [hi, Polynomial.coeff_natDegree] at hc
  exact hc ▸ Polynomial.leadingCoeff_ne_zero.mpr hn

/-- Reconstruct the focused polynomial and restore its original column position. -/
def reconstructFocusedRows (prefixLength retainedLength : ℕ)
    (rows : List (List SignType)) : List (List SignType) :=
  (reconstructFromRemainderRows (retainedLength + 1) rows).map
    (restoreSelectedColumn prefixLength)

/-- The literal family-replacement step reconstructs the original family in its
original column order. The derivative-leading hypothesis is derived from trimming. -/
theorem reconstructFocusedRows_correct (e : Evaluator A ℝ)
    (focus : PolynomialFamilyFocus A)
    (hinputs : ∀ q ∈ focus.original, 1 < q.length ∧ e (leadingCoeff q) ≠ 0)
    {rows : List (List SignType)}
    (h : ReducedRealizes (focus.replacement.map (toPolynomial e)) rows) :
    ReducedRealizes (focus.original.map (toPolynomial e))
      (reconstructFocusedRows focus.before.length focus.retained.length rows) := by
  have hselected := hinputs focus.selected (by simp [PolynomialFamilyFocus.original])
  have hretained : ∀ q ∈ focus.retained, 1 < q.length ∧ e (leadingCoeff q) ≠ 0 := by
    intro q hq
    apply hinputs q
    simpa only [PolynomialFamilyFocus.original, PolynomialFamilyFocus.retained,
      List.mem_append, List.mem_cons] using
      (show q ∈ focus.before ∨ q = focus.selected ∨ q ∈ focus.after from
        (List.mem_append.mp hq).elim Or.inl (fun ha => Or.inr (Or.inr ha)))
  have hdivisors := focus.replacementDivisors_eq_derivative_cons_retained
    (fun q hq => (hretained q hq).1)
  have hleading : ∀ q ∈ derivative focus.selected :: focus.retained,
      e (leadingCoeff q) ≠ 0 := by
    intro q hq
    rcases List.mem_cons.mp hq with rfl | hq
    · exact derivative_leadingCoeff_ne_zero e focus.selected hselected.1 hselected.2
    · exact (hretained q hq).2
  have hsource : ReducedRealizes
      (((derivative focus.selected :: focus.retained).map (toPolynomial e)) ++
        ((derivative focus.selected :: focus.retained).map
          (fun d => toPolynomial e (pseudoDivide focus.selected d).remainder))) rows := by
    simpa only [PolynomialFamilyFocus.replacement,
      PolynomialFamilyFocus.replacementRemainders, hdivisors, List.map_append,
      List.map_cons, List.map_map, Function.comp_def] using h
  have hrebuilt := reconstructFromPseudoRemainderRows_correct e focus.selected focus.retained
    hselected.1 hselected.2 hleading hsource
  have hrestored := ReducedRealizes.restoreSelectedColumn
    (before := focus.before.map (toPolynomial e))
    (after := focus.after.map (toPolynomial e))
    (by simpa only [PolynomialFamilyFocus.retained, List.map_append] using hrebuilt)
  simpa only [PolynomialFamilyFocus.original, PolynomialFamilyFocus.retained,
    List.map_append, List.map_cons,
    List.length_map, reconstructFocusedRows] using hrestored

end MathUE.RealQuantifierElimination
