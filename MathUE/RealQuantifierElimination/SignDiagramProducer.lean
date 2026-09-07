import MathUE.RealQuantifierElimination.PolynomialFamilyDiagramRestoration
import MathUE.RealQuantifierElimination.CoefficientSignBranchInvariants
import MathUE.RealQuantifierElimination.FocusedSignReconstruction
import MathUE.RealQuantifierElimination.PolynomialFamilyFocusSelection
import MathUE.RealQuantifierElimination.PolynomialFamilyPreprocessingBounds

/-!
# Executable Cohen-Hormander sign-diagram producer
-/

namespace MathUE.RealQuantifierElimination

open Math.DensePolynomial OrderedRealSignDiagram

variable {n : Nat}

/-- Every retained column at a selected preprocessing leaf is nonconstant and
has a nonzero specialized formal leading coefficient. -/
theorem ClassifiesFamilyAt.nonconstant_inputs
    {environment : Fin n → ℝ}
    {originals : List (Math.DensePolynomial (RingExpression n))}
    {classifications : List (PolynomialClassification n)}
    (h : ClassifiesFamilyAt environment originals classifications) :
    ∀ p ∈ nonconstantPolynomials classifications,
      1 < p.length ∧ RingExpression.realEvaluator environment (leadingCoeff p) ≠ 0 := by
  induction h with
  | nil => simp [nonconstantPolynomials]
  | @cons original classification originals classifications hc ht ih =>
      cases classification with
      | zero => exact ih
      | constant sign => exact ih
      | nonconstant p =>
          intro q hq
          rcases List.mem_cons.mp hq with rfl | hq
          · refine ⟨by have := hc.1; omega, ?_⟩
            apply hc.2.2.2.resolve_left
            intro hz
            have := hc.1
            simp only [hz, List.length_nil] at this
            omega
          · exact ih q hq

/-- Total executable row restoration; the semantic theorem proves the fallback
is unreachable on every selected branch with a correctly realized input diagram. -/
def restoreDiagramRows (classifications : List (PolynomialClassification n))
    (rows : List (List SignType)) : List (List SignType) :=
  (restoreRows classifications rows).getD []

theorem restoreDiagramRows_correct (environment : Fin n → ℝ)
    {originals : List (Math.DensePolynomial (RingExpression n))}
    {classifications : List (PolynomialClassification n)}
    (hclassified : ClassifiesFamilyAt environment originals classifications)
    {rows : List (List SignType)}
    (h : ReducedRealizes (specializeFamily environment
      (nonconstantPolynomials classifications)) rows) :
    ReducedRealizes (specializeFamily environment originals)
      (restoreDiagramRows classifications rows) := by
  obtain ⟨restored, heq, hrestored⟩ :=
    exists_restoreRows_reducedRealizes environment hclassified h
  simpa only [restoreDiagramRows, heq, Option.getD_some] using hrestored

/-- Structural decrease for every preprocessing branch, including branches no real
environment selects. This is the bound needed inside the proof-aware callback. -/
theorem focused_preprocessing_replacement_decreases
    {originals : List (Math.DensePolynomial (RingExpression n))}
    {classifications : List (PolynomialClassification n)}
    (hbound : FamilyLengthBound originals classifications)
    {focus : PolynomialFamilyFocus (RingExpression n)}
    (hfocus : focusMaximum? (nonconstantPolynomials classifications) = some focus) :
    familyRecursionMeasure focus.replacement < familyRecursionMeasure originals := by
  have hspec := focusMaximum?_spec hfocus
  have hselected : focus.selected ∈ nonconstantPolynomials classifications := by
    rw [← hspec.1]
    simp [PolynomialFamilyFocus.original]
  have hdegree := nonconstantPolynomials_length_two_le hbound focus.selected hselected
  have hmaximal : ∀ q ∈ focus.retained, q.length ≤ focus.selected.length := by
    intro q hq
    apply hspec.2 q
    rw [← hspec.1]
    simp only [PolynomialFamilyFocus.original, PolynomialFamilyFocus.retained,
      List.mem_append, List.mem_cons] at hq ⊢
    exact hq.elim Or.inl (fun ha => Or.inr (Or.inr ha))
  have hstep := focus.replacement_recursionMeasure_lt hdegree hmaximal
  rw [hspec.1] at hstep
  exact FamilyRecursionMeasure.less_of_less_of_atMost hstep
    (familyRecursionMeasure_nonconstantPolynomials_atMost hbound)

/-- Compute a finite coefficient-sign tree of reduced real sign diagrams.
The recursion uses only formal coefficient syntax and natural-number size bounds. -/
def signDiagram (family : List (Math.DensePolynomial (RingExpression n))) :
    CoefficientSignBranch n (List (List SignType)) :=
  (CoefficientSignBranch.preprocessFamily family).bindWithProof (FamilyLengthBound family)
    (CoefficientSignBranch.allLeaves_preprocessFamily_lengthBound family)
    (fun classifications _hbound =>
      match _hfocus : focusMaximum? (nonconstantPolynomials classifications) with
      | none => .leaf (restoreDiagramRows classifications [[]])
      | some focus =>
          (signDiagram focus.replacement).map (fun rows =>
            restoreDiagramRows classifications
              (reconstructFocusedRows focus.before.length focus.retained.length rows)))
termination_by familyRecursionMeasure family
decreasing_by exact focused_preprocessing_replacement_decreases _hbound _hfocus

/-- Every real environment selects a correctly realized reduced diagram for the
entire original family. No producer or elimination theorem is supplied as a hypothesis. -/
theorem signDiagram_correct (environment : Fin n → ℝ)
    (family : List (Math.DensePolynomial (RingExpression n))) (rows : List (List SignType))
    (hselected : (signDiagram family).Selects environment rows) :
    ReducedRealizes (specializeFamily environment family) rows := by
  rw [signDiagram, CoefficientSignBranch.selects_bindWithProof_iff] at hselected
  obtain ⟨classifications, hbound, hclassified, hselected⟩ := hselected
  have hclass := CoefficientSignBranch.classifiesFamilyAt_of_selects_preprocessFamily
    environment family classifications hclassified
  split at hselected
  · rename_i hfocus
    have hempty := (focusMaximum?_eq_none_iff _).mp hfocus
    have hrows : rows = restoreDiagramRows classifications [[]] := hselected
    rw [hrows]
    apply restoreDiagramRows_correct environment hclass
    simpa only [hempty, specializeFamily, List.map_nil] using reducedRealizes_empty
  · rename_i focus hfocus
    have hrows : ∃ recursiveRows, (signDiagram focus.replacement).Selects
        environment recursiveRows ∧ rows = restoreDiagramRows classifications
          (reconstructFocusedRows focus.before.length focus.retained.length recursiveRows) :=
      (CoefficientSignBranch.selects_map_iff _ _ _ _).mp hselected
    obtain ⟨recursiveRows, hrecursive, rfl⟩ := hrows
    apply restoreDiagramRows_correct environment hclass
    have hrecursiveCorrect := signDiagram_correct environment focus.replacement
      recursiveRows hrecursive
    have hspec := focusMaximum?_spec hfocus
    have hrebuilt := reconstructFocusedRows_correct
      (RingExpression.realEvaluator environment) focus
      (fun q hq => hclass.nonconstant_inputs q (hspec.1 ▸ hq)) hrecursiveCorrect
    simpa only [specializeFamily, hspec.1] using hrebuilt
termination_by familyRecursionMeasure family
decreasing_by exact focused_preprocessing_replacement_decreases hbound (by assumption)

end MathUE.RealQuantifierElimination
