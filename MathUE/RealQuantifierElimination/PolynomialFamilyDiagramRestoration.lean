import MathUE.RealQuantifierElimination.PolynomialFamilyPreprocessing
import MathUE.Polynomial.OrderedRealSignDiagram

/-!
# Restoring preprocessed polynomial sign diagrams

Rows for retained nonconstant columns are expanded to the original column order.
Zero and nonzero constant columns create no roots, so the same ordered cuts also
satisfy the reduced root-cut invariant for the original family.
-/

namespace MathUE.RealQuantifierElimination

open Math
open MathUE.OrderedRealSignDiagram

/-- Specialize every symbolic coefficient list to a real polynomial. -/
noncomputable def specializeFamily {n : Nat} (environment : Fin n → ℝ)
    (family : List (DensePolynomial (RingExpression n))) : List (Polynomial ℝ) :=
  family.map fun polynomial =>
    DensePolynomial.toPolynomial (RingExpression.realEvaluator environment) polynomial

@[simp]
theorem specializeFamily_cons {n : Nat} (environment : Fin n → ℝ)
    (polynomial : DensePolynomial (RingExpression n))
    (family : List (DensePolynomial (RingExpression n))) :
    specializeFamily environment (polynomial :: family) =
      DensePolynomial.toPolynomial (RingExpression.realEvaluator environment) polynomial ::
        specializeFamily environment family :=
  rfl

/-- Restore every row, failing exactly when a recursive row has the wrong width. -/
def restoreRows {n : Nat} (classifications : List (PolynomialClassification n)) :
    List (List SignType) → Option (List (List SignType))
  | [] => some []
  | row :: rows => do
      let restoredRow ← restoreRow classifications row
      let restoredRows ← restoreRows classifications rows
      pure (restoredRow :: restoredRows)

theorem toPolynomial_eq_of_classifiesAt_nonconstant {n : Nat}
    (environment : Fin n → ℝ)
    {original polynomial : DensePolynomial (RingExpression n)}
    (hclassified : ClassifiesAt environment original (.nonconstant polynomial)) :
    DensePolynomial.toPolynomial (RingExpression.realEvaluator environment) original =
      DensePolynomial.toPolynomial (RingExpression.realEvaluator environment) polynomial := by
  apply Polynomial.funext
  intro x
  rw [DensePolynomial.toPolynomial_eval, DensePolynomial.toPolynomial_eval]
  exact hclassified.2.1 x

/-- Every retained polynomial has positive specialized degree. -/
theorem toPolynomial_natDegree_pos_of_classifiesAt_nonconstant {n : Nat}
    (environment : Fin n → ℝ)
    {original polynomial : DensePolynomial (RingExpression n)}
    (hclassified : ClassifiesAt environment original (.nonconstant polynomial)) :
    0 < (DensePolynomial.toPolynomial (RingExpression.realEvaluator environment)
      polynomial).natDegree := by
  have hnonempty : polynomial ≠ [] := by
    intro hzero
    have hlength := hclassified.1
    rw [hzero] at hlength
    simp at hlength
  have hleading := hclassified.2.2.2.resolve_left hnonempty
  have hlength := hclassified.1
  rw [DensePolynomial.toPolynomial_natDegree_eq _ polynomial hleading]
  omega

/-- Every retained polynomial has nonzero real specialization. -/
theorem toPolynomial_ne_zero_of_classifiesAt_nonconstant {n : Nat}
    (environment : Fin n → ℝ)
    {original polynomial : DensePolynomial (RingExpression n)}
    (hclassified : ClassifiesAt environment original (.nonconstant polynomial)) :
    DensePolynomial.toPolynomial (RingExpression.realEvaluator environment) polynomial ≠ 0 := by
  intro hzero
  have hpositive :=
    toPolynomial_natDegree_pos_of_classifiesAt_nonconstant environment hclassified
  rw [hzero] at hpositive
  simp at hpositive

/-- A restored row is correct on the same cell for the original polynomial order. -/
theorem exists_restoreRow_rowOn {n : Nat}
    (environment : Fin n → ℝ) (cell : Set ℝ)
    {originals : List (DensePolynomial (RingExpression n))}
    {classifications : List (PolynomialClassification n)}
    (hclassified : ClassifiesFamilyAt environment originals classifications)
    {recursiveRow : List SignType}
    (hrow : RowOn (specializeFamily environment
      (nonconstantPolynomials classifications)) cell recursiveRow) :
    ∃ restoredRow,
      restoreRow classifications recursiveRow = some restoredRow ∧
      RowOn (specializeFamily environment originals) cell restoredRow := by
  induction hclassified generalizing recursiveRow with
  | nil =>
      simp [specializeFamily, nonconstantPolynomials, RowOn] at hrow
      subst recursiveRow
      exact ⟨[], rfl, .nil⟩
  | @cons original classification originals classifications hhead htail ih =>
      cases classification with
      | zero =>
          obtain ⟨restored, hrestore, hrestored⟩ := ih hrow
          refine ⟨.zero :: restored, by simp [restoreRow, hrestore], .cons ?_ hrestored⟩
          change SignOn
            (DensePolynomial.toPolynomial (RingExpression.realEvaluator environment) original)
            .zero cell
          rw [hhead]
          intro x _
          simp
      | constant sign =>
          obtain ⟨restored, hrestore, hrestored⟩ := ih hrow
          refine ⟨sign :: restored, by simp [restoreRow, hrestore], .cons ?_ hrestored⟩
          intro x _
          rw [DensePolynomial.toPolynomial_eval]
          exact hhead.2 x
      | nonconstant polynomial =>
          cases recursiveRow with
          | nil => cases hrow
          | cons sign signs =>
              cases hrow with
              | cons hpolynomial hrowTail =>
                  obtain ⟨restored, hrestore, hrestored⟩ := ih hrowTail
                  have heq :=
                    toPolynomial_eq_of_classifiesAt_nonconstant environment hhead
                  have horiginal :
                      SignOn
                        (DensePolynomial.toPolynomial
                          (RingExpression.realEvaluator environment) original)
                        sign cell := by
                    rw [heq]
                    exact hpolynomial
                  exact ⟨sign :: restored, by simp [restoreRow, hrestore],
                    .cons horiginal hrestored⟩

/-- All rows of a realized recursive diagram restore over the same cells. -/
theorem exists_restoreRows_rowsOn {n : Nat}
    (environment : Fin n → ℝ)
    {originals : List (DensePolynomial (RingExpression n))}
    {classifications : List (PolynomialClassification n)}
    (hclassified : ClassifiesFamilyAt environment originals classifications)
    {cells : List (Set ℝ)} {recursiveRows : List (List SignType)}
    (hrows : RowsOn (specializeFamily environment
      (nonconstantPolynomials classifications)) cells recursiveRows) :
    ∃ restoredRows,
      restoreRows classifications recursiveRows = some restoredRows ∧
      RowsOn (specializeFamily environment originals) cells restoredRows := by
  induction hrows with
  | nil => exact ⟨[], rfl, .nil⟩
  | @cons cell recursiveRow cells recursiveRows hrow hrows ih =>
      obtain ⟨restoredRow, hrestoreRow, hrestoredRow⟩ :=
        exists_restoreRow_rowOn environment cell hclassified hrow
      obtain ⟨restoredRows, hrestoreRows, hrestoredRows⟩ := ih
      exact ⟨restoredRow :: restoredRows,
        by simp [restoreRows, hrestoreRow, hrestoreRows],
        .cons hrestoredRow hrestoredRows⟩

/-- The same cuts realize the restored rows for the original family. -/
theorem exists_restoreRows_realizes {n : Nat}
    (environment : Fin n → ℝ)
    {originals : List (DensePolynomial (RingExpression n))}
    {classifications : List (PolynomialClassification n)}
    (hclassified : ClassifiesFamilyAt environment originals classifications)
    {recursiveRows : List (List SignType)}
    (hrealizes : Realizes (specializeFamily environment
      (nonconstantPolynomials classifications)) recursiveRows) :
    ∃ restoredRows,
      restoreRows classifications recursiveRows = some restoredRows ∧
      Realizes (specializeFamily environment originals) restoredRows := by
  obtain ⟨cuts, hordered, hrows⟩ := hrealizes
  obtain ⟨restoredRows, hrestore, hrestored⟩ :=
    exists_restoreRows_rowsOn environment hclassified hrows
  exact ⟨restoredRows, hrestore, cuts, hordered, hrestored⟩

/-- A polynomial family has a nonzero member vanishing at one point. -/
def HasNonzeroRootAt (polynomials : List (Polynomial ℝ)) (x : ℝ) : Prop :=
  ∃ polynomial ∈ polynomials, polynomial ≠ 0 ∧ polynomial.eval x = 0

theorem hasNonzeroRootAt_cons (polynomial : Polynomial ℝ)
    (polynomials : List (Polynomial ℝ)) (x : ℝ) :
    HasNonzeroRootAt (polynomial :: polynomials) x ↔
      (polynomial ≠ 0 ∧ polynomial.eval x = 0) ∨
        HasNonzeroRootAt polynomials x := by
  simp [HasNonzeroRootAt]

/-- Preprocessing preserves the union of roots of nonzero family members. -/
theorem hasNonzeroRootAt_specializeFamily_iff {n : Nat}
    (environment : Fin n → ℝ) (x : ℝ)
    {originals : List (DensePolynomial (RingExpression n))}
    {classifications : List (PolynomialClassification n)}
    (hclassified : ClassifiesFamilyAt environment originals classifications) :
    HasNonzeroRootAt (specializeFamily environment originals) x ↔
      HasNonzeroRootAt (specializeFamily environment
        (nonconstantPolynomials classifications)) x := by
  induction hclassified with
  | nil => simp [HasNonzeroRootAt, specializeFamily, nonconstantPolynomials]
  | @cons original classification originals classifications hhead htail ih =>
      cases classification with
      | zero =>
          change DensePolynomial.toPolynomial
            (RingExpression.realEvaluator environment) original = 0 at hhead
          have hnoRoot :
              ¬(DensePolynomial.toPolynomial (RingExpression.realEvaluator environment)
                  original ≠ 0 ∧
                (DensePolynomial.toPolynomial (RingExpression.realEvaluator environment)
                  original).eval x = 0) := by
            simp [hhead]
          simp only [specializeFamily_cons, nonconstantPolynomials,
            hasNonzeroRootAt_cons]
          simp only [hnoRoot, false_or]
          exact ih
      | constant sign =>
          have hnoRoot :
              ¬(DensePolynomial.toPolynomial (RingExpression.realEvaluator environment)
                  original ≠ 0 ∧
                (DensePolynomial.toPolynomial (RingExpression.realEvaluator environment)
                  original).eval x = 0) := by
            rintro ⟨_, hroot⟩
            apply hhead.1
            rw [← hhead.2 x, ← DensePolynomial.toPolynomial_eval, hroot]
            simp
          simp only [specializeFamily_cons, nonconstantPolynomials,
            hasNonzeroRootAt_cons]
          simp only [hnoRoot, false_or]
          exact ih
      | nonconstant polynomial =>
          have heq := toPolynomial_eq_of_classifiesAt_nonconstant environment hhead
          simp only [specializeFamily_cons, nonconstantPolynomials,
            hasNonzeroRootAt_cons]
          rw [heq, ih]

/-- Reduced realization is preserved, including the exact root-cut predicate. -/
theorem exists_restoreRows_reducedRealizes {n : Nat}
    (environment : Fin n → ℝ)
    {originals : List (DensePolynomial (RingExpression n))}
    {classifications : List (PolynomialClassification n)}
    (hclassified : ClassifiesFamilyAt environment originals classifications)
    {recursiveRows : List (List SignType)}
    (hrealizes : ReducedRealizes (specializeFamily environment
      (nonconstantPolynomials classifications)) recursiveRows) :
    ∃ restoredRows,
      restoreRows classifications recursiveRows = some restoredRows ∧
      ReducedRealizes (specializeFamily environment originals) restoredRows := by
  obtain ⟨cuts, ⟨hordered, hrows⟩, hroots⟩ := hrealizes
  obtain ⟨restoredRows, hrestore, hrestored⟩ :=
    exists_restoreRows_rowsOn environment hclassified hrows
  refine ⟨restoredRows, hrestore, cuts, ⟨⟨hordered, hrestored⟩, fun x => ?_⟩⟩
  rw [hroots]
  exact (hasNonzeroRootAt_specializeFamily_iff environment x hclassified).symm

end MathUE.RealQuantifierElimination
