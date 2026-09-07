import MathUE.RealQuantifierElimination.PolynomialFormula

/-! # Leading blocks of quantified polynomial variables -/

namespace MathUE.RealQuantifierElimination.PolynomialFormula

/-- Embed an index from a leading block into a context whose trailing block
has size `free`. -/
def leadingBlockIndex (free : Nat) : {bound : Nat} → Fin bound → Fin (free + bound)
  | 0, index => Fin.elim0 index
  | _ + 1, index => Fin.cases 0 (fun earlier => (leadingBlockIndex free earlier).succ) index

/-- Embed an index from the trailing free block after a leading bound block. -/
def trailingBlockIndex (free : Nat) : (bound : Nat) → Fin free → Fin (free + bound)
  | 0, index => index
  | bound + 1, index => (trailingBlockIndex free bound index).succ

/-- Combine leading bound values and trailing free values in the index order
used by `universallyQuantifyFirst`. -/
def blockEnvironment {R : Type} {free : Nat} :
    {bound : Nat} → (Fin bound → R) → (Fin free → R) → Fin (free + bound) → R
  | 0, _, parameters => parameters
  | _ + 1, values, parameters =>
      Fin.cases (values 0)
        (blockEnvironment (fun index => values index.succ) parameters)

@[simp]
theorem blockEnvironment_leadingBlockIndex {R : Type} {free bound : Nat}
    (values : Fin bound → R) (parameters : Fin free → R) (index : Fin bound) :
    blockEnvironment values parameters (leadingBlockIndex free index) = values index := by
  induction bound with
  | zero => exact Fin.elim0 index
  | succ bound ih =>
      refine Fin.cases ?_ (fun earlier => ?_) index
      · rfl
      · exact ih (fun other => values other.succ) earlier

@[simp]
theorem blockEnvironment_trailingBlockIndex {R : Type} {free bound : Nat}
    (values : Fin bound → R) (parameters : Fin free → R) (index : Fin free) :
    blockEnvironment values parameters (trailingBlockIndex free bound index) =
      parameters index := by
  induction bound with
  | zero => rfl
  | succ bound ih =>
      exact ih (fun other => values other.succ)

/-- Universally bind a leading variable block, leaving the trailing variables
free and in their original order. -/
def universallyQuantifyFirst {free : Nat} :
    (bound : Nat) → PolynomialFormula (free + bound) → PolynomialFormula free
  | 0, formula => formula
  | bound + 1, formula => universallyQuantifyFirst bound (.all formula)

/-- Semantics of universal binding for a leading variable block. -/
theorem holdsAt_universallyQuantifyFirst_iff {free bound : Nat}
    (formula : PolynomialFormula (free + bound)) (parameters : Fin free → ℝ) :
    (universallyQuantifyFirst bound formula).HoldsAt parameters ↔
      ∀ values : Fin bound → ℝ, formula.HoldsAt (blockEnvironment values parameters) := by
  induction bound with
  | zero =>
      constructor
      · intro h values
        simpa [universallyQuantifyFirst, blockEnvironment] using h
      · intro h
        simpa [universallyQuantifyFirst, blockEnvironment] using h Fin.elim0
  | succ bound ih =>
      rw [universallyQuantifyFirst, ih]
      change (∀ earlier : Fin bound → ℝ, ∀ value : ℝ,
          formula.HoldsAt
            (Fin.cases value (blockEnvironment earlier parameters))) ↔ _
      constructor
      · intro h values
        exact h (fun index => values index.succ) (values 0)
      · intro h earlier value
        simpa [blockEnvironment] using h (Fin.cases value earlier)

end MathUE.RealQuantifierElimination.PolynomialFormula
