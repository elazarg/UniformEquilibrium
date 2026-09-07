import MathUE.RealQuantifierElimination.CoefficientSignBranch

/-! # Structural invariants for every coefficient-sign branch leaf -/

namespace MathUE.RealQuantifierElimination

namespace CoefficientSignBranch

variable {n : Nat} {α β : Type*}

/-- A predicate holds at every leaf, independently of any real environment. -/
def AllLeaves (predicate : α → Prop) : CoefficientSignBranch n α → Prop
  | .leaf value => predicate value
  | .test _ negative zero positive =>
      negative.AllLeaves predicate ∧ zero.AllLeaves predicate ∧
        positive.AllLeaves predicate

@[simp]
theorem allLeaves_leaf_iff (predicate : α → Prop) (value : α) :
    (CoefficientSignBranch.leaf value : CoefficientSignBranch n α).AllLeaves predicate ↔
      predicate value :=
  Iff.rfl

@[simp]
theorem allLeaves_test_iff (predicate : α → Prop)
    (coefficient : RingExpression n)
    (negative zero positive : CoefficientSignBranch n α) :
    (CoefficientSignBranch.test coefficient negative zero positive).AllLeaves predicate ↔
      negative.AllLeaves predicate ∧ zero.AllLeaves predicate ∧
        positive.AllLeaves predicate :=
  Iff.rfl

/-- Mapping leaves transports an all-leaves invariant by precomposition. -/
theorem allLeaves_map_iff (predicate : β → Prop) (function : α → β)
    (tree : CoefficientSignBranch n α) :
    (tree.map function).AllLeaves predicate ↔
      tree.AllLeaves (predicate ∘ function) := by
  induction tree with
  | leaf value => rfl
  | test coefficient negative zero positive hnegative hzero hpositive =>
      simp only [map, allLeaves_test_iff, hnegative, hzero, hpositive]

/-- Binding trees preserves exactly the invariant required of every substituted tree. -/
theorem allLeaves_bind_iff (predicate : β → Prop)
    (tree : CoefficientSignBranch n α)
    (function : α → CoefficientSignBranch n β) :
    (tree.bind function).AllLeaves predicate ↔
      tree.AllLeaves fun value => (function value).AllLeaves predicate := by
  induction tree with
  | leaf value => rfl
  | test coefficient negative zero positive hnegative hzero hpositive =>
      simp only [bind, allLeaves_test_iff, hnegative, hzero, hpositive]

/-- Bind leaves while making their structural invariant available to the callback. -/
def bindWithProof (predicate : α → Prop) :
    (tree : CoefficientSignBranch n α) → tree.AllLeaves predicate →
      (∀ value, predicate value → CoefficientSignBranch n β) →
        CoefficientSignBranch n β
  | .leaf value, hvalue, function => function value hvalue
  | .test coefficient negative zero positive, hall, function =>
      .test coefficient
        (negative.bindWithProof predicate hall.1 function)
        (zero.bindWithProof predicate hall.2.1 function)
        (positive.bindWithProof predicate hall.2.2 function)

/-- A proof-aware bind preserves an output invariant supplied for every callback. -/
theorem allLeaves_bindWithProof (predicate : α → Prop) (output : β → Prop)
    (tree : CoefficientSignBranch n α) (hall : tree.AllLeaves predicate)
    (function : ∀ value, predicate value → CoefficientSignBranch n β)
    (hfunction : ∀ value hvalue, (function value hvalue).AllLeaves output) :
    (tree.bindWithProof predicate hall function).AllLeaves output := by
  induction tree with
  | leaf value => exact hfunction value hall
  | test coefficient negative zero positive hnegative hzero hpositive =>
      exact ⟨hnegative hall.1, hzero hall.2.1, hpositive hall.2.2⟩

/-- Every semantically selected value satisfies a structural all-leaves invariant. -/
theorem of_selects_of_allLeaves (predicate : α → Prop)
    (tree : CoefficientSignBranch n α) (environment : Fin n → ℝ) (value : α)
    (hall : tree.AllLeaves predicate) (hselected : tree.Selects environment value) :
    predicate value := by
  induction tree with
  | leaf leafValue =>
      simpa [AllLeaves, Selects] using hselected ▸ hall
  | test coefficient negative zero positive hnegative hzero hpositive =>
      rcases hall with ⟨hallNegative, hallZero, hallPositive⟩
      cases hsign : SignType.sign (coefficient.evalReal environment) with
      | neg =>
          exact hnegative hallNegative (by simpa [Selects, hsign] using hselected)
      | zero =>
          exact hzero hallZero (by simpa [Selects, hsign] using hselected)
      | pos =>
          exact hpositive hallPositive (by simpa [Selects, hsign] using hselected)

/-- A selected proof-aware bind leaf comes from the selected input leaf and its callback. -/
theorem selects_bindWithProof_iff (predicate : α → Prop)
    (tree : CoefficientSignBranch n α) (hall : tree.AllLeaves predicate)
    (function : ∀ value, predicate value → CoefficientSignBranch n β)
    (environment : Fin n → ℝ) (selected : β) :
    (tree.bindWithProof predicate hall function).Selects environment selected ↔
      ∃ value, ∃ hvalue : predicate value,
        tree.Selects environment value ∧
          (function value hvalue).Selects environment selected := by
  induction tree with
  | leaf value =>
      constructor
      · intro hselected
        exact ⟨value, hall, rfl, hselected⟩
      · rintro ⟨other, hother, heq, hselected⟩
        subst other
        have hproof : hother = hall := Subsingleton.elim _ _
        subst hother
        exact hselected
  | test coefficient negative zero positive hnegative hzero hpositive =>
      cases hsign : SignType.sign (coefficient.evalReal environment) with
      | neg =>
          simpa [bindWithProof, Selects, hsign] using
            hnegative hall.1
      | zero =>
          simpa [bindWithProof, Selects, hsign] using
            hzero hall.2.1
      | pos =>
          simpa [bindWithProof, Selects, hsign] using
            hpositive hall.2.2

theorem AllLeaves.mono {tree : CoefficientSignBranch n α} {predicate result : α → Prop}
    (hall : tree.AllLeaves predicate) (himp : ∀ value, predicate value → result value) :
    tree.AllLeaves result := by
  induction tree with
  | leaf value => exact himp value hall
  | test coefficient negative zero positive hnegative hzero hpositive =>
      exact ⟨hnegative hall.1, hzero hall.2.1, hpositive hall.2.2⟩

end CoefficientSignBranch
end MathUE.RealQuantifierElimination
