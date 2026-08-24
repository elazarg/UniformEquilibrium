/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import MathUE.DirectedTransport.Additive.Cycles
import MathUE.DirectedTransport.Basic

/-!
# Simple-cycle tests for monoid-valued directed labels

For an arbitrary monoid labelling, identity label on every directed simple
cycle implies identity label on every closed walk.  The proof removes a proper
closed subwalk and uses strong induction on length.  No commutativity or
inverse operation is needed.
-/

noncomputable section

namespace Math
namespace DirectedTransport

universe uV uE uM

variable {V : Type uV} {E : Type uE} {M : Type uM}
variable {G : EdgeGraph V E} [Monoid M] {label : E → M}

/-- The chronological walk label is the reverse product of the edge-label
list. -/
theorem walkLabel_eq_reverse_prod {start finish : V}
    (walk : G.Walk start finish) :
    walkLabel label walk = (walk.edges.map label).reverse.prod := by
  induction walk with
  | nil => simp
  | concat walk edge legal ih =>
      simp [walkLabel, ih]

/-- Identity labels on directed simple cycles suffice to check identity on
all closed walks. -/
theorem hasTrivialCycleLabels_of_simpleCycles
    (hsimple : ∀ (base : V) (cycle : G.Walk base base),
      AdditiveTransport.IsSimpleCycle cycle → walkLabel label cycle = 1) :
    HasTrivialCycleLabels G label := by
  intro base cycle
  induction hlength : cycle.length using Nat.strong_induction_on generalizing base with
  | h length ih =>
      by_cases hzero : cycle.length = 0
      · have hedges : cycle.edges = [] := by
          apply List.eq_nil_of_length_eq_zero
          simpa using hzero
        rw [walkLabel_eq_reverse_prod, hedges]
        simp
      · have hpositive : 0 < cycle.length := Nat.pos_of_ne_zero hzero
        by_cases hsimpleCycle : AdditiveTransport.IsSimpleCycle cycle
        · exact hsimple base cycle hsimpleCycle
        · simp only [AdditiveTransport.IsSimpleCycle, hpositive,
            true_and] at hsimpleCycle
          push Not at hsimpleCycle
          obtain ⟨vertex, before, inner, after, hedges, hinner, hremainder⟩ :=
            hsimpleCycle
          let remainder : G.Walk base base := before.append after
          have hlengths :
              cycle.length = inner.length + remainder.length := by
            rw [← cycle.edges_length, hedges]
            simp [remainder, Nat.add_comm, Nat.add_assoc]
          have hinnerLt : inner.length < length := by
            have hremainderPositive : 0 < remainder.length := by
              simpa [remainder] using hremainder
            rw [← hlength]
            omega
          have hremainderLt : remainder.length < length := by
            rw [← hlength]
            omega
          have hinnerLabel : walkLabel label inner = 1 := by
            exact ih inner.length hinnerLt vertex inner rfl
          have hremainderLabel : walkLabel label remainder = 1 := by
            exact ih remainder.length hremainderLt base remainder rfl
          have hbeforeAfter :
              walkLabel label after * walkLabel label before = 1 := by
            simpa [remainder] using hremainderLabel
          rw [walkLabel_eq_reverse_prod, hedges]
          simp only [List.map_append, List.reverse_append, List.prod_append]
          rw [← walkLabel_eq_reverse_prod, ← walkLabel_eq_reverse_prod,
            ← walkLabel_eq_reverse_prod, hinnerLabel, one_mul, hbeforeAfter]

end DirectedTransport
end Math

end
