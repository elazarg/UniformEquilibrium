/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import MathUE.Probability.HarmonicTwoStateBranchingSCC
import MathUE.LinearAlgebra.FourierMotzkin

/-!
# Finite coupled variation potentials and their LP dual

A static nonnegative charge `charge state` is paid by a coupled potential `h` when

`charge state + E[h(next) | state] ≤ h(state)`.

If `0 ≤ h ≤ bound`, the standard Markov telescope bounds every finite expected charge prefix
by `bound`.  This is the reusable interface exhibited by the exact two-state branching SCC.

The finite feasibility problem is a linear program.  We encode its Bellman, lower-bound, and
upper-bound rows and apply the checked theorem of the alternative.  The decoded obstruction
has nonnegative Bellman occupation weights `alpha`, lower slacks `beta`, and upper slacks
`gamma`.  Column balance is

`alpha - alpha P + beta - gamma = 0`,

while strict dual positivity is

`bound * sum gamma < sum alpha * charge`.

Thus proving a sharp SCC bound is exactly proving that no such charged flow obstruction
exists.  The alternative does not itself establish Simon's cardinality estimate.
-/

open Finset BigOperators

namespace Math.Probability

noncomputable section

variable {Node : Type*} [Fintype Node]

/-- A bounded nonnegative coupled Bellman potential for a static Markov charge. -/
structure BoundedCoupledPotential
    (kernel : Node → PMF Node) (charge : Node → ℝ) (bound : ℝ) where
  potential : Node → ℝ
  nonneg : ∀ state, 0 ≤ potential state
  le_bound : ∀ state, potential state ≤ bound
  pays : ∀ state,
    charge state + expect (kernel state) potential ≤ potential state

/-- A coupled potential compiles any dominated conditional variation into a uniform
finite-horizon bound. -/
theorem finiteExpectedSpaceTimeMarkovVariation_le_of_boundedCoupledPotential
    (initial : Node) (kernel : Node → PMF Node)
    (value : Node → ℕ → ℝ) (charge : Node → ℝ) (bound : ℝ)
    (certificate : BoundedCoupledPotential kernel charge bound)
    (localVariation : ∀ state time,
      expect (kernel state) (fun successor =>
        |value successor (time + 1) - value state time|) ≤ charge state)
    (horizon : ℕ) :
    finiteExpectedSpaceTimeMarkovVariation initial kernel value horizon ≤ bound := by
  let potential : Node → ℕ → ℝ := fun state _ => certificate.potential state
  exact (finiteExpectedSpaceTimeMarkovVariation_le_initialPotential
    initial kernel value potential
      (fun state _ => certificate.nonneg state)
      (fun state time => by
        dsimp only [potential]
        calc
          expect (kernel state) (fun successor =>
                |value successor (time + 1) - value state time|) +
              expect (kernel state) certificate.potential ≤
              charge state + expect (kernel state) certificate.potential :=
            by
              simpa only [add_comm] using
                add_le_add_right (localVariation state time)
                  (expect (kernel state) certificate.potential)
          _ ≤ certificate.potential state := certificate.pays state)
      horizon).trans (certificate.le_bound initial)

/-- Rows of the bounded-potential LP: Bellman, lower bound, and upper bound. -/
abbrev CoupledPotentialRow (Node : Type*) := Node ⊕ (Node ⊕ Node)

/-- Encode a state-indexed potential in the coordinate type required by the LP library. -/
def encodeCoupledPotential (potential : Node → ℝ) : Fin (Fintype.card Node) → ℝ :=
  fun column => potential ((Fintype.equivFin Node).symm column)

/-- Decode LP coordinates back to state labels. -/
def decodeCoupledPotential (x : Fin (Fintype.card Node) → ℝ) : Node → ℝ :=
  fun state => x (Fintype.equivFin Node state)

@[simp]
theorem decode_encodeCoupledPotential (potential : Node → ℝ) :
    decodeCoupledPotential (encodeCoupledPotential potential) = potential := by
  funext state
  simp [decodeCoupledPotential, encodeCoupledPotential]

@[simp]
theorem encode_decodeCoupledPotential (x : Fin (Fintype.card Node) → ℝ) :
    encodeCoupledPotential (decodeCoupledPotential x) = x := by
  funext column
  simp [decodeCoupledPotential, encodeCoupledPotential]

variable [DecidableEq Node]

/-- Coefficient matrix for Bellman drift and pointwise box constraints. -/
def coupledPotentialMatrix (kernel : Node → PMF Node) :
    CoupledPotentialRow Node → Fin (Fintype.card Node) → ℝ
  | Sum.inl source, column =>
      (if (Fintype.equivFin Node).symm column = source then 1 else 0) -
        (kernel source ((Fintype.equivFin Node).symm column)).toReal
  | Sum.inr (Sum.inl state), column =>
      if (Fintype.equivFin Node).symm column = state then 1 else 0
  | Sum.inr (Sum.inr state), column =>
      if (Fintype.equivFin Node).symm column = state then -1 else 0

/-- Right-hand side for Bellman charge, nonnegativity, and the upper bound. -/
def coupledPotentialRhs (charge : Node → ℝ) (bound : ℝ) :
    CoupledPotentialRow Node → ℝ
  | Sum.inl state => charge state
  | Sum.inr (Sum.inl _) => 0
  | Sum.inr (Sum.inr _) => -bound

private theorem rowEval_coupledPotentialMatrix_bellman
    (kernel : Node → PMF Node) (potential : Node → ℝ) (source : Node) :
    Math.LinearAlgebra.rowEval (coupledPotentialMatrix kernel) (Sum.inl source)
        (encodeCoupledPotential potential) =
      potential source - expect (kernel source) potential := by
  rw [Math.LinearAlgebra.rowEval]
  have hreindex := (Fintype.equivFin Node).symm.sum_comp
    (fun state => ((if state = source then 1 else 0) -
      (kernel source state).toReal) * potential state)
  rw [show
    (∑ column : Fin (Fintype.card Node),
      coupledPotentialMatrix kernel (Sum.inl source) column *
        encodeCoupledPotential potential column) =
      ∑ state : Node, ((if state = source then 1 else 0) -
        (kernel source state).toReal) * potential state by
          simpa [coupledPotentialMatrix, encodeCoupledPotential] using hreindex]
  rw [expect_eq_sum]
  simp only [sub_mul, Finset.sum_sub_distrib]
  simp

private theorem rowEval_coupledPotentialMatrix_lower
    (kernel : Node → PMF Node) (potential : Node → ℝ) (state : Node) :
    Math.LinearAlgebra.rowEval (coupledPotentialMatrix kernel)
        (Sum.inr (Sum.inl state)) (encodeCoupledPotential potential) =
      potential state := by
  rw [Math.LinearAlgebra.rowEval]
  have hreindex := (Fintype.equivFin Node).symm.sum_comp
    (fun current => (if current = state then 1 else 0) * potential current)
  rw [show
    (∑ column : Fin (Fintype.card Node),
      coupledPotentialMatrix kernel (Sum.inr (Sum.inl state)) column *
        encodeCoupledPotential potential column) =
      ∑ current : Node, (if current = state then 1 else 0) * potential current by
        simpa [coupledPotentialMatrix, encodeCoupledPotential] using hreindex]
  simp

private theorem rowEval_coupledPotentialMatrix_upper
    (kernel : Node → PMF Node) (potential : Node → ℝ) (state : Node) :
    Math.LinearAlgebra.rowEval (coupledPotentialMatrix kernel)
        (Sum.inr (Sum.inr state)) (encodeCoupledPotential potential) =
      -potential state := by
  rw [Math.LinearAlgebra.rowEval]
  have hreindex := (Fintype.equivFin Node).symm.sum_comp
    (fun current => (if current = state then -1 else 0) * potential current)
  rw [show
    (∑ column : Fin (Fintype.card Node),
      coupledPotentialMatrix kernel (Sum.inr (Sum.inr state)) column *
        encodeCoupledPotential potential column) =
      ∑ current : Node, (if current = state then -1 else 0) * potential current by
        simpa [coupledPotentialMatrix, encodeCoupledPotential] using hreindex]
  simp

/-- The mathematical potential interface is exactly feasibility of the encoded finite LP. -/
theorem nonempty_boundedCoupledPotential_iff_isFeasible
    (kernel : Node → PMF Node) (charge : Node → ℝ) (bound : ℝ) :
    Nonempty (BoundedCoupledPotential kernel charge bound) ↔
      Math.LinearAlgebra.IsFeasible
        (coupledPotentialMatrix kernel) (coupledPotentialRhs charge bound) := by
  constructor
  · rintro ⟨certificate⟩
    refine ⟨encodeCoupledPotential certificate.potential, ?_⟩
    intro row
    rcases row with source | state | state
    · rw [coupledPotentialRhs,
        rowEval_coupledPotentialMatrix_bellman]
      linarith [certificate.pays source]
    · rw [coupledPotentialRhs,
        rowEval_coupledPotentialMatrix_lower]
      exact certificate.nonneg state
    · rw [coupledPotentialRhs,
        rowEval_coupledPotentialMatrix_upper]
      linarith [certificate.le_bound state]
  · rintro ⟨x, feasible⟩
    let potential := decodeCoupledPotential x
    have hencode : encodeCoupledPotential potential = x := by
      exact encode_decodeCoupledPotential x
    refine ⟨{
      potential := potential
      nonneg := ?_
      le_bound := ?_
      pays := ?_ }⟩
    · intro state
      have hrow := feasible (Sum.inr (Sum.inl state))
      rw [← hencode, coupledPotentialRhs,
        rowEval_coupledPotentialMatrix_lower] at hrow
      exact hrow
    · intro state
      have hrow := feasible (Sum.inr (Sum.inr state))
      rw [← hencode, coupledPotentialRhs,
        rowEval_coupledPotentialMatrix_upper] at hrow
      linarith
    · intro state
      have hrow := feasible (Sum.inl state)
      rw [← hencode, coupledPotentialRhs,
        rowEval_coupledPotentialMatrix_bellman] at hrow
      linarith

/-- Decoded dual obstruction to a bounded coupled potential. -/
def IsCoupledPotentialFlowObstruction
    (kernel : Node → PMF Node) (charge : Node → ℝ) (bound : ℝ)
    (alpha beta gamma : Node → ℝ) : Prop :=
  (∀ state, 0 ≤ alpha state) ∧
    (∀ state, 0 ≤ beta state) ∧
    (∀ state, 0 ≤ gamma state) ∧
    (∀ destination,
      alpha destination -
          ∑ source, alpha source * (kernel source destination).toReal +
          beta destination - gamma destination = 0) ∧
    bound * ∑ state, gamma state <
      ∑ state, alpha state * charge state

/-- Net mass created at a destination by a proposed Bellman occupation weight. -/
def coupledPotentialFlowDefect
    (kernel : Node → PMF Node) (alpha : Node → ℝ) (destination : Node) : ℝ :=
  alpha destination -
    ∑ source, alpha source * (kernel source destination).toReal

/-- The one-weight form of the flow obstruction.  The positive part of the net defect is
the least upper-slack mass compatible with a given Bellman occupation weight. -/
def IsReducedCoupledPotentialFlowObstruction
    (kernel : Node → PMF Node) (charge : Node → ℝ) (bound : ℝ)
    (alpha : Node → ℝ) : Prop :=
  ( ∀ state, 0 ≤ alpha state) ∧
    bound * ∑ state, max (coupledPotentialFlowDefect kernel alpha state) 0 <
      ∑ state, alpha state * charge state

omit [DecidableEq Node] in
/-- Flow defect has total mass zero because every row of a Markov kernel has mass one. -/
theorem sum_coupledPotentialFlowDefect_eq_zero
    (kernel : Node → PMF Node) (alpha : Node → ℝ) :
    ∑ state, coupledPotentialFlowDefect kernel alpha state = 0 := by
  rw [show (∑ state, coupledPotentialFlowDefect kernel alpha state) =
      (∑ state, alpha state) -
        ∑ destination, ∑ source,
          alpha source * (kernel source destination).toReal by
    simp only [coupledPotentialFlowDefect, Finset.sum_sub_distrib]]
  rw [Finset.sum_comm]
  have hincoming :
      (∑ source, ∑ destination,
          alpha source * (kernel source destination).toReal) =
        ∑ source, alpha source := by
    apply Finset.sum_congr rfl
    intro source _
    rw [← Finset.mul_sum, pmf_toReal_sum_one]
    ring
  rw [hincoming, sub_self]

omit [DecidableEq Node] in
/-- Positive and negative flow defects have the same total mass. -/
theorem sum_max_flowDefect_zero_eq_sum_max_neg_flowDefect_zero
    (kernel : Node → PMF Node) (alpha : Node → ℝ) :
    (∑ state, max (coupledPotentialFlowDefect kernel alpha state) 0) =
      ∑ state, max (-coupledPotentialFlowDefect kernel alpha state) 0 := by
  have hpoint (state : Node) :
      max (coupledPotentialFlowDefect kernel alpha state) 0 -
          max (-coupledPotentialFlowDefect kernel alpha state) 0 =
        coupledPotentialFlowDefect kernel alpha state := by
    by_cases hdefect : 0 ≤ coupledPotentialFlowDefect kernel alpha state
    · simp [max_eq_left hdefect, max_eq_right (neg_nonpos.mpr hdefect)]
    · have hdefect' : coupledPotentialFlowDefect kernel alpha state ≤ 0 :=
        le_of_not_ge hdefect
      simp [max_eq_right hdefect', max_eq_left (neg_nonneg.mpr hdefect')]
  have hsum :
      (∑ state, max (coupledPotentialFlowDefect kernel alpha state) 0) -
          ∑ state, max (-coupledPotentialFlowDefect kernel alpha state) 0 = 0 := by
    rw [← Finset.sum_sub_distrib]
    simpa only [hpoint] using sum_coupledPotentialFlowDefect_eq_zero kernel alpha
  linarith

/-- Pack the three families of dual weights into the row coordinates of the LP. -/
def encodeCoupledPotentialFlow
    (alpha beta gamma : Node → ℝ) : CoupledPotentialRow Node → ℝ
  | Sum.inl state => alpha state
  | Sum.inr (Sum.inl state) => beta state
  | Sum.inr (Sum.inr state) => gamma state

private theorem encodeCoupledPotentialFlow_matrix_sum
    (kernel : Node → PMF Node) (alpha beta gamma : Node → ℝ)
    (column : Fin (Fintype.card Node)) :
    (∑ row, encodeCoupledPotentialFlow alpha beta gamma row *
        coupledPotentialMatrix kernel row column) =
      alpha ((Fintype.equivFin Node).symm column) -
          ∑ source, alpha source *
            (kernel source ((Fintype.equivFin Node).symm column)).toReal +
          beta ((Fintype.equivFin Node).symm column) -
        gamma ((Fintype.equivFin Node).symm column) := by
  rw [Fintype.sum_sum_type, Fintype.sum_sum_type]
  simp only [encodeCoupledPotentialFlow, coupledPotentialMatrix, mul_sub,
    Finset.sum_sub_distrib]
  simp
  ring

omit [DecidableEq Node] in
private theorem encodeCoupledPotentialFlow_rhs_sum
    (charge : Node → ℝ) (bound : ℝ) (alpha beta gamma : Node → ℝ) :
    (∑ row, encodeCoupledPotentialFlow alpha beta gamma row *
        coupledPotentialRhs charge bound row) =
      (∑ state, alpha state * charge state) - bound * ∑ state, gamma state := by
  have hgamma :
      (∑ state, gamma state * -bound) = -(bound * ∑ state, gamma state) := by
    calc
      (∑ state, gamma state * -bound) =
          ∑ state, -(bound * gamma state) := by
        apply Finset.sum_congr rfl
        intro state _
        ring
      _ = -(∑ state, bound * gamma state) := by simp
      _ = -(bound * ∑ state, gamma state) := by rw [Finset.mul_sum]
  rw [Fintype.sum_sum_type, Fintype.sum_sum_type]
  simp only [encodeCoupledPotentialFlow, coupledPotentialRhs, mul_zero, Finset.sum_const_zero,
    sub_eq_add_neg]
  rw [hgamma]
  ring

/-- Raw Farkas weights are exactly nonnegative charged-flow obstructions. -/
theorem hasCertificate_coupledPotential_iff_exists_flowObstruction
    (kernel : Node → PMF Node) (charge : Node → ℝ) (bound : ℝ) :
    Math.LinearAlgebra.HasCertificate
        (coupledPotentialMatrix kernel) (coupledPotentialRhs charge bound) ↔
      ∃ alpha beta gamma,
        IsCoupledPotentialFlowObstruction kernel charge bound alpha beta gamma := by
  constructor
  · rintro ⟨u, huNonneg, huBalance, huStrict⟩
    let alpha : Node → ℝ := fun state => u (Sum.inl state)
    let beta : Node → ℝ := fun state => u (Sum.inr (Sum.inl state))
    let gamma : Node → ℝ := fun state => u (Sum.inr (Sum.inr state))
    have huEncode : u = encodeCoupledPotentialFlow alpha beta gamma := by
      funext row
      rcases row with state | state | state <;> rfl
    rw [huEncode] at huNonneg huBalance huStrict
    refine ⟨alpha, beta, gamma, ?_, ?_, ?_, ?_, ?_⟩
    · exact fun state => huNonneg (Sum.inl state)
    · exact fun state => huNonneg (Sum.inr (Sum.inl state))
    · exact fun state => huNonneg (Sum.inr (Sum.inr state))
    · intro destination
      have hcolumn := huBalance (Fintype.equivFin Node destination)
      rw [encodeCoupledPotentialFlow_matrix_sum] at hcolumn
      simpa using hcolumn
    · rw [encodeCoupledPotentialFlow_rhs_sum] at huStrict
      linarith
  · rintro ⟨alpha, beta, gamma, hAlpha, hBeta, hGamma, hBalance, hStrict⟩
    refine ⟨encodeCoupledPotentialFlow alpha beta gamma, ?_, ?_, ?_⟩
    · intro row
      rcases row with state | state | state
      · exact hAlpha state
      · exact hBeta state
      · exact hGamma state
    · intro column
      rw [encodeCoupledPotentialFlow_matrix_sum]
      exact hBalance ((Fintype.equivFin Node).symm column)
    · rw [encodeCoupledPotentialFlow_rhs_sum]
      linarith

omit [DecidableEq Node] in
/-- For a nonnegative budget, lower and upper slacks can be eliminated exactly.  A dual
obstruction is equivalently one nonnegative occupation weight whose charged mass exceeds
the budget times the positive part of its flow defect. -/
theorem exists_flowObstruction_iff_exists_reducedFlowObstruction
    (kernel : Node → PMF Node) (charge : Node → ℝ) {bound : ℝ}
    (bound_nonneg : 0 ≤ bound) :
    (∃ alpha beta gamma,
        IsCoupledPotentialFlowObstruction kernel charge bound alpha beta gamma) ↔
      ∃ alpha,
        IsReducedCoupledPotentialFlowObstruction kernel charge bound alpha := by
  constructor
  · rintro ⟨alpha, beta, gamma, hAlpha, hBeta, hGamma, hBalance, hStrict⟩
    refine ⟨alpha, hAlpha, ?_⟩
    have hDefect (state : Node) :
        max (coupledPotentialFlowDefect kernel alpha state) 0 ≤ gamma state := by
      apply max_le
      · dsimp only [coupledPotentialFlowDefect]
        linarith [hBalance state, hBeta state]
      · exact hGamma state
    have hsum :
        (∑ state, max (coupledPotentialFlowDefect kernel alpha state) 0) ≤
          ∑ state, gamma state := by
      exact Finset.sum_le_sum fun state _ => hDefect state
    exact (mul_le_mul_of_nonneg_left hsum bound_nonneg).trans_lt hStrict
  · rintro ⟨alpha, hAlpha, hStrict⟩
    let defect := coupledPotentialFlowDefect kernel alpha
    let beta : Node → ℝ := fun state => max (-defect state) 0
    let gamma : Node → ℝ := fun state => max (defect state) 0
    refine ⟨alpha, beta, gamma, hAlpha, ?_, ?_, ?_, ?_⟩
    · intro state
      exact le_max_right _ _
    · intro state
      exact le_max_right _ _
    · intro state
      change defect state + beta state - gamma state = 0
      by_cases hDefect : 0 ≤ defect state
      · simp [beta, gamma, max_eq_left hDefect,
          max_eq_right (neg_nonpos.mpr hDefect)]
      · have hDefect' : defect state ≤ 0 := le_of_not_ge hDefect
        simp [beta, gamma, max_eq_right hDefect',
          max_eq_left (neg_nonneg.mpr hDefect')]
    · simpa [gamma, defect] using hStrict

/-- The theorem of the alternative gives an exact raw Farkas obstruction whenever the
bounded potential LP is infeasible. -/
theorem not_nonempty_boundedCoupledPotential_iff_farkas
    (kernel : Node → PMF Node) (charge : Node → ℝ) (bound : ℝ) :
    ¬Nonempty (BoundedCoupledPotential kernel charge bound) ↔
      Math.LinearAlgebra.HasCertificate
        (coupledPotentialMatrix kernel) (coupledPotentialRhs charge bound) := by
  rw [nonempty_boundedCoupledPotential_iff_isFeasible]
  exact Math.LinearAlgebra.theorem_of_alternative
    (coupledPotentialMatrix kernel) (coupledPotentialRhs charge bound)

/-- Exact theorem of alternatives for bounded coupled potentials, stated intrinsically:
the potential fails precisely when a nonnegative charged flow violates its budget. -/
theorem not_nonempty_boundedCoupledPotential_iff_exists_flowObstruction
    (kernel : Node → PMF Node) (charge : Node → ℝ) (bound : ℝ) :
    ¬Nonempty (BoundedCoupledPotential kernel charge bound) ↔
      ∃ alpha beta gamma,
        IsCoupledPotentialFlowObstruction kernel charge bound alpha beta gamma := by
  rw [not_nonempty_boundedCoupledPotential_iff_farkas,
    hasCertificate_coupledPotential_iff_exists_flowObstruction]

/-- One-weight intrinsic alternative for a nonnegative potential budget. -/
theorem not_nonempty_boundedCoupledPotential_iff_exists_reducedFlowObstruction
    (kernel : Node → PMF Node) (charge : Node → ℝ) {bound : ℝ}
    (bound_nonneg : 0 ≤ bound) :
    ¬Nonempty (BoundedCoupledPotential kernel charge bound) ↔
      ∃ alpha,
        IsReducedCoupledPotentialFlowObstruction kernel charge bound alpha := by
  rw [not_nonempty_boundedCoupledPotential_iff_exists_flowObstruction,
    exists_flowObstruction_iff_exists_reducedFlowObstruction kernel charge bound_nonneg]

/-- Exact intrinsic dual criterion: a bounded coupled potential exists precisely when every
nonnegative occupation weight satisfies the charged flow-defect inequality. -/
theorem nonempty_boundedCoupledPotential_iff_forall_flowBound
    (kernel : Node → PMF Node) (charge : Node → ℝ) {bound : ℝ}
    (bound_nonneg : 0 ≤ bound) :
    Nonempty (BoundedCoupledPotential kernel charge bound) ↔
      ∀ alpha, (∀ state, 0 ≤ alpha state) →
        (∑ state, alpha state * charge state) ≤
          bound * ∑ state, max (coupledPotentialFlowDefect kernel alpha state) 0 := by
  constructor
  · intro certificate alpha alpha_nonneg
    by_contra hbound
    have obstruction :
        IsReducedCoupledPotentialFlowObstruction kernel charge bound alpha :=
      ⟨alpha_nonneg, lt_of_not_ge hbound⟩
    exact ((not_nonempty_boundedCoupledPotential_iff_exists_reducedFlowObstruction
      kernel charge bound_nonneg).2 ⟨alpha, obstruction⟩) certificate
  · intro flowBound
    by_contra no_certificate
    obtain ⟨alpha, alpha_nonneg, obstruction⟩ :=
      (not_nonempty_boundedCoupledPotential_iff_exists_reducedFlowObstruction
        kernel charge bound_nonneg).1 no_certificate
    exact (not_lt_of_ge (flowBound alpha alpha_nonneg)) obstruction

/-! ## A sharp barrier to phase-blind static charges -/

namespace PhaseBlindPotentialBarrier

open ConditionalReturnBoundCounterexample

/-- Freeze the largest one-step source charge of the three-phase one-transient example at
every phase.  This pointwise envelope is deliberately stronger than the actual charge. -/
def phaseBlindCharge (state : State) : ℝ :=
  if state = source then 21 / 74 else 0

/-- One unit of proposed occupation at the transient source. -/
def alpha (state : State) : ℝ :=
  if state = source then 1 else 0

/-- The source's exit mass arrives at the first recurrent state. -/
def beta (state : State) : ℝ :=
  if state = first then 1 / 4 else 0

/-- The source retains a flow defect equal to its one-quarter exit probability. -/
def gamma (state : State) : ℝ :=
  if state = source then 1 / 4 else 0

private theorem expect_sourceLaw (f : State → ℝ) :
    expect sourceLaw f =
      (3 / 4 : ℝ) * f source + (1 / 4 : ℝ) * f first := by
  rw [sourceLaw, expect_bind]
  simp_rw [expect_map]
  simp [sourceSuccessor,
    Math.ProbabilityMassFunction.expect_uniformOfFintype_bool]
  ring

private theorem sourceLaw_source_toReal :
    (sourceLaw source).toReal = (3 / 4 : ℝ) := by
  have h := expect_sourceLaw (fun state => if state = source then 1 else 0)
  rw [expect_eq_sum] at h
  simpa [source, first] using h

private theorem sourceLaw_first_toReal :
    (sourceLaw first).toReal = (1 / 4 : ℝ) := by
  have h := expect_sourceLaw (fun state => if state = first then 1 else 0)
  rw [expect_eq_sum] at h
  simpa [source, first] using h

private theorem sourceLaw_second_toReal :
    (sourceLaw second).toReal = 0 := by
  have h := expect_sourceLaw (fun state => if state = second then 1 else 0)
  rw [expect_eq_sum] at h
  simpa [source, first, second] using h

private theorem sourceLaw_third_toReal :
    (sourceLaw third).toReal = 0 := by
  have h := expect_sourceLaw (fun state => if state = third then 1 else 0)
  rw [expect_eq_sum] at h
  simpa [source, first, third] using h

private def IsCycleState (state : State) : Prop :=
  state = first ∨ state = second ∨ state = third

private theorem cycleState_of_supportStep
    {cycleSource destination : State}
    (source_cycle : IsCycleState cycleSource)
    (step : PMFSupportStep kernel cycleSource destination) :
    IsCycleState destination := by
  rcases source_cycle with rfl | rfl | rfl
  · right
    left
    simpa [PMFSupportStep, kernel, source, first, second] using step
  · right
    right
    simpa [PMFSupportStep, kernel, source, first, second, third] using step
  · left
    simpa [PMFSupportStep, kernel, source, first, second, third] using step

private theorem cycleState_of_reachable
    {cycleSource destination : State}
    (source_cycle : IsCycleState cycleSource)
    (reachable : PMFReachable kernel cycleSource destination) :
    IsCycleState destination := by
  induction reachable with
  | refl => exact source_cycle
  | tail _ step ih => exact cycleState_of_supportStep ih step

private theorem cycleState_reaches_first
    {state : State} (state_cycle : IsCycleState state) :
    PMFReachable kernel state first := by
  rcases state_cycle with rfl | rfl | rfl
  · exact Relation.ReflTransGen.refl
  · have second_third : PMFSupportStep kernel second third := by
      change (PMF.pure third) third ≠ 0
      simp
    have third_first : PMFSupportStep kernel third first := by
      change (PMF.pure first) first ≠ 0
      simp
    exact (Relation.ReflTransGen.single second_third).tail third_first
  · apply Relation.ReflTransGen.single
    change (PMF.pure first) first ≠ 0
    simp

private theorem first_mem_finiteRecurrentCore :
    first ∈ finiteRecurrentCore kernel := by
  apply (mem_finiteRecurrentCore_iff kernel first).mpr
  intro cycleSource source_mem destination step
  have source_communicates :=
    (mem_pmfCommunicationClass_iff kernel first cycleSource).mp source_mem
  have source_cycle := cycleState_of_reachable
    (show IsCycleState first from Or.inl rfl) source_communicates.1
  apply (mem_pmfCommunicationClass_iff kernel first destination).mpr
  exact ⟨source_communicates.1.tail step,
    cycleState_reaches_first (cycleState_of_supportStep source_cycle step)⟩

private theorem second_mem_finiteRecurrentCore :
    second ∈ finiteRecurrentCore kernel := by
  apply finiteRecurrentCore_closed kernel first_mem_finiteRecurrentCore
  simp [kernel, source, first, second]

private theorem third_mem_finiteRecurrentCore :
    third ∈ finiteRecurrentCore kernel := by
  apply finiteRecurrentCore_closed kernel second_mem_finiteRecurrentCore
  simp [kernel, source, first, second, third]

private theorem not_reachable_source_from_first :
    ¬PMFReachable kernel first source := by
  intro reachable
  rcases cycleState_of_reachable (Or.inl rfl) reachable with h | h | h <;>
    have hval := congrArg Fin.val h <;>
    norm_num [source, first, second, third] at hval

private theorem source_mem_finiteTransientStates :
    source ∈ finiteTransientStates kernel := by
  apply (mem_finiteTransientStates_iff kernel source).mpr
  intro source_recurrent
  have class_closed :=
    (mem_finiteRecurrentCore_iff kernel source).mp source_recurrent
  have first_step : PMFSupportStep kernel source first := by
    simp [PMFSupportStep, kernel, sourceLaw, sourceSuccessor, source, first]
  have first_mem := class_closed
    (self_mem_pmfCommunicationClass kernel source) first_step
  exact not_reachable_source_from_first
    ((mem_pmfCommunicationClass_iff kernel source first).mp first_mem).2

private theorem uniqueTransient :
    finiteTransientStates kernel = {source} := by
  ext state
  rw [Finset.mem_singleton]
  constructor
  · intro state_transient
    by_contra state_ne
    fin_cases state
    · exact state_ne rfl
    · exact (mem_finiteTransientStates_iff kernel first).mp
        state_transient first_mem_finiteRecurrentCore
    · exact (mem_finiteTransientStates_iff kernel second).mp
        state_transient second_mem_finiteRecurrentCore
    · exact (mem_finiteTransientStates_iff kernel third).mp
        state_transient third_mem_finiteRecurrentCore
  · rintro rfl
    exact source_mem_finiteTransientStates

private theorem mod_three_cases (time : ℕ) :
    time % 3 = 0 ∨ time % 3 = 1 ∨ time % 3 = 2 := by
  omega

private theorem source_conditionalVariation_le_phaseBlindCharge (time : ℕ) :
    expect (kernel source) (fun successor =>
      |value successor (time + 1) - value source time|) ≤
        phaseBlindCharge source := by
  rw [show kernel source = sourceLaw by simp [kernel]]
  rw [expect_sourceLaw]
  rcases mod_three_cases time with htime | htime | htime
  · have hsucc : (time + 1) % 3 = 1 := by omega
    norm_num [value, sourceValue, firstValue, source, first, phaseBlindCharge,
      htime, hsucc, abs_of_nonneg, abs_of_nonpos]
  · have hsucc : (time + 1) % 3 = 2 := by omega
    norm_num [value, sourceValue, firstValue, source, first, phaseBlindCharge,
      htime, hsucc, abs_of_nonneg, abs_of_nonpos]
  · have hsucc : (time + 1) % 3 = 0 := by omega
    norm_num [value, sourceValue, firstValue, source, first, phaseBlindCharge,
      htime, hsucc, abs_of_nonneg, abs_of_nonpos]

/-- The frozen charge is the exact pointwise envelope of the three actual source phases. -/
theorem conditionalVariation_le_phaseBlindCharge (state : State) (time : ℕ) :
    expect (kernel state) (fun successor =>
      |value successor (time + 1) - value state time|) ≤
        phaseBlindCharge state := by
  by_cases state_source : state = source
  · subst state
    exact source_conditionalVariation_le_phaseBlindCharge time
  · have state_recurrent : state ∈ finiteRecurrentCore kernel := by
      fin_cases state
      · exact False.elim (state_source rfl)
      · exact first_mem_finiteRecurrentCore
      · exact second_mem_finiteRecurrentCore
      · exact third_mem_finiteRecurrentCore
    rw [expect_abs_increment_eq_zero_of_mem_finiteRecurrentCore
      kernel value value_isUnitIntervalBackwardMarkovHarmonic state_recurrent time]
    simp [phaseBlindCharge, state_source]

/-- The envelope is attained at source and phase zero. -/
theorem conditionalVariation_eq_phaseBlindCharge_at_source_zero :
    expect (kernel source) (fun successor =>
      |value successor 1 - value source 0|) = phaseBlindCharge source := by
  rw [ConditionalReturnBoundCounterexample.source_conditionalVariation_zero]
  norm_num [phaseBlindCharge]

/-- The phase-blind unit-budget LP has an explicit rational flow obstruction. -/
theorem phaseBlindCharge_flowObstruction :
    IsCoupledPotentialFlowObstruction kernel phaseBlindCharge 1 alpha beta gamma := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro state
    fin_cases state <;> norm_num [alpha, source]
  · intro state
    fin_cases state <;> norm_num [beta, first]
  · intro state
    fin_cases state <;> norm_num [gamma, source]
  · intro destination
    fin_cases destination
    · have hsource : (sourceLaw (0 : State)).toReal = (3 / 4 : ℝ) := by
        simpa only [source] using sourceLaw_source_toReal
      norm_num [alpha, beta, gamma, kernel, source, first, second, third,
        Fin.sum_univ_succ]
      linarith
    · have hfirst : (sourceLaw (1 : State)).toReal = (1 / 4 : ℝ) := by
        simpa only [first] using sourceLaw_first_toReal
      norm_num [alpha, beta, gamma, kernel, source, first, second, third,
        Fin.sum_univ_succ]
      linarith
    · have hsecond : (sourceLaw (2 : State)).toReal = 0 := by
        simpa only [second] using sourceLaw_second_toReal
      norm_num [alpha, beta, gamma, kernel, source, first, second, third,
        Fin.sum_univ_succ]
      exact hsecond
    · have hthird : (sourceLaw (3 : State)).toReal = 0 := by
        simpa only [third] using sourceLaw_third_toReal
      norm_num [alpha, beta, gamma, kernel, source, first, second, third,
        Fin.sum_univ_succ]
      exact hthird
  · norm_num [alpha, gamma, phaseBlindCharge, source, Fin.sum_univ_succ]

/-- Hence no static potential bounded by one can pay the pointwise phase envelope. -/
theorem not_nonempty_phaseBlind_boundedCoupledPotential :
    ¬Nonempty (BoundedCoupledPotential kernel phaseBlindCharge 1) := by
  exact (not_nonempty_boundedCoupledPotential_iff_exists_flowObstruction
    kernel phaseBlindCharge 1).2
      ⟨alpha, beta, gamma, phaseBlindCharge_flowObstruction⟩

/-- The obstruction is only to the phase-blind certificate.  The actual three-phase harmonic
orbit has one transient state, so its genuine time-dependent variation obeys the sharp bound
one at every horizon. -/
theorem actual_finiteExpectedSpaceTimeMarkovVariation_le_one
    (initial : State) (horizon : ℕ) :
    finiteExpectedSpaceTimeMarkovVariation initial kernel value horizon ≤ 1 := by
  exact finiteExpectedSpaceTimeMarkovVariation_le_one_of_singleTransient
    initial kernel source value value_isUnitIntervalBackwardMarkovHarmonic
      uniqueTransient horizon

end PhaseBlindPotentialBarrier

end

end Math.Probability
