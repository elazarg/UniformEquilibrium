import MathUE.NormalizedFarkasBasis
import MathUE.Simplex

/-! # Two-supported replacement of a finite two-coordinate mixture -/

noncomputable section

namespace Math

open LinearAlgebra

/-- Every finite mixture of two-coordinate points is weakly dominated by a
two-supported mixture with exactly the same first coordinate. -/
theorem exists_twoSupported_simplex_preserving_first_improving_second
    {Atom : Type*} [Fintype Atom] (first second : Atom → ℝ)
    (source : stdSimplex ℝ Atom) :
    ∃ target : stdSimplex ℝ Atom,
      Fintype.card {atom // target.val atom ≠ 0} ≤ 2 ∧
      wsum target first = wsum source first ∧
      wsum source second ≤ wsum target second := by
  classical
  let matrix : Matrix (Fin 2) Atom ℝ := ![fun _ => 1, first]
  let rhs : Fin 2 → ℝ := ![1, wsum source first]
  have hfeasible_iff (weight : Atom → ℝ) :
      weight ∈ standardFeasibleSet matrix rhs ↔
        weight ∈ stdSimplex ℝ Atom ∧ ∑ atom, weight atom * first atom =
          wsum source first := by
    simp only [standardFeasibleSet, Set.mem_setOf_eq, funext_iff, Fin.forall_fin_two,
      matrix, rhs, Matrix.mulVec, dotProduct, Matrix.cons_val_zero,
      Matrix.cons_val_one, mul_comm, mul_one,
      stdSimplex, Set.mem_setOf_eq]
    tauto
  have hsource : source.val ∈ standardFeasibleSet matrix rhs := by
    exact (hfeasible_iff source.val).mpr ⟨source.property, rfl⟩
  have hcompact : IsCompact (standardFeasibleSet matrix rhs) := by
    exact (isCompact_stdSimplex ℝ Atom).of_isClosed_subset
      (isClosed_standardFeasibleSet matrix rhs)
      (fun weight hweight => ((hfeasible_iff weight).mp hweight).1)
  obtain ⟨optimal, hoptimalFeasible, hoptimal⟩ := hcompact.exists_isMaxOn
    ⟨source.val, hsource⟩ (finiteDotContinuousLinearMap second).continuous.continuousOn
  have hstandard : IsStandardOptimal matrix rhs second optimal := by
    exact ⟨hoptimalFeasible, fun weight hweight => by
      simpa only [finiteDotContinuousLinearMap_apply, Set.mem_setOf_eq] using
        hoptimal hweight⟩
  obtain ⟨sparse, hsparseExtreme, hsparseOptimal, _⟩ :=
    exists_extreme_standardOptimal_of_standardOptimal matrix rhs second hstandard
  have hsparse := (hfeasible_iff sparse).mp hsparseOptimal.1
  refine ⟨⟨sparse, hsparse.1⟩, ?_, hsparse.2, ?_⟩
  · have hcard :=
      (linearIndependent_supportColumns_of_extreme_standardFeasible
        matrix rhs hsparseExtreme).fintype_card_le_finrank
    simpa only [Module.finrank_fintype_fun_eq_card, Fintype.card_fin] using hcard
  · change (∑ atom, source.val atom * second atom) ≤ ∑ atom, sparse atom * second atom
    simpa only [mul_comm] using hsparseOptimal.2 source.val hsource

/-- An objective increasing in its second coordinate can be maximized on a two-supported
marginal whenever a maximizing source is supplied. -/
theorem exists_twoSupported_simplex_maximizer
    {Atom : Type*} [Fintype Atom] (first second : Atom → ℝ)
    (objective : ℝ → ℝ → ℝ)
    (hmono : ∀ firstValue secondValue nextSecond,
      secondValue ≤ nextSecond →
        objective firstValue secondValue ≤ objective firstValue nextSecond)
    (source : stdSimplex ℝ Atom)
    (hsource : ∀ candidate : stdSimplex ℝ Atom,
      objective (wsum candidate first) (wsum candidate second) ≤
        objective (wsum source first) (wsum source second)) :
    ∃ target : stdSimplex ℝ Atom,
      Fintype.card {atom // target.val atom ≠ 0} ≤ 2 ∧
      objective (wsum target first) (wsum target second) =
        objective (wsum source first) (wsum source second) ∧
      ∀ candidate : stdSimplex ℝ Atom,
        objective (wsum candidate first) (wsum candidate second) ≤
          objective (wsum target first) (wsum target second) := by
  obtain ⟨target, hcard, hfirst, hsecond⟩ :=
    exists_twoSupported_simplex_preserving_first_improving_second first second source
  have hvalue : objective (wsum target first) (wsum target second) =
      objective (wsum source first) (wsum source second) := by
    apply le_antisymm (hsource target)
    rw [hfirst]
    exact hmono _ _ _ hsecond
  exact ⟨target, hcard, hvalue, fun candidate => (hsource candidate).trans hvalue.ge⟩

section ThreeMarginals

variable {First Second Third : Type*}
variable [Fintype First] [Fintype Second] [Fintype Third]

/-- A finite three-marginal product expectation, with no correlation variable. -/
def threeMarginalValue (kernel : First → Second → Third → ℝ)
    (first : stdSimplex ℝ First) (second : stdSimplex ℝ Second)
    (third : stdSimplex ℝ Third) : ℝ :=
  wsum first (fun i => wsum second (fun j => wsum third (kernel i j)))

theorem threeMarginalValue_swap_first_second (kernel : First → Second → Third → ℝ)
    (first : stdSimplex ℝ First) (second : stdSimplex ℝ Second)
    (third : stdSimplex ℝ Third) :
    threeMarginalValue kernel first second third =
      threeMarginalValue (fun j i k => kernel i j k) second first third := by
  exact wsum_wsum_comm first second (fun i j => wsum third (kernel i j))

theorem threeMarginalValue_rotate_last_first (kernel : First → Second → Third → ℝ)
    (first : stdSimplex ℝ First) (second : stdSimplex ℝ Second)
    (third : stdSimplex ℝ Third) :
    threeMarginalValue kernel first second third =
      threeMarginalValue (fun k i j => kernel i j k) third first second := by
  unfold threeMarginalValue
  simp_rw [wsum_wsum_comm second third]
  exact wsum_wsum_comm first third _

/-- Successive unilateral marginal replacements retain the first output and
weakly increase the second while making every marginal two-supported. -/
theorem exists_three_twoSupported_marginals_preserving_first_improving_second
    (firstKernel secondKernel : First → Second → Third → ℝ)
    (first : stdSimplex ℝ First) (second : stdSimplex ℝ Second)
    (third : stdSimplex ℝ Third) :
    ∃ nextFirst : stdSimplex ℝ First, ∃ nextSecond : stdSimplex ℝ Second,
      ∃ nextThird : stdSimplex ℝ Third,
        Fintype.card {i // nextFirst.val i ≠ 0} ≤ 2 ∧
        Fintype.card {j // nextSecond.val j ≠ 0} ≤ 2 ∧
        Fintype.card {k // nextThird.val k ≠ 0} ≤ 2 ∧
        threeMarginalValue firstKernel nextFirst nextSecond nextThird =
          threeMarginalValue firstKernel first second third ∧
        threeMarginalValue secondKernel first second third ≤
          threeMarginalValue secondKernel nextFirst nextSecond nextThird := by
  obtain ⟨nextFirst, hcardFirst, hfirstA, hfirstB⟩ :=
    exists_twoSupported_simplex_preserving_first_improving_second
      (fun i => wsum second (fun j => wsum third (firstKernel i j)))
      (fun i => wsum second (fun j => wsum third (secondKernel i j))) first
  obtain ⟨nextSecond, hcardSecond, hsecondA, hsecondB⟩ :=
    exists_twoSupported_simplex_preserving_first_improving_second
      (fun j => wsum nextFirst (fun i => wsum third (firstKernel i j)))
      (fun j => wsum nextFirst (fun i => wsum third (secondKernel i j))) second
  obtain ⟨nextThird, hcardThird, hthirdA, hthirdB⟩ :=
    exists_twoSupported_simplex_preserving_first_improving_second
      (fun k => wsum nextFirst (fun i => wsum nextSecond (fun j => firstKernel i j k)))
      (fun k => wsum nextFirst (fun i => wsum nextSecond (fun j => secondKernel i j k))) third
  have hsecondA' : threeMarginalValue firstKernel nextFirst nextSecond third =
      threeMarginalValue firstKernel nextFirst second third := by
    rw [threeMarginalValue_swap_first_second firstKernel nextFirst nextSecond third,
      threeMarginalValue_swap_first_second firstKernel nextFirst second third]
    exact hsecondA
  have hsecondB' : threeMarginalValue secondKernel nextFirst second third ≤
      threeMarginalValue secondKernel nextFirst nextSecond third := by
    rw [threeMarginalValue_swap_first_second secondKernel nextFirst second third,
      threeMarginalValue_swap_first_second secondKernel nextFirst nextSecond third]
    exact hsecondB
  have hthirdA' : threeMarginalValue firstKernel nextFirst nextSecond nextThird =
      threeMarginalValue firstKernel nextFirst nextSecond third := by
    rw [threeMarginalValue_rotate_last_first firstKernel nextFirst nextSecond nextThird,
      threeMarginalValue_rotate_last_first firstKernel nextFirst nextSecond third]
    exact hthirdA
  have hthirdB' : threeMarginalValue secondKernel nextFirst nextSecond third ≤
      threeMarginalValue secondKernel nextFirst nextSecond nextThird := by
    rw [threeMarginalValue_rotate_last_first secondKernel nextFirst nextSecond third,
      threeMarginalValue_rotate_last_first secondKernel nextFirst nextSecond nextThird]
    exact hthirdB
  exact ⟨nextFirst, nextSecond, nextThird, hcardFirst, hcardSecond, hcardThird,
    hthirdA'.trans (hsecondA'.trans hfirstA), (hfirstB.trans hsecondB').trans hthirdB'⟩

theorem continuous_threeMarginalValue (kernel : First → Second → Third → ℝ) :
    Continuous (fun source : stdSimplex ℝ First × stdSimplex ℝ Second × stdSimplex ℝ Third =>
      threeMarginalValue kernel source.1 source.2.1 source.2.2) := by
  unfold threeMarginalValue wsum dotProduct
  apply continuous_finsetSum
  intro i _
  apply Continuous.mul
  · exact (stdSimplex.continuous_coord i).comp continuous_fst
  · apply continuous_finsetSum
    intro j _
    apply Continuous.mul
    · exact (stdSimplex.continuous_coord j).comp (continuous_fst.comp continuous_snd)
    · apply continuous_finsetSum
      intro k _
      exact ((stdSimplex.continuous_coord k).comp
        (continuous_snd.comp continuous_snd)).mul continuous_const

/-- A continuous objective increasing in its second coordinate attains its
finite three-marginal maximum with every marginal supported on at most two atoms. -/
theorem exists_three_twoSupported_marginals_maximizer
    [Nonempty First] [Nonempty Second] [Nonempty Third]
    (firstKernel secondKernel : First → Second → Third → ℝ)
    (objective : ℝ → ℝ → ℝ)
    (hcontinuous : Continuous (fun pair : ℝ × ℝ => objective pair.1 pair.2))
    (hmono : ∀ firstValue secondValue nextSecond,
      secondValue ≤ nextSecond →
        objective firstValue secondValue ≤ objective firstValue nextSecond) :
    ∃ first : stdSimplex ℝ First, ∃ second : stdSimplex ℝ Second,
      ∃ third : stdSimplex ℝ Third,
        Fintype.card {i // first.val i ≠ 0} ≤ 2 ∧
        Fintype.card {j // second.val j ≠ 0} ≤ 2 ∧
        Fintype.card {k // third.val k ≠ 0} ≤ 2 ∧
        ∀ otherFirst : stdSimplex ℝ First, ∀ otherSecond : stdSimplex ℝ Second,
          ∀ otherThird : stdSimplex ℝ Third,
            objective (threeMarginalValue firstKernel otherFirst otherSecond otherThird)
                (threeMarginalValue secondKernel otherFirst otherSecond otherThird) ≤
              objective (threeMarginalValue firstKernel first second third)
                (threeMarginalValue secondKernel first second third) := by
  let value := fun source :
      stdSimplex ℝ First × stdSimplex ℝ Second × stdSimplex ℝ Third =>
    objective (threeMarginalValue firstKernel source.1 source.2.1 source.2.2)
      (threeMarginalValue secondKernel source.1 source.2.1 source.2.2)
  have hvalue : Continuous value := hcontinuous.comp
    ((continuous_threeMarginalValue firstKernel).prodMk
      (continuous_threeMarginalValue secondKernel))
  obtain ⟨source, _, hsource⟩ :=
    isCompact_univ.exists_isMaxOn Set.univ_nonempty hvalue.continuousOn
  obtain ⟨first, second, third, hfirst, hsecond, hthird, hA, hB⟩ :=
    exists_three_twoSupported_marginals_preserving_first_improving_second
      firstKernel secondKernel source.1 source.2.1 source.2.2
  refine ⟨first, second, third, hfirst, hsecond, hthird, ?_⟩
  intro otherFirst otherSecond otherThird
  have hle := hsource (show (otherFirst, otherSecond, otherThird) ∈ Set.univ from trivial)
  change value (otherFirst, otherSecond, otherThird) ≤ value source at hle
  apply hle.trans
  change objective _ _ ≤ objective _ _
  rw [hA]
  exact hmono _ _ _ hB

/-- The square-root objective in the overlap packet satisfies the generic
finite-kernel maximizer theorem, including zero coordinates. -/
theorem exists_three_twoSupported_marginals_sqrt_maximizer
    [Nonempty First] [Nonempty Second] [Nonempty Third]
    (firstKernel secondKernel : First → Second → Third → ℝ) :
    ∃ first : stdSimplex ℝ First, ∃ second : stdSimplex ℝ Second,
      ∃ third : stdSimplex ℝ Third,
        Fintype.card {i // first.val i ≠ 0} ≤ 2 ∧
        Fintype.card {j // second.val j ≠ 0} ≤ 2 ∧
        Fintype.card {k // third.val k ≠ 0} ≤ 2 ∧
        ∀ otherFirst : stdSimplex ℝ First, ∀ otherSecond : stdSimplex ℝ Second,
          ∀ otherThird : stdSimplex ℝ Third,
            Real.sqrt (threeMarginalValue firstKernel otherFirst otherSecond otherThird) +
                Real.sqrt (threeMarginalValue secondKernel otherFirst otherSecond otherThird) ≤
              Real.sqrt (threeMarginalValue firstKernel first second third) +
                Real.sqrt (threeMarginalValue secondKernel first second third) := by
  exact exists_three_twoSupported_marginals_maximizer firstKernel secondKernel
    (fun first second => Real.sqrt first + Real.sqrt second)
    ((Real.continuous_sqrt.comp continuous_fst).add
      (Real.continuous_sqrt.comp continuous_snd))
    (fun _ _ _ hle => add_le_add le_rfl (Real.sqrt_le_sqrt hle))

end ThreeMarginals

end Math
