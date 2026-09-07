import UniformEquilibrium.Quitting.Paths.FiniteCalendarRewardTableSemialgebraic
import UniformEquilibrium.Quitting.Paths.FiniteCalendarOrderedPairGroupExclusion

/-! Semialgebraicity of the raw-table group-exclusion acceptance set. -/

noncomputable section

namespace GameTheory

variable {n : ℕ}

/-- Insert the uniform mixture parameter between the reward and calendar blocks. -/
def quittingFiniteCalendarGroupCoordinateEmbedding (deadline : ℕ) :
    Fin (Fintype.card (QuittingRewardTableVariable (Fin n)) +
      Fintype.card (QuittingFiniteCalendarVariable (Fin n) deadline)) →
    Fin ((Fintype.card (QuittingRewardTableVariable (Fin n)) + 1) +
      Fintype.card (QuittingFiniteCalendarVariable (Fin n) deadline)) :=
  Fin.addCases
    (fun index => Fin.castAdd _ (Fin.castAdd 1 index))
    (fun index => Fin.natAdd _ index)

theorem quittingFiniteCalendarGroupCoordinateEmbedding_append
    (table : Fin (Fintype.card (QuittingRewardTableVariable (Fin n))) → ℝ)
    (lambda : ℝ) (deadline : ℕ)
    (calendar : Fin (Fintype.card (QuittingFiniteCalendarVariable (Fin n) deadline)) → ℝ) :
    Fin.append (Fin.append table (fun _ : Fin 1 => lambda)) calendar ∘
      quittingFiniteCalendarGroupCoordinateEmbedding deadline = Fin.append table calendar := by
  funext index
  refine Fin.addCases (fun index => ?_) (fun index => ?_) index
  · simp only [Function.comp_apply, quittingFiniteCalendarGroupCoordinateEmbedding,
      Fin.addCases_left, Fin.append_left]
  · simp only [Function.comp_apply, quittingFiniteCalendarGroupCoordinateEmbedding,
      Fin.addCases_right, Fin.append_right]

/-- Literal two-player weighted singleton surplus with one uniform parameter. -/
def quittingFiniteCalendarOrderedPairPolynomial (deadline : ℕ) (first second : Fin n) :
    MvPolynomial
      (Fin ((Fintype.card (QuittingRewardTableVariable (Fin n)) + 1) +
        Fintype.card (QuittingFiniteCalendarVariable (Fin n) deadline))) ℝ :=
  let parameter := MvPolynomial.X (Fin.castAdd
    (Fintype.card (QuittingFiniteCalendarVariable (Fin n) deadline))
      (Fin.natAdd (Fintype.card (QuittingRewardTableVariable (Fin n))) 0))
  (1 - parameter) *
    MvPolynomial.rename (quittingFiniteCalendarGroupCoordinateEmbedding deadline)
      (quittingFiniteCalendarCoordinateSingletonSurplusPolynomial deadline first) +
    parameter *
    MvPolynomial.rename (quittingFiniteCalendarGroupCoordinateEmbedding deadline)
      (quittingFiniteCalendarCoordinateSingletonSurplusPolynomial deadline second)

theorem eval_quittingFiniteCalendarOrderedPairPolynomial
    (table : Fin (Fintype.card (QuittingRewardTableVariable (Fin n))) → ℝ)
    (lambda : ℝ) (deadline : ℕ)
    (calendar : Fin (Fintype.card (QuittingFiniteCalendarVariable (Fin n) deadline)) → ℝ)
    (first second : Fin n) :
    MvPolynomial.eval (Fin.append (Fin.append table (fun _ : Fin 1 => lambda)) calendar)
      (quittingFiniteCalendarOrderedPairPolynomial deadline first second) =
        (1 - lambda) * (MvPolynomial.eval
          (calendar ∘ Fintype.equivFin (QuittingFiniteCalendarVariable (Fin n) deadline))
          (quittingFiniteCalendarRawPayoffPolynomial
            (quittingRewardTableFromCoordinates table) deadline first) -
              quittingRewardTableFromCoordinates table (quittingSingletonTerminal first) first) +
        lambda * (MvPolynomial.eval
          (calendar ∘ Fintype.equivFin (QuittingFiniteCalendarVariable (Fin n) deadline))
          (quittingFiniteCalendarRawPayoffPolynomial
            (quittingRewardTableFromCoordinates table) deadline second) -
              quittingRewardTableFromCoordinates table
                (quittingSingletonTerminal second) second) := by
  simp only [quittingFiniteCalendarOrderedPairPolynomial, map_add, map_mul, map_sub,
    map_one, MvPolynomial.eval_X, Fin.append_left, Fin.append_right,
    MvPolynomial.eval_rename, quittingFiniteCalendarGroupCoordinateEmbedding_append,
    eval_quittingFiniteCalendarCoordinateSingletonSurplusPolynomial]

theorem eval_quittingFiniteCalendarOrderedPairPolynomial_parameterPoint
    (point : Fin (Fintype.card (QuittingRewardTableVariable (Fin n)) + 1) → ℝ)
    (deadline : ℕ)
    (calendar : Fin (Fintype.card (QuittingFiniteCalendarVariable (Fin n) deadline)) → ℝ)
    (first second : Fin n) :
    MvPolynomial.eval (Fin.append point calendar)
      (quittingFiniteCalendarOrderedPairPolynomial deadline first second) =
        (1 - point (Fin.natAdd _ 0)) * (MvPolynomial.eval
          (calendar ∘ Fintype.equivFin (QuittingFiniteCalendarVariable (Fin n) deadline))
          (quittingFiniteCalendarRawPayoffPolynomial
            (quittingRewardTableFromCoordinates (point ∘ Fin.castAdd 1)) deadline first) -
              quittingRewardTableFromCoordinates (point ∘ Fin.castAdd 1)
                (quittingSingletonTerminal first) first) +
        point (Fin.natAdd _ 0) * (MvPolynomial.eval
          (calendar ∘ Fintype.equivFin (QuittingFiniteCalendarVariable (Fin n) deadline))
          (quittingFiniteCalendarRawPayoffPolynomial
            (quittingRewardTableFromCoordinates (point ∘ Fin.castAdd 1)) deadline second) -
              quittingRewardTableFromCoordinates (point ∘ Fin.castAdd 1)
                (quittingSingletonTerminal second) second) := by
  have heval := eval_quittingFiniteCalendarOrderedPairPolynomial
    (point ∘ Fin.castAdd 1) (point (Fin.natAdd _ 0)) deadline calendar first second
  have htail : (fun _ : Fin 1 => point (Fin.natAdd _ 0)) =
      fun index : Fin 1 => point (Fin.natAdd _ index) := by
    funext index
    congr 2
    exact Subsingleton.elim _ _
  rw [htail] at heval
  simp only [Function.comp_def] at heval
  rw [Fin.append_castAdd_natAdd] at heval
  exact heval

/-- The parameter is fixed outside the universal calendar quantifier; the pair is not. -/
theorem isSemialgebraic_quittingRewardTables_rawOrderedPairGroupExclusion :
    MathUE.IsSemialgebraic {point |
      HasQuittingFiniteCalendarRawOrderedPairGroupExclusion
        (quittingRewardTableFromCoordinates (point ∘ Fin.castAdd 1))
        (point (Fin.natAdd (Fintype.card (QuittingRewardTableVariable (Fin n))) 0))} := by
  let deadline := Fintype.card (Fin n) * (Fintype.card (Fin n) + 1)
  let coordinates := Fintype.equivFin (QuittingFiniteCalendarVariable (Fin n) deadline)
  have hpairs := MathUE.IsSemialgebraic.exists_finset (Finset.univ : Finset (Fin n))
    (fun first point => ∃ second ∈ (Finset.univ : Finset (Fin n)), first ≠ second ∧
      MvPolynomial.eval point (quittingFiniteCalendarOrderedPairPolynomial
        deadline first second) ≤ 0) (fun first _ => by
      apply MathUE.IsSemialgebraic.exists_finset
      intro second _
      by_cases hne : first ≠ second
      · convert MathUE.IsSemialgebraic.polynomial_nonpos
          (quittingFiniteCalendarOrderedPairPolynomial deadline first second) using 1
        ext point
        exact ⟨And.right, fun hp => ⟨hne, hp⟩⟩
      · convert
          (MathUE.IsSemialgebraic.empty : MathUE.IsSemialgebraic
            (∅ : Set (Fin ((Fintype.card (QuittingRewardTableVariable (Fin n)) + 1) +
              Fintype.card (QuittingFiniteCalendarVariable (Fin n) deadline)) → ℝ))) using 1
        ext point
        simp only [Set.mem_setOf_eq, hne, false_and, Set.mem_empty_iff_false])
  have hadmissible :=
    (isSemialgebraic_quittingFiniteCalendarCoordinateSimplex coordinates).preimage_coordinates
      (Fin.natAdd (Fintype.card (QuittingRewardTableVariable (Fin n)) + 1))
  have hresult := (hadmissible.compl.union hpairs).forall_last_coordinates
  convert hresult using 1
  ext point
  simp only [Set.mem_setOf_eq, HasQuittingFiniteCalendarRawOrderedPairGroupExclusion]
  rw [← forall_quittingFiniteCalendarCoordinates_iff
    (quittingRewardTableFromCoordinates (point ∘ Fin.castAdd 1)) deadline
      (fun value => ∃ first second : Fin n, first ≠ second ∧
        (1 - point (Fin.natAdd _ 0)) *
          (value first - quittingRewardTableFromCoordinates (point ∘ Fin.castAdd 1)
            (quittingSingletonTerminal first) first) +
          point (Fin.natAdd _ 0) *
            (value second - quittingRewardTableFromCoordinates (point ∘ Fin.castAdd 1)
              (quittingSingletonTerminal second) second) ≤ 0)]
  apply forall_congr'
  intro calendar
  simp only [Set.mem_setOf_eq, Set.mem_union, Set.mem_compl_iff,
    Finset.mem_univ, true_and, eval_quittingFiniteCalendarOrderedPairPolynomial_parameterPoint,
    Function.comp_def, Fin.append_right]
  exact imp_iff_not_or

/-- Group-exclusion acceptance is semialgebraic in raw reward entries, with one uniform
parameter in `(0, 1/2]` before the universal calendar and distinct-pair quantifiers. -/
theorem isSemialgebraic_quittingRewardTables_rawNonconcentratedGroupExclusion
    [Nonempty (Fin n)] :
    MathUE.IsSemialgebraic {table | ∃ beta < 1,
      HasQuittingFiniteCalendarRawNonconcentratedGroupExclusion
        (quittingRewardTableFromCoordinates (n := n) table) beta} := by
  let parameter : MvPolynomial
      (Fin (Fintype.card (QuittingRewardTableVariable (Fin n)) + 1)) ℝ :=
    MvPolynomial.X (Fin.natAdd (Fintype.card (QuittingRewardTableVariable (Fin n))) 0)
  have hpositive := MathUE.IsSemialgebraic.polynomial_pos parameter
  have hhalf := MathUE.IsSemialgebraic.polynomial_nonneg (MvPolynomial.C (1 / 2) - parameter)
  have hbounded := hpositive.inter
    (hhalf.inter (isSemialgebraic_quittingRewardTables_rawOrderedPairGroupExclusion (n := n)))
  have hresult := hbounded.exists_last_coordinates
  convert hresult using 1
  ext table
  simp only [Set.mem_setOf_eq]
  rw [exists_finiteCalendarRawNonconcentratedGroupExclusion_iff_orderedPair]
  simp only [Set.mem_setOf_eq, Set.mem_inter_iff, parameter, MvPolynomial.eval_X,
    map_sub, MvPolynomial.eval_C, Fin.append_right, Function.comp_def, Fin.append_left,
    sub_nonneg]
  constructor
  · rintro ⟨lambda, hlambda, hhalf, hpair⟩
    exact ⟨fun _ : Fin 1 => lambda, hlambda, hhalf, hpair⟩
  · rintro ⟨parameter, hpositive, hhalf, hpair⟩
    exact ⟨parameter 0, hpositive, hhalf, hpair⟩

end GameTheory
