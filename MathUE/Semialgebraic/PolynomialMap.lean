import MathUE.Semialgebraic.Projection
import MathUE.Logic.SignFormulaFiniteFolds
import Mathlib.Algebra.MvPolynomial.Monad

/-!
# Semialgebraic preimages, graphs, and images of finite polynomial maps

Maps are supplied as actual finite tuples of real-coefficient multivariate
polynomials. Their preimages use polynomial substitution, and their images use
the proved real-coordinate projection theorem.
-/

namespace MathUE

/-- Evaluate the coordinate polynomials of a finite real polynomial map. -/
noncomputable def evaluatePolynomialMap {n m : ℕ}
    (polynomials : Fin m → MvPolynomial (Fin n) ℝ) (point : Fin n → ℝ) : Fin m → ℝ :=
  fun index => MvPolynomial.eval point (polynomials index)

/-- Evaluating substituted polynomials is evaluation along the supplied polynomial map. -/
theorem eval_polynomialMap_substitution {n m : ℕ}
    (polynomials : Fin m → MvPolynomial (Fin n) ℝ) (point : Fin n → ℝ)
    (polynomial : MvPolynomial (Fin m) ℝ) :
    MvPolynomial.eval point (MvPolynomial.bind₁ polynomials polynomial) =
      MvPolynomial.eval (evaluatePolynomialMap polynomials point) polynomial :=
  MvPolynomial.eval₂Hom_bind₁ (RingHom.id ℝ) point polynomials polynomial

namespace IsSemialgebraic

/-- Preimages under actual finite polynomial maps preserve semialgebraicity. -/
theorem preimage_polynomialMap {n m : ℕ} {set : Set (Fin m → ℝ)}
    (h : IsSemialgebraic set) (polynomials : Fin m → MvPolynomial (Fin n) ℝ) :
    IsSemialgebraic (evaluatePolynomialMap polynomials ⁻¹' set) := by
  obtain ⟨formula, hformula⟩ := h
  refine ⟨formula.mapAtoms (MvPolynomial.bind₁ polynomials), ?_⟩
  intro point
  rw [RealPolynomialSignFormula.HoldsAt,
    Math.PolynomialSignCell.SignFormula.holds_mapAtoms]
  have heq : (fun p => SignType.sign (MvPolynomial.eval point p)) ∘
      MvPolynomial.bind₁ polynomials =
        fun p => SignType.sign (MvPolynomial.eval (evaluatePolynomialMap polynomials point) p) := by
    funext p
    exact congrArg SignType.sign (eval_polynomialMap_substitution polynomials point p)
  rw [heq]
  exact hformula (evaluatePolynomialMap polynomials point)

/-- The graph of a polynomial map is semialgebraic in the source/output coordinate block. -/
theorem polynomialMap_graph {n m : ℕ}
    (polynomials : Fin m → MvPolynomial (Fin n) ℝ) :
    IsSemialgebraic {point : Fin (n + m) → ℝ |
      (fun index => point (Fin.natAdd n index)) =
        evaluatePolynomialMap polynomials (fun index => point (Fin.castAdd m index))} := by
  let equations : Fin m → MvPolynomial (Fin (n + m)) ℝ := fun index =>
    MvPolynomial.X (Fin.natAdd n index) -
      MvPolynomial.rename (Fin.castAdd m) (polynomials index)
  refine ⟨Math.PolynomialSignCell.SignFormula.conjunction
    (List.ofFn (fun index : Fin m => .atom (equations index) 0)), ?_⟩
  intro point
  simp only [RealPolynomialSignFormula.HoldsAt, Set.mem_setOf_eq,
    Math.PolynomialSignCell.SignFormula.holds_conjunction_iff,
    List.mem_ofFn, forall_exists_index, forall_apply_eq_imp_iff,
    Math.PolynomialSignCell.SignFormula.Holds, sign_eq_zero_iff,
    equations, map_sub, MvPolynomial.eval_X, MvPolynomial.eval_rename,
    sub_eq_zero, evaluatePolynomialMap, Function.comp_def, funext_iff]

/-- Images under actual finite polynomial maps are semialgebraic, by projecting
the graph restricted to the semialgebraic source. -/
theorem image_polynomialMap {n m : ℕ} {set : Set (Fin n → ℝ)}
    (h : IsSemialgebraic set) (polynomials : Fin m → MvPolynomial (Fin n) ℝ) :
    IsSemialgebraic (evaluatePolynomialMap polynomials '' set) := by
  have hlift := h.preimage_coordinates (Fin.castAdd m)
  have hgraph := polynomialMap_graph polynomials
  have hprojected := (hlift.inter hgraph).image_coordinate_projection
  convert hprojected using 1
  ext output
  constructor
  · rintro ⟨input, hinput, rfl⟩
    refine ⟨Fin.append input (evaluatePolynomialMap polynomials input), ?_, ?_⟩
    · constructor
      · simpa only [Set.mem_setOf_eq, Function.comp_def, Fin.append_left] using hinput
      · simp only [Set.mem_setOf_eq, Fin.append_left, Fin.append_right]
    · funext index
      exact Fin.append_right input (evaluatePolynomialMap polynomials input) index
  · rintro ⟨point, ⟨hinput, hgraphPoint⟩, rfl⟩
    exact ⟨fun index => point (Fin.castAdd m index), hinput, hgraphPoint.symm⟩

end IsSemialgebraic
end MathUE
