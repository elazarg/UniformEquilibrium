import MathUE.LinearProgramming.RationalOptimization
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Rat.Encodable
import Mathlib.Logic.Encodable.Pi

/-!
# Executable exact rational feasibility and optimality selection

The canonical encodable search supplies the enumeration and terminating selector.
All tests are finite rational comparisons. Real existence is used only in erased proofs.
No optimizer, feasible rational point, numerical bound, or runtime estimate is an input.
-/

namespace Math.LinearProgramming

open scoped BigOperators

variable {Row Col : Type*} [Fintype Row] [Fintype Col]

private theorem exists_nonnegative_rational_test
    (A : Row → Col → ℚ) (b : Row → ℚ)
    (hfeasible : ∃ x : Col → ℝ, (∀ j, 0 ≤ x j) ∧
      ∀ i, (b i : ℝ) ≤ ∑ j, (A i j : ℝ) * x j) :
    ∃ x : Col → ℚ, (∀ j, 0 ≤ x j) ∧ ∀ i, b i ≤ ∑ j, A i j * x j := by
  obtain ⟨x, hx, hrows⟩ := exists_nonnegative_rational_solution
    (fun i j => (A i j : ℝ)) (fun i => (b i : ℝ))
    (fun i j => ⟨A i j, rfl⟩) (fun i => ⟨b i, rfl⟩) hfeasible
  refine ⟨x, hx, ?_⟩
  intro i
  exact_mod_cast hrows i

/-- Executable exact weak-row solver. Test the zero vector against the actual
rational rows first, then use canonical exhaustive selection if it fails.
The feasibility proof is erased and supplies no runtime witness. -/
def selectNonnegativeRationalFeasible [Encodable Col]
    (A : Row → Col → ℚ) (b : Row → ℚ)
    (hfeasible : ∃ x : Col → ℝ, (∀ j, 0 ≤ x j) ∧
      ∀ i, (b i : ℝ) ≤ ∑ j, (A i j : ℝ) * x j) : Col → ℚ :=
  if ∀ i, b i ≤ 0 then 0
  else Encodable.choose (exists_nonnegative_rational_test A b hfeasible)

theorem selectNonnegativeRationalFeasible_spec [Encodable Col]
    (A : Row → Col → ℚ) (b : Row → ℚ)
    (hfeasible : ∃ x : Col → ℝ, (∀ j, 0 ≤ x j) ∧
      ∀ i, (b i : ℝ) ≤ ∑ j, (A i j : ℝ) * x j) :
    (∀ j, 0 ≤ selectNonnegativeRationalFeasible A b hfeasible j) ∧
      ∀ i, b i ≤ ∑ j, A i j * selectNonnegativeRationalFeasible A b hfeasible j := by
  unfold selectNonnegativeRationalFeasible
  split
  · rename_i hzero
    refine ⟨fun _ => le_rfl, ?_⟩
    intro i
    simpa only [Pi.zero_apply, mul_zero, Finset.sum_const_zero] using hzero i
  · exact Encodable.choose_spec (exists_nonnegative_rational_test A b hfeasible)

/-- Decidable exact primal/dual zero-gap test, written over rationals for execution.
Its semantics are the canonical real standard-form LP, not a second duality theory. -/
def rationalPrimalDualAccepts (A : Row → Col → ℚ) (b : Row → ℚ) (c : Col → ℚ)
    (pair : (Col → ℚ) × (Row → ℚ)) : Bool :=
  decide ((∀ j, 0 ≤ pair.1 j) ∧
    (∀ i, b i ≤ ∑ j, A i j * pair.1 j) ∧
    (∀ i, 0 ≤ pair.2 i) ∧
    (∀ j, (∑ i, pair.2 i * A i j) ≤ c j) ∧
    (∑ i, b i * pair.2 i) = ∑ j, c j * pair.1 j)

theorem rationalPrimalDualAccepts_iff
    (A : Row → Col → ℚ) (b : Row → ℚ) (c : Col → ℚ)
    (pair : (Col → ℚ) × (Row → ℚ)) :
    rationalPrimalDualAccepts A b c pair = true ↔
      MinPrimalFeasible (fun i j => (A i j : ℝ)) (fun i => (b i : ℝ))
        (fun j => (pair.1 j : ℝ)) ∧
      MaxDualFeasible (fun i j => (A i j : ℝ)) (fun j => (c j : ℝ))
        (fun i => (pair.2 i : ℝ)) ∧
      maxDualValue (fun i => (b i : ℝ)) (fun i => (pair.2 i : ℝ)) =
        minPrimalValue (fun j => (c j : ℝ)) (fun j => (pair.1 j : ℝ)) := by
  simp only [rationalPrimalDualAccepts, decide_eq_true_eq, MinPrimalFeasible,
    MaxDualFeasible, Nonnegative, rowEval, colEval, maxDualValue, minPrimalValue, dot]
  constructor
  · rintro ⟨hx, hA, hy, hdual, hgap⟩
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_⟩
    · intro j
      exact_mod_cast hx j
    · intro i
      exact_mod_cast hA i
    · intro i
      exact_mod_cast hy i
    · intro j
      exact_mod_cast hdual j
    · exact_mod_cast hgap
  · rintro ⟨⟨hx, hA⟩, ⟨hy, hdual⟩, hgap⟩
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro j
      exact_mod_cast hx j
    · intro i
      exact_mod_cast hA i
    · intro i
      exact_mod_cast hy i
    · intro j
      exact_mod_cast hdual j
    · exact_mod_cast hgap

private theorem exists_rationalPrimalDual_accepts
    (A : Row → Col → ℚ) (b : Row → ℚ) (c : Col → ℚ)
    (hfeasible : ∃ x, MinPrimalFeasible
      (fun i j => (A i j : ℝ)) (fun i => (b i : ℝ)) x)
    (hbounded : ∃ lower : ℝ, ∀ x,
      MinPrimalFeasible (fun i j => (A i j : ℝ)) (fun i => (b i : ℝ)) x →
      lower ≤ minPrimalValue (fun j => (c j : ℝ)) x) :
    ∃ pair, rationalPrimalDualAccepts A b c pair = true := by
  obtain ⟨x, y, hx, hy, hgap, _⟩ := exists_rational_minPrimalOptimal
    (fun i j => (A i j : ℝ)) (fun i => (b i : ℝ)) (fun j => (c j : ℝ))
    (fun i j => ⟨A i j, rfl⟩) (fun i => ⟨b i, rfl⟩)
    (fun j => ⟨c j, rfl⟩) hfeasible hbounded
  exact ⟨(x, y), (rationalPrimalDualAccepts_iff A b c (x, y)).mpr ⟨hx, hy, hgap⟩⟩

omit [Fintype Col] in
/-- A finite computable menu: zero primal with zero dual or a unit dual row.
Rows are enumerated by their sorted natural encodings, not by a chosen list
representative of a quotient. Candidates need not be feasible or optimal. -/
def rationalPrimalDualZeroPrimalCandidates [Encodable Row] :
    List ((Col → ℚ) × (Row → ℚ)) :=
  (0, 0) ::
    ((Finset.univ.image (Encodable.encode : Row → ℕ)).sort (· ≤ ·)).filterMap
      (fun code => (Encodable.decode (α := Row) code).map fun row =>
        (0, fun other => if Encodable.encode other = Encodable.encode row then 1 else 0))

/-- Exact LP selection first tests a finite computable menu, then falls back
to canonical rational enumeration. Every branch uses the SAME exact primal/
dual zero-gap test. Only feasibility/boundedness proofs are supplied. -/
def selectRationalPrimalDual [Encodable Row] [Encodable Col]
    (A : Row → Col → ℚ) (b : Row → ℚ) (c : Col → ℚ)
    (hfeasible : ∃ x, MinPrimalFeasible
      (fun i j => (A i j : ℝ)) (fun i => (b i : ℝ)) x)
    (hbounded : ∃ lower : ℝ, ∀ x,
      MinPrimalFeasible (fun i j => (A i j : ℝ)) (fun i => (b i : ℝ)) x →
      lower ≤ minPrimalValue (fun j => (c j : ℝ)) x) :
    (Col → ℚ) × (Row → ℚ) :=
  match (rationalPrimalDualZeroPrimalCandidates (Row := Row) (Col := Col)).find?
      (rationalPrimalDualAccepts A b c) with
  | some candidate => candidate
  | none => Encodable.choose (exists_rationalPrimalDual_accepts A b c hfeasible hbounded)

theorem selectRationalPrimalDual_accepts [Encodable Row] [Encodable Col]
    (A : Row → Col → ℚ) (b : Row → ℚ) (c : Col → ℚ)
    (hfeasible : ∃ x, MinPrimalFeasible
      (fun i j => (A i j : ℝ)) (fun i => (b i : ℝ)) x)
    (hbounded : ∃ lower : ℝ, ∀ x,
      MinPrimalFeasible (fun i j => (A i j : ℝ)) (fun i => (b i : ℝ)) x →
      lower ≤ minPrimalValue (fun j => (c j : ℝ)) x) :
    rationalPrimalDualAccepts A b c (selectRationalPrimalDual A b c hfeasible hbounded) =
      true := by
  unfold selectRationalPrimalDual
  split
  · rename_i candidate hfound
    exact List.find?_some hfound
  · exact Encodable.choose_spec (exists_rationalPrimalDual_accepts A b c hfeasible hbounded)

/-- The computed primal is optimal against ALL real feasible points. -/
theorem selectRationalPrimalDual_optimal [Encodable Row] [Encodable Col]
    (A : Row → Col → ℚ) (b : Row → ℚ) (c : Col → ℚ)
    (hfeasible : ∃ x, MinPrimalFeasible
      (fun i j => (A i j : ℝ)) (fun i => (b i : ℝ)) x)
    (hbounded : ∃ lower : ℝ, ∀ x,
      MinPrimalFeasible (fun i j => (A i j : ℝ)) (fun i => (b i : ℝ)) x →
      lower ≤ minPrimalValue (fun j => (c j : ℝ)) x) :
    let pair := selectRationalPrimalDual A b c hfeasible hbounded
    MinPrimalFeasible (fun i j => (A i j : ℝ)) (fun i => (b i : ℝ))
        (fun j => (pair.1 j : ℝ)) ∧
      ∀ z, MinPrimalFeasible (fun i j => (A i j : ℝ)) (fun i => (b i : ℝ)) z →
        minPrimalValue (fun j => (c j : ℝ)) (fun j => (pair.1 j : ℝ)) ≤
          minPrimalValue (fun j => (c j : ℝ)) z := by
  dsimp only
  obtain ⟨hx, hy, hgap⟩ := (rationalPrimalDualAccepts_iff A b c _).mp
    (selectRationalPrimalDual_accepts A b c hfeasible hbounded)
  refine ⟨hx, fun z hz => ?_⟩
  rw [← hgap]
  exact min_weak_duality hz hy

/-- Executable finite amplification used after rational weights have been selected. -/
def rationalWeightAmplification
    {Outside Child : Type*} [Fintype Outside] [Nonempty Outside] [Fintype Child]
    (weight : Outside → Child → ℚ) : ℚ :=
  max 1 (Finset.univ.sup' Finset.univ_nonempty (fun outside => ∑ child, weight outside child))

theorem one_le_rationalWeightAmplification
    {Outside Child : Type*} [Fintype Outside] [Nonempty Outside] [Fintype Child]
    (weight : Outside → Child → ℚ) : 1 ≤ rationalWeightAmplification weight :=
  le_max_left _ _

/-- The computed rational amplification is exactly the semantic real amplification. -/
theorem rationalWeightAmplification_cast
    {Outside Child : Type*} [Fintype Outside] [Nonempty Outside] [Fintype Child]
    (weight : Outside → Child → ℚ) :
    (rationalWeightAmplification weight : ℝ) =
      max 1 (Finset.univ.sup' Finset.univ_nonempty
        (fun outside => ∑ child, (weight outside child : ℝ))) := by
  unfold rationalWeightAmplification
  rw [Rat.cast_max, Rat.cast_one]
  congr 1
  have hcast := Finset.apply_sup'_eq_sup'_comp
    (s := Finset.univ) (f := fun outside => ∑ child, weight outside child)
    Finset.univ_nonempty (fun value : ℚ => (value : ℝ))
    (fun left right => Rat.cast_max left right)
  simpa only [Function.comp_apply, Rat.cast_sum] using hcast

end Math.LinearProgramming
