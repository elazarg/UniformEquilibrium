import MathUE.RealQuantifierElimination.IsolatedRealRootParameters
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.RingTheory.Algebraic.Defs
import Mathlib.Topology.Order.Basic
import Mathlib.Algebra.Order.Archimedean.Basic

/-!
# Isolated-root encodings cover exactly the real-algebraic values

Existence of an encoding is proved using finite polynomial root sets and
rational density. This is a semantic existence theorem, not an executable
encoder from an unencoded real value or an algebraicity proof.
-/

namespace MathUE.RealQuantifierElimination

namespace IsolatedRealRootData

/-- The rational polynomial described by the ascending coefficient list. -/
noncomputable def rationalPolynomial (data : IsolatedRealRootData) : Polynomial ℚ :=
  data.coefficients.foldr (fun coefficient tail =>
    Polynomial.C coefficient + Polynomial.X * tail) 0

theorem aeval_rationalPolynomial (data : IsolatedRealRootData) (value : ℝ) :
    Polynomial.aeval value data.rationalPolynomial = data.evalAt value := by
  rcases data with ⟨coefficients, lower, upper⟩
  induction coefficients with
  | nil => simp [rationalPolynomial, evalAt]
  | cons coefficient coefficients ih =>
      simp only [rationalPolynomial, List.foldr_cons, map_add, map_mul,
        Polynomial.aeval_C, Polynomial.aeval_X, evalAt]
      exact congrArg (fun tail => (coefficient : ℝ) + value * tail) ih

/-- Unique root isolation excludes the zero polynomial, even with zero padding. -/
theorem rationalPolynomial_ne_zero_of_isValid {data : IsolatedRealRootData}
    (hvalid : data.IsValid) : data.rationalPolynomial ≠ 0 := by
  intro hzero
  obtain ⟨value, hvalue, hunique⟩ := hvalid
  let other : ℝ := (value + data.upper) / 2
  have hother : data.RootWithin other := by
    refine ⟨?_, ?_, ?_⟩
    · dsimp only [other]
      linarith [hvalue.1, hvalue.2.1]
    · dsimp only [other]
      linarith [hvalue.2.1]
    · rw [← aeval_rationalPolynomial, hzero, map_zero]
  have heq := hunique other hother
  dsimp only [other] at heq
  linarith [hvalue.2.1]

/-- Every value denoted by a certified description is algebraic over the rationals. -/
theorem isAlgebraic_of_isValid_rootWithin {data : IsolatedRealRootData} {value : ℝ}
    (hvalid : data.IsValid) (hroot : data.RootWithin value) : IsAlgebraic ℚ value := by
  refine ⟨data.rationalPolynomial, rationalPolynomial_ne_zero_of_isValid hvalid, ?_⟩
  rw [aeval_rationalPolynomial]
  exact hroot.2.2

end IsolatedRealRootData

private noncomputable def rationalRealEvaluator : Math.DensePolynomial.Evaluator ℚ ℝ where
  toFun := fun value => (value : ℝ)
  map_zero := Rat.cast_zero
  map_one := Rat.cast_one
  map_add := Rat.cast_add
  map_neg := Rat.cast_neg
  map_mul := Rat.cast_mul

private theorem evalAt_eq_evalMap (coefficients : List ℚ) (lower upper : ℚ) (value : ℝ) :
    (IsolatedRealRootData.mk coefficients lower upper).evalAt value =
      Math.DensePolynomial.evalMap rationalRealEvaluator coefficients value := by
  induction coefficients with
  | nil => simp [IsolatedRealRootData.evalAt, Math.DensePolynomial.evalMap]
  | cons coefficient coefficients ih =>
      simpa [IsolatedRealRootData.evalAt, Math.DensePolynomial.evalMap,
        rationalRealEvaluator] using congrArg (fun tail => (coefficient : ℝ) + value * tail) ih

/-- Every rational polynomial has an ascending finite Horner coefficient presentation. -/
private theorem exists_coefficients_aeval (polynomial : Polynomial ℚ) :
    ∃ coefficients : List ℚ, ∀ value : ℝ,
      (IsolatedRealRootData.mk coefficients 0 0).evalAt value =
        Polynomial.aeval value polynomial := by
  induction polynomial using Polynomial.induction_on with
  | C coefficient =>
      refine ⟨[coefficient], fun value => ?_⟩
      simp [IsolatedRealRootData.evalAt]
  | add left right hleft hright =>
      obtain ⟨leftCoefficients, hleft⟩ := hleft
      obtain ⟨rightCoefficients, hright⟩ := hright
      refine ⟨Math.DensePolynomial.add leftCoefficients rightCoefficients, fun value => ?_⟩
      rw [evalAt_eq_evalMap]
      rw [Math.DensePolynomial.evalMap_add]
      rw [← evalAt_eq_evalMap leftCoefficients 0 0,
        ← evalAt_eq_evalMap rightCoefficients 0 0]
      rw [hleft, hright, map_add]
  | monomial degree coefficient ih =>
      obtain ⟨coefficients, hcoefficients⟩ := ih
      refine ⟨0 :: coefficients, fun value => ?_⟩
      rw [evalAt_eq_evalMap, Math.DensePolynomial.evalMap_cons,
        ← evalAt_eq_evalMap coefficients 0 0]
      simp only [Math.DensePolynomial.Evaluator.apply_zero, zero_add]
      rw [hcoefficients]
      simp only [map_mul, map_pow, Polynomial.aeval_C, Polynomial.aeval_X, pow_succ]
      ring

/-- Around any real value, a rational interval excludes every distinct root of
a nonzero rational polynomial. Repeated roots cause no difficulty. -/
theorem exists_rational_isolating_interval
    {polynomial : Polynomial ℚ} (hnonzero : polynomial ≠ 0) {value : ℝ} :
    ∃ lower upper : ℚ,
      (lower : ℝ) < value ∧ value < (upper : ℝ) ∧
        ∀ other : ℝ, (lower : ℝ) < other → other < (upper : ℝ) →
          Polynomial.aeval other polynomial = 0 → other = value := by
  let realPolynomial := polynomial.map (algebraMap ℚ ℝ)
  have hrealNonzero : realPolynomial ≠ 0 :=
    (Polynomial.map_ne_zero_iff (FaithfulSMul.algebraMap_injective ℚ ℝ)).mpr hnonzero
  let bad : Set ℝ := {other | realPolynomial.IsRoot other} \ {value}
  have hfinite : bad.Finite :=
    (Polynomial.finite_setOf_isRoot hrealNonzero).subset Set.sdiff_subset
  have hvalue : value ∈ badᶜ := by simp [bad]
  have hneighborhood : badᶜ ∈ nhds value := hfinite.isClosed.isOpen_compl.mem_nhds hvalue
  obtain ⟨left, right, hinterval, hsubset⟩ :=
    mem_nhds_iff_exists_Ioo_subset.mp hneighborhood
  obtain ⟨lower, hleft, hlower⟩ := exists_rat_btwn hinterval.1
  obtain ⟨upper, hupper, hright⟩ := exists_rat_btwn hinterval.2
  refine ⟨lower, upper, hlower, hupper, ?_⟩
  intro other hlowerOther hotherUpper hotherRoot
  have houtside := hsubset ⟨hleft.trans hlowerOther, hotherUpper.trans hright⟩
  by_contra hne
  apply houtside
  refine ⟨?_, hne⟩
  change (polynomial.map (algebraMap ℚ ℝ)).eval other = 0
  rw [Polynomial.eval_map]
  exact hotherRoot

/-- Every real-algebraic number has a finite rational isolated-root encoding.
This theorem produces an existential witness, not a computable encoder from `Real`. -/
theorem exists_isolatedRealRootData_of_isAlgebraic {value : ℝ}
    (halgebraic : IsAlgebraic ℚ value) :
    ∃ data : IsolatedRealRootData, data.IsValid ∧ data.RootWithin value := by
  obtain ⟨polynomial, hnonzero, hroot⟩ := halgebraic
  obtain ⟨coefficients, hcoefficients⟩ := exists_coefficients_aeval polynomial
  obtain ⟨lower, upper, hlower, hupper, hisolated⟩ :=
    exists_rational_isolating_interval hnonzero (value := value)
  let data : IsolatedRealRootData := ⟨coefficients, lower, upper⟩
  have heval : ∀ other : ℝ, data.evalAt other = Polynomial.aeval other polynomial :=
    hcoefficients
  have hwithin : data.RootWithin value := ⟨hlower, hupper, (heval value).trans hroot⟩
  refine ⟨data, ⟨value, hwithin, ?_⟩, hwithin⟩
  intro other hother
  exact hisolated other hother.1 hother.2.1 ((heval other).symm.trans hother.2.2)

/-- Valid isolated-root descriptions represent exactly the real-algebraic values. -/
theorem isAlgebraic_iff_exists_isolatedRealRootData (value : ℝ) :
    IsAlgebraic ℚ value ↔
      ∃ data : IsolatedRealRootData, data.IsValid ∧ data.RootWithin value := by
  constructor
  · exact exists_isolatedRealRootData_of_isAlgebraic
  · rintro ⟨data, hvalid, hroot⟩
    exact IsolatedRealRootData.isAlgebraic_of_isValid_rootWithin hvalid hroot

/-- Any finite tuple of real-algebraic values admits certified root parameters.
This proof uses choice to establish existence, not to define an executable encoder. -/
theorem exists_certifiedIsolatedRootParameters {n : Nat} (environment : Fin n → ℝ)
    (halgebraic : ∀ index, IsAlgebraic ℚ (environment index)) :
    ∃ parameters : Fin n → CertifiedIsolatedRealRoot,
      ∀ index, (parameters index).data.RootWithin (environment index) := by
  classical
  choose data hvalid hroot using fun index =>
    exists_isolatedRealRootData_of_isAlgebraic (halgebraic index)
  exact ⟨fun index => ⟨data index, hvalid index⟩, hroot⟩

end MathUE.RealQuantifierElimination
