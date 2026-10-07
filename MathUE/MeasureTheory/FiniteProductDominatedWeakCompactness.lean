import MathUE.MeasureTheory.BoundedDensityWeakCompactness
import Mathlib.MeasureTheory.Measure.FiniteMeasurePi

/-! # Dominated finite products and a common weak subsequence

Actual independent probability products inherit the product of their marginal
domination constants. Compactness of a finite tuple of probability measures
chooses one subsequence for all marginals; continuity of the probability product
then gives product convergence against every fixed integrable real test.

No convergence of changing comparison kernels, marked calendars, ties, or
distinguished stopping labels is inferred from the marginal weak limits.
-/

noncomputable section

open Set Filter
open scoped Topology BigOperators

namespace MeasureTheory.ProbabilityMeasure

variable {ι : Type*} [Fintype ι] {X : ι → Type*} [∀ i, MeasurableSpace (X i)]

/-- Domination of finitely many actual marginals gives domination of their
independent product. Zero constants and the empty product need no extra premises. -/
theorem pi_le_smul_pi_of_le
    (base law : ∀ i, ProbabilityMeasure (X i)) (constant : ι → NNReal)
    (hbound : ∀ i, (law i : Measure (X i)) ≤ constant i • (base i : Measure (X i))) :
    (ProbabilityMeasure.pi law : Measure (∀ i, X i)) ≤
      (∏ i, constant i) • (ProbabilityMeasure.pi base : Measure (∀ i, X i)) := by
  let scalar : ENNReal := ((∏ i, constant i : NNReal) : ENNReal)
  have hscalar : scalar ≠ ⊤ := ENNReal.coe_ne_top
  have houter :
      OuterMeasure.pi (fun i => (law i : Measure (X i)).toOuterMeasure) ≤
        scalar • OuterMeasure.pi (fun i => (base i : Measure (X i)).toOuterMeasure) := by
    simp only [OuterMeasure.pi]
    rw [OuterMeasure.smul_boundedBy hscalar]
    apply OuterMeasure.le_boundedBy.mpr
    intro s
    apply (OuterMeasure.boundedBy_le s).trans
    change (∏ i, (law i : Measure (X i)) (Function.eval i '' s)) ≤
      scalar * ∏ i, (base i : Measure (X i)) (Function.eval i '' s)
    calc
      _ ≤ ∏ i, (constant i : ENNReal) *
          (base i : Measure (X i)) (Function.eval i '' s) := by
        apply Finset.prod_le_prod
        intro i _
        exact hbound i (Function.eval i '' s)
      _ = _ := by
        rw [Finset.prod_mul_distrib]
        simp only [scalar, ENNReal.ofNNReal_finsetProd]
  apply Measure.le_iff.mpr
  intro s hs
  change Measure.pi (fun i => (law i : Measure (X i))) s ≤
    ((∏ i, constant i) • Measure.pi (fun i => (base i : Measure (X i)))) s
  rw [Measure.coe_nnreal_smul_apply]
  rw [Measure.pi, Measure.pi, toMeasure_apply _ _ hs, toMeasure_apply _ _ hs]
  exact houter s

/-- One subsequence of the actual finite tuple works for every marginal and
for every fixed integrable test of the independent product. The limits and the
subsequence are produced before the test is chosen. -/
theorem exists_dominated_pi_subsequence_integral_tendsto
    [∀ i, TopologicalSpace (X i)] [∀ i, TopologicalSpace.MetrizableSpace (X i)]
    [∀ i, CompactSpace (X i)] [∀ i, BorelSpace (X i)]
    (base : ∀ i, ProbabilityMeasure (X i)) (constant : ι → NNReal)
    (laws : ℕ → ∀ i, ProbabilityMeasure (X i))
    (hbound : ∀ j i,
      (laws j i : Measure (X i)) ≤ constant i • (base i : Measure (X i))) :
    ∃ (limit : ∀ i, ProbabilityMeasure (X i)) (subsequence : ℕ → ℕ),
      StrictMono subsequence ∧
      (∀ i, Tendsto (fun j => laws (subsequence j) i) atTop (𝓝 (limit i))) ∧
      (∀ i, (limit i : Measure (X i)) ≤ constant i • (base i : Measure (X i))) ∧
      Tendsto (fun j => ProbabilityMeasure.pi (laws (subsequence j))) atTop
        (𝓝 (ProbabilityMeasure.pi limit)) ∧
      (ProbabilityMeasure.pi limit : Measure (∀ i, X i)) ≤
        (∏ i, constant i) • (ProbabilityMeasure.pi base : Measure (∀ i, X i)) ∧
      ∀ test : (∀ i, X i) → ℝ,
        Integrable test (ProbabilityMeasure.pi base : Measure (∀ i, X i)) →
        Tendsto (fun j => ∫ x, test x
          ∂(ProbabilityMeasure.pi (laws (subsequence j)) : Measure (∀ i, X i))) atTop
          (𝓝 (∫ x, test x ∂(ProbabilityMeasure.pi limit : Measure (∀ i, X i)))) := by
  obtain ⟨limit, subsequence, hmono, hlimit⟩ := CompactSpace.tendsto_subseq laws
  have hmarginal (i : ι) :
      Tendsto (fun j => laws (subsequence j) i) atTop (𝓝 (limit i)) :=
    hlimit.apply_nhds i
  have hlimitBound (i : ι) :
      (limit i : Measure (X i)) ≤ constant i • (base i : Measure (X i)) :=
    le_of_tendsto_of_le_measure _ (hmarginal i)
      (Eventually.of_forall fun j => hbound (subsequence j) i)
  have hproduct : Tendsto (fun j => ProbabilityMeasure.pi (laws (subsequence j)))
      atTop (𝓝 (ProbabilityMeasure.pi limit)) :=
    ProbabilityMeasure.continuous_pi.continuousAt.tendsto.comp hlimit
  refine ⟨limit, subsequence, hmono, hmarginal, hlimitBound, hproduct,
    pi_le_smul_pi_of_le base limit constant hlimitBound, ?_⟩
  intro test htest
  exact tendsto_integral_of_tendsto_of_le_smul (ProbabilityMeasure.pi base)
    (∏ i, constant i) hproduct
    (Eventually.of_forall fun j =>
      pi_le_smul_pi_of_le base (laws (subsequence j)) constant (hbound (subsequence j)))
    test htest

end MeasureTheory.ProbabilityMeasure
