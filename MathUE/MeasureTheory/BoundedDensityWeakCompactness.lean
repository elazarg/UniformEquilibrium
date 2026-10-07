import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.MeasureTheory.Measure.Portmanteau
import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.Topology.Sequences

/-! # Weak limits of dominated probability measures

Portmanteau on open sets and outer regularity preserve domination by a fixed
measure. Compactness of probability measures on a compact metrizable space
therefore produces an actual dominated probability limit along a subsequence.
The actual Radon–Nikodym density is bounded, and weak convergence under common
domination extends to every fixed integrable real test of the base measure.

This is the measure-valued compactness foundation for bounded likelihoods on a
compact interval. It does not assert convergence of discontinuous moving tests,
unless their actual base-measure L¹ error tends to zero. It does not produce
marked calendars, ties, or stopping-game response caps.
-/

noncomputable section

open Set Filter
open scoped Topology

namespace MeasureTheory.ProbabilityMeasure

variable {X : Type*} [MeasurableSpace X]

private theorem rnDeriv_le_constant_of_le_smul
    (base law : ProbabilityMeasure X) (constant : NNReal)
    (hbound : (law : Measure X) ≤ constant • (base : Measure X)) :
    ∀ᵐ x ∂(base : Measure X),
      (law : Measure X).rnDeriv (base : Measure X) x ≤ (constant : ENNReal) := by
  apply ae_le_of_forall_setLIntegral_le_of_sigmaFinite
    ((law : Measure X).measurable_rnDeriv (base : Measure X))
  intro s _ _
  have h := (Measure.setLIntegral_rnDeriv_le
    (μ := (law : Measure X)) (ν := (base : Measure X)) s).trans (hbound s)
  simpa only [lintegral_const, Measure.restrict_apply_univ,
    Measure.coe_nnreal_smul_apply] using h

/-- A dominated probability has its actual real Radon–Nikodym density, bounded
by the supplied finite constant. No topological or positivity premise is needed. -/
theorem rnDeriv_toReal_spec_of_le_smul
    (base law : ProbabilityMeasure X) (constant : NNReal)
    (hbound : (law : Measure X) ≤ constant • (base : Measure X)) :
    let density := fun x => ((law : Measure X).rnDeriv (base : Measure X) x).toReal
    Measurable density ∧
      (∀ᵐ x ∂(base : Measure X), 0 ≤ density x ∧ density x ≤ (constant : ℝ)) ∧
      (base : Measure X).withDensity (fun x => ENNReal.ofReal (density x)) =
        (law : Measure X) ∧
      ∫ x, density x ∂(base : Measure X) = 1 := by
  dsimp only
  have habs : (law : Measure X) ≪ (base : Measure X) :=
    Measure.absolutelyContinuous_of_le_smul hbound
  refine ⟨((law : Measure X).measurable_rnDeriv (base : Measure X)).ennreal_toReal,
    ?_, ?_, ?_⟩
  · filter_upwards [rnDeriv_le_constant_of_le_smul base law constant hbound] with x hx
    exact ⟨ENNReal.toReal_nonneg, ENNReal.toReal_mono ENNReal.coe_ne_top hx⟩
  · calc
      _ = (base : Measure X).withDensity
          ((law : Measure X).rnDeriv (base : Measure X)) := by
        apply withDensity_congr_ae
        filter_upwards [(law : Measure X).rnDeriv_lt_top (base : Measure X)] with x hx
        exact ENNReal.ofReal_toReal hx.ne
      _ = (law : Measure X) := Measure.withDensity_rnDeriv_eq _ _ habs
  · simpa using Measure.integral_toReal_rnDeriv habs

private theorem dist_integral_le_of_le_smul
    (base law : ProbabilityMeasure X) (constant : NNReal)
    (hbound : (law : Measure X) ≤ constant • (base : Measure X))
    {test approximation : X → ℝ}
    (htest : Integrable test (base : Measure X))
    (happroximation : Integrable approximation (base : Measure X)) :
    dist (∫ x, test x ∂(law : Measure X))
        (∫ x, approximation x ∂(law : Measure X)) ≤
      (constant : ℝ) * ∫ x, ‖test x - approximation x‖ ∂(base : Measure X) := by
  rw [dist_eq_norm, ← integral_sub
    (htest.smul_measure_nnreal.mono_measure hbound)
    (happroximation.smul_measure_nnreal.mono_measure hbound)]
  calc
    _ ≤ ∫ x, ‖test x - approximation x‖ ∂(law : Measure X) :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ x, ‖test x - approximation x‖ ∂(constant • (base : Measure X)) :=
      integral_mono_measure hbound (Eventually.of_forall fun _ => norm_nonneg _)
        (htest.sub happroximation).norm.smul_measure_nnreal
    _ = _ := by rw [integral_smul_nnreal_measure]; rfl

variable [TopologicalSpace X]

/-- Domination passes to a weak probability limit. Neither compactness nor an
already supplied density for the limit is needed. -/
theorem le_of_tendsto_of_le_measure
    [OpensMeasurableSpace X] [HasOuterApproxClosed X]
    {J : Type*} {filter : Filter J} [filter.NeBot]
    {laws : J → ProbabilityMeasure X} {limit : ProbabilityMeasure X}
    (bound : Measure X) [bound.OuterRegular]
    (hlimit : Tendsto laws filter (𝓝 limit))
    (hbound : ∀ᶠ j in filter, (laws j : Measure X) ≤ bound) :
    (limit : Measure X) ≤ bound := by
  apply Measure.le_iff'.mpr
  intro s
  rw [s.measure_eq_iInf_isOpen bound]
  refine le_iInf fun U => le_iInf fun hsU => le_iInf fun hU => ?_
  apply (measure_mono hsU).trans
  apply (le_liminf_measure_open_of_tendsto hlimit hU).trans
  apply (Filter.liminf_le_limsup).trans
  exact Filter.limsup_le_of_le (by isBoundedDefault)
    (hbound.mono fun j hj => Measure.le_iff'.mp hj U)

/-- Every sequence of probabilities uniformly dominated by a finite multiple
of a fixed base probability on a compact metrizable Borel space has a dominated
probability subsequential limit. The constant need not be positive as a premise;
inconsistent bounds simply admit no such sequence. -/
theorem exists_dominated_subsequence
    [TopologicalSpace.MetrizableSpace X] [CompactSpace X] [BorelSpace X]
    (base : ProbabilityMeasure X) (constant : NNReal)
    (laws : ℕ → ProbabilityMeasure X)
    (hbound : ∀ j, (laws j : Measure X) ≤ constant • (base : Measure X)) :
    ∃ (limit : ProbabilityMeasure X) (subsequence : ℕ → ℕ),
      StrictMono subsequence ∧
      Tendsto (laws ∘ subsequence) atTop (𝓝 limit) ∧
      (limit : Measure X) ≤ constant • (base : Measure X) := by
  obtain ⟨limit, subsequence, hmono, hlimit⟩ := CompactSpace.tendsto_subseq laws
  refine ⟨limit, subsequence, hmono, hlimit, ?_⟩
  exact le_of_tendsto_of_le_measure _ hlimit
    (Eventually.of_forall fun j => hbound (subsequence j))

/-- Weak convergence under eventual common domination gives convergence against
every fixed real test integrable under the base probability. -/
theorem tendsto_integral_of_tendsto_of_le_smul
    [TopologicalSpace.MetrizableSpace X] [CompactSpace X] [BorelSpace X]
    {J : Type*} {filter : Filter J} [filter.NeBot]
    (base : ProbabilityMeasure X) (constant : NNReal)
    {laws : J → ProbabilityMeasure X} {limit : ProbabilityMeasure X}
    (hlimit : Tendsto laws filter (𝓝 limit))
    (hbound : ∀ᶠ j in filter, (laws j : Measure X) ≤ constant • (base : Measure X))
    (test : X → ℝ) (htest : Integrable test (base : Measure X)) :
    Tendsto (fun j => ∫ x, test x ∂(laws j : Measure X)) filter
      (𝓝 (∫ x, test x ∂(limit : Measure X))) := by
  have hlimitBound := le_of_tendsto_of_le_measure _ hlimit hbound
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  let tolerance := ε / (4 * ((constant : ℝ) + 1))
  have htolerance : 0 < tolerance := by dsimp [tolerance]; positivity
  obtain ⟨approximation, herror, happroximation⟩ :=
    htest.exists_boundedContinuous_integral_sub_le htolerance
  have hsmall : (constant : ℝ) * tolerance < ε / 4 := by
    dsimp only [tolerance]
    rw [← mul_div_assoc]
    apply (div_lt_iff₀ (by positivity)).mpr
    nlinarith
  have hcontinuous :=
    (tendsto_iff_forall_integral_tendsto.mp hlimit) approximation
  have hclose := (Metric.tendsto_nhds.mp hcontinuous) (ε / 2) (by positivity)
  filter_upwards [hbound, hclose] with j hj hclosej
  have hfirst := (dist_integral_le_of_le_smul base (laws j) constant hj
    htest happroximation).trans (mul_le_mul_of_nonneg_left herror constant.coe_nonneg)
  have hlast := (dist_integral_le_of_le_smul base limit constant hlimitBound
    htest happroximation).trans (mul_le_mul_of_nonneg_left herror constant.coe_nonneg)
  have htriangle := dist_triangle
    (∫ x, test x ∂(laws j : Measure X))
    (∫ x, approximation x ∂(laws j : Measure X))
    (∫ x, test x ∂(limit : Measure X))
  have htriangle' := dist_triangle
    (∫ x, approximation x ∂(laws j : Measure X))
    (∫ x, approximation x ∂(limit : Measure X))
    (∫ x, test x ∂(limit : Measure X))
  rw [dist_comm (∫ x, approximation x ∂(limit : Measure X))] at htriangle'
  linarith

/-- Moving integrable tests may be combined with weakly converging dominated
laws when their actual L¹ error under the base probability tends to zero.
Weak convergence of the laws alone does not supply this test-error premise. -/
theorem tendsto_integral_moving_test_of_tendsto_of_le_smul
    [TopologicalSpace.MetrizableSpace X] [CompactSpace X] [BorelSpace X]
    {J : Type*} {filter : Filter J} [filter.NeBot]
    (base : ProbabilityMeasure X) (constant : NNReal)
    {laws : J → ProbabilityMeasure X} {limit : ProbabilityMeasure X}
    (hlimit : Tendsto laws filter (𝓝 limit))
    (hbound : ∀ᶠ j in filter, (laws j : Measure X) ≤ constant • (base : Measure X))
    (test : X → ℝ) (htest : Integrable test (base : Measure X))
    (movingTest : J → X → ℝ)
    (hmoving : ∀ᶠ j in filter, Integrable (movingTest j) (base : Measure X))
    (herror : Tendsto
      (fun j => ∫ x, ‖movingTest j x - test x‖ ∂(base : Measure X)) filter (𝓝 0)) :
    Tendsto (fun j => ∫ x, movingTest j x ∂(laws j : Measure X)) filter
      (𝓝 (∫ x, test x ∂(limit : Measure X))) := by
  have hfixed := tendsto_integral_of_tendsto_of_le_smul
    base constant hlimit hbound test htest
  have hscaled : Tendsto
      (fun j => (constant : ℝ) * ∫ x, ‖movingTest j x - test x‖ ∂(base : Measure X))
      filter (𝓝 0) := by
    simpa only [mul_zero] using tendsto_const_nhds.mul herror
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have hsmall := hscaled.eventually (gt_mem_nhds (show (0 : ℝ) < ε / 2 by positivity))
  have hclose := (Metric.tendsto_nhds.mp hfixed) (ε / 2) (by positivity)
  filter_upwards [hbound, hmoving, hsmall, hclose] with j hj hmovingj hsmallj hclosej
  have herr := dist_integral_le_of_le_smul base (laws j) constant hj hmovingj htest
  have htriangle := dist_triangle
    (∫ x, movingTest j x ∂(laws j : Measure X))
    (∫ x, test x ∂(laws j : Measure X))
    (∫ x, test x ∂(limit : Measure X))
  linarith

/-- One dominated probability subsequence works for all fixed integrable real
tests. The subsequence is chosen before the test function. -/
theorem exists_dominated_subsequence_integral_tendsto
    [TopologicalSpace.MetrizableSpace X] [CompactSpace X] [BorelSpace X]
    (base : ProbabilityMeasure X) (constant : NNReal)
    (laws : ℕ → ProbabilityMeasure X)
    (hbound : ∀ j, (laws j : Measure X) ≤ constant • (base : Measure X)) :
    ∃ (limit : ProbabilityMeasure X) (subsequence : ℕ → ℕ),
      StrictMono subsequence ∧
      Tendsto (laws ∘ subsequence) atTop (𝓝 limit) ∧
      (limit : Measure X) ≤ constant • (base : Measure X) ∧
      ∀ test : X → ℝ, Integrable test (base : Measure X) →
        Tendsto (fun j => ∫ x, test x ∂(laws (subsequence j) : Measure X)) atTop
          (𝓝 (∫ x, test x ∂(limit : Measure X))) := by
  obtain ⟨limit, subsequence, hmono, hlimit, hlimitBound⟩ :=
    exists_dominated_subsequence base constant laws hbound
  refine ⟨limit, subsequence, hmono, hlimit, hlimitBound, ?_⟩
  intro test htest
  exact tendsto_integral_of_tendsto_of_le_smul base constant hlimit
    (Eventually.of_forall fun j => hbound (subsequence j)) test htest

end MeasureTheory.ProbabilityMeasure
