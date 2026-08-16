import Mathlib

/-!
# Kakutani dichotomy for infinite product laws: the absolute-continuity direction

**Layer-2 item 4, product case.** For independent finite-alphabet steps whose per-step laws
`p t, q t : I → ℝ` share support (mutual per-step absolute continuity) and whose Hellinger
affinities `ρ t := ∑ i, √(p t i * q t i)` satisfy `Summable (fun t => 1 - ρ t)`, the infinite
product measures `P := ⊗_t (p t)` and `Q := ⊗_t (q t)` on `ℕ → I` (built with
`MeasureTheory.Measure.infinitePi`, this pin's infinite-product API) are **mutually absolutely
continuous** (`product_mutuallyAC`, with the two directions as
`productLaw_absolutelyContinuous`). The consumer bridge `hdich_of_product` instantiates this
for the mixture family `q t i = (1 - δ t) * p t i + δ t * s t i` with `δ t ∈ [0, 1/2]`,
positive base `p`, and a uniform χ²-bound, concluding `P ≪ Q` from
`Summable (fun t => δ t ^ 2)` — exactly the hypothesis `hdich` that
`experiments/AnytimeDetectionConditional.lean` consumes. Together the two files give the full
Q38 anytime-detection impossibility for independent deviation rates.

## Proof route (disclosed deviation from the martingale skeleton)

The horizon-`N` likelihood ratio `L N` appears here as `partialDensity`, and the finite-horizon
density identity `⊗(hybrid N) = P.withDensity (L N)` — where `hybrid N` plays `q` before time
`N` and `p` after — is proved by box-value uniqueness (`Measure.eq_infinitePi`,
`productLaw_hybrid_eq_withDensity`); hence every `P`-null set is null for every hybrid law.
The passage to the infinite horizon is done **without martingale convergence**: any measurable
`A` is approximated by a cylinder `C` in `(Q + hybrid N)`-measure
(`Measure.MeasureDense.of_generateFrom_isSetAlgebra_finite` applied to the cylinder algebra),
and `Q` and the hybrid law are compared on `C` by a finite-dimensional Cauchy–Schwarz /
Hellinger total-variation bound (`abs_sum_sub_sum_le`) whose constant
`2 * √(2 * (1 - ∏ ρ))` is controlled, uniformly over all cylinders, by the affinity tail sum
`tailSum N := ∑' k, (1 - ρ (k + N))`, which vanishes as `N → ∞` by the summability
hypothesis. This route needs neither `condExp`, filtrations, uniform integrability, L²
martingale convergence, nor `Multipliable`/infinite-product-of-reals machinery: the
`E_P[L N] = 1` / `E_P[√(L N)] = ∏ ρ` identities of the original skeleton are subsumed by the
same finite-`N` product computations (`lintegral_infinitePi_prod`, `Fintype.prod_sum`) that
the martingale route would have rested on.

## Main statements

* `productLaw_absolutelyContinuous` — rung F1, one direction: under nonnegativity,
  normalization, shared support, and `Summable (fun t => 1 - ρ t)`, `Q ≪ P`.
* `product_mutuallyAC` — rung F1, both directions (`Q ≪ P ∧ P ≪ Q`), by applying the main
  lemma twice with the roles of `p` and `q` swapped; no Kolmogorov 0-1 law is used.
* `hdich_of_product` — the consumer bridge: for the mixture family with square-summable
  mixing rates, `P ≪ Q` (E62's exact hypothesis shape, product instantiation).

## Next stage

The adapted-kernel version — history-dependent steps, the repo's
`GameTheory.Concepts.Stochastic.Core.Probability.InfinitePlayMeasure` play-measure instantiation via
`Kernel.trajMeasure` — is the named next stage; this file is deliberately kernel-free
(independent steps only). Library-bound (kraft) after ratification, following the
`fixed-point-theorems-lean4` pattern.
-/


namespace Research.KakutaniProductDichotomy

open MeasureTheory Filter
open scoped ENNReal Topology symmDiff

variable {I : Type*} [Fintype I] [MeasurableSpace I] [DiscreteMeasurableSpace I]

/-! ## Per-step laws on the finite alphabet -/

/-- The measure on the finite alphabet `I` with real mass function `f`. -/
noncomputable def stepMeasure (f : I → ℝ) : Measure I :=
  ∑ i, ENNReal.ofReal (f i) • Measure.dirac i

theorem stepMeasure_apply (f : I → ℝ) (s : Set I) :
    stepMeasure f s = ∑ i, s.indicator (fun j => ENNReal.ofReal (f j)) i := by
  rw [stepMeasure, Measure.finsetSum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Measure.smul_apply, Measure.dirac_apply, smul_eq_mul]
  by_cases hi : i ∈ s
  · rw [Set.indicator_of_mem hi, Set.indicator_of_mem hi, Pi.one_apply, mul_one]
  · rw [Set.indicator_of_notMem hi, Set.indicator_of_notMem hi, mul_zero]

theorem stepMeasure_singleton (f : I → ℝ) (a : I) :
    stepMeasure f {a} = ENNReal.ofReal (f a) := by
  rw [stepMeasure_apply]
  rw [Finset.sum_eq_single a (fun b _ hb => by
    rw [Set.indicator_of_notMem (by simpa using hb)]) (fun h => absurd (Finset.mem_univ a) h)]
  simp

theorem isProbabilityMeasure_stepMeasure {f : I → ℝ} (hf0 : ∀ i, 0 ≤ f i)
    (hf1 : ∑ i, f i = 1) : IsProbabilityMeasure (stepMeasure f) := by
  constructor
  rw [stepMeasure_apply]
  simp only [Set.indicator_univ]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => hf0 i), hf1, ENNReal.ofReal_one]

theorem lintegral_stepMeasure (f : I → ℝ) (g : I → ℝ≥0∞) :
    ∫⁻ x, g x ∂stepMeasure f = ∑ i, g i * ENNReal.ofReal (f i) := by
  rw [lintegral_fintype]
  exact Finset.sum_congr rfl fun i _ => by rw [stepMeasure_singleton]

/-! ## Hellinger affinity -/

/-- The Hellinger affinity of two mass functions on `I`: `∑ i, √(f i * g i)`.
The brief's `ρ t` is `affinity (p t) (q t)`. -/
noncomputable def affinity (f g : I → ℝ) : ℝ := ∑ i, Real.sqrt (f i * g i)

omit [MeasurableSpace I] [DiscreteMeasurableSpace I] in
theorem affinity_nonneg (f g : I → ℝ) : 0 ≤ affinity f g :=
  Finset.sum_nonneg fun _ _ => Real.sqrt_nonneg _

omit [MeasurableSpace I] [DiscreteMeasurableSpace I] in
theorem affinity_comm (f g : I → ℝ) : affinity f g = affinity g f :=
  Finset.sum_congr rfl fun i _ => by rw [mul_comm]

omit [MeasurableSpace I] [DiscreteMeasurableSpace I] in
theorem affinity_le_one {f g : I → ℝ} (hf0 : ∀ i, 0 ≤ f i) (hg0 : ∀ i, 0 ≤ g i)
    (hf1 : ∑ i, f i = 1) (hg1 : ∑ i, g i = 1) : affinity f g ≤ 1 := by
  have h : ∀ i ∈ Finset.univ, Real.sqrt (f i * g i) ≤ (f i + g i) / 2 := by
    intro i _
    have h2 : f i * g i ≤ ((f i + g i) / 2) ^ 2 := by nlinarith [sq_nonneg (f i - g i)]
    calc Real.sqrt (f i * g i) ≤ Real.sqrt (((f i + g i) / 2) ^ 2) := Real.sqrt_le_sqrt h2
      _ = (f i + g i) / 2 := Real.sqrt_sq (by linarith [hf0 i, hg0 i])
  calc affinity f g ≤ ∑ i, (f i + g i) / 2 := Finset.sum_le_sum h
    _ = 1 := by rw [← Finset.sum_div, Finset.sum_add_distrib, hf1, hg1]; norm_num

omit [MeasurableSpace I] [DiscreteMeasurableSpace I] in
/-- The brief's positivity fact: under shared support and normalization of `f`, the affinity
is strictly positive (some `i` has `f i > 0`, hence `g i > 0`). -/
theorem affinity_pos {f g : I → ℝ} (hf0 : ∀ i, 0 ≤ f i) (hg0 : ∀ i, 0 ≤ g i)
    (hf1 : ∑ i, f i = 1) (hsupp : ∀ i, f i = 0 ↔ g i = 0) : 0 < affinity f g := by
  obtain ⟨i, hi⟩ : ∃ i, f i ≠ 0 := by
    by_contra h
    push Not at h
    rw [Finset.sum_eq_zero fun i _ => h i] at hf1
    exact one_ne_zero hf1.symm
  have hfi : 0 < f i := (hf0 i).lt_of_ne (Ne.symm hi)
  have hgi : 0 < g i := (hg0 i).lt_of_ne (Ne.symm fun h => hi ((hsupp i).mpr h))
  exact (Real.sqrt_pos.mpr (mul_pos hfi hgi)).trans_le
    (Finset.single_le_sum (fun j _ => Real.sqrt_nonneg (f j * g j)) (Finset.mem_univ i))

omit [MeasurableSpace I] [DiscreteMeasurableSpace I] in
theorem affinity_self {f : I → ℝ} (hf0 : ∀ i, 0 ≤ f i) (hf1 : ∑ i, f i = 1) :
    affinity f f = 1 := by
  rw [affinity, ← hf1]
  exact Finset.sum_congr rfl fun i _ => Real.sqrt_mul_self (hf0 i)

/-! ## Elementary product estimates -/

/-- `1 - ∏ f ≤ ∑ (1 - f)` for factors in `[0, 1]`. -/
theorem one_sub_prod_le_sum_one_sub {α : Type*} (s : Finset α) (f : α → ℝ) :
    (∀ a ∈ s, 0 ≤ f a) → (∀ a ∈ s, f a ≤ 1) →
      1 - ∏ a ∈ s, f a ≤ ∑ a ∈ s, (1 - f a) := by
  induction s using Finset.cons_induction with
  | empty => intro _ _; simp
  | cons a s ha ih =>
    intro h0 h1
    rw [Finset.prod_cons, Finset.sum_cons]
    have h0' : ∀ b ∈ s, 0 ≤ f b := fun b hb => h0 b (Finset.mem_cons_of_mem hb)
    have h1' : ∀ b ∈ s, f b ≤ 1 := fun b hb => h1 b (Finset.mem_cons_of_mem hb)
    have iha := ih h0' h1'
    have ha1 : f a ≤ 1 := h1 a (Finset.mem_cons_self a s)
    have hP1 : ∏ b ∈ s, f b ≤ 1 := Finset.prod_le_one h0' h1'
    nlinarith [mul_nonneg (sub_nonneg.mpr ha1) (sub_nonneg.mpr hP1)]

/-- **The finite-dimensional Hellinger/total-variation estimate** (Cauchy–Schwarz): two
probability vectors `A B` on a finite type differ, on any event `S`, by at most
`2 * √(2 * (1 - r))` where `r = ∑ √(A·B)` is their Hellinger affinity. -/
theorem abs_sum_sub_sum_le {β : Type*} [Fintype β] (A B : β → ℝ)
    (hA0 : ∀ y, 0 ≤ A y) (hB0 : ∀ y, 0 ≤ B y)
    (hA1 : ∑ y, A y = 1) (hB1 : ∑ y, B y = 1) (S : Finset β) :
    |(∑ y ∈ S, A y) - ∑ y ∈ S, B y| ≤
      2 * Real.sqrt (2 * (1 - ∑ y, Real.sqrt (A y * B y))) := by
  set r := ∑ y, Real.sqrt (A y * B y) with hr
  have hr1 : r ≤ 1 := by
    have h : ∀ y ∈ Finset.univ, Real.sqrt (A y * B y) ≤ (A y + B y) / 2 := by
      intro y _
      have h2 : A y * B y ≤ ((A y + B y) / 2) ^ 2 := by nlinarith [sq_nonneg (A y - B y)]
      calc Real.sqrt (A y * B y) ≤ Real.sqrt (((A y + B y) / 2) ^ 2) := Real.sqrt_le_sqrt h2
        _ = (A y + B y) / 2 := Real.sqrt_sq (by linarith [hA0 y, hB0 y])
    calc r ≤ ∑ y, (A y + B y) / 2 := Finset.sum_le_sum h
      _ = 1 := by rw [← Finset.sum_div, Finset.sum_add_distrib, hA1, hB1]; norm_num
  have hpt : ∀ y, |A y - B y| =
      |Real.sqrt (A y) - Real.sqrt (B y)| * (Real.sqrt (A y) + Real.sqrt (B y)) := by
    intro y
    have h1 : A y - B y =
        (Real.sqrt (A y) + Real.sqrt (B y)) * (Real.sqrt (A y) - Real.sqrt (B y)) := by
      rw [← sq_sub_sq, Real.sq_sqrt (hA0 y), Real.sq_sqrt (hB0 y)]
    rw [h1, abs_mul, abs_of_nonneg (by positivity), mul_comm]
  have hsq1 : ∑ y, |Real.sqrt (A y) - Real.sqrt (B y)| ^ 2 = 2 - 2 * r := by
    have h : ∀ y ∈ Finset.univ, |Real.sqrt (A y) - Real.sqrt (B y)| ^ 2 =
        A y + B y - 2 * Real.sqrt (A y * B y) := by
      intro y _
      have e1 := Real.sq_sqrt (hA0 y)
      have e2 := Real.sq_sqrt (hB0 y)
      have e3 : Real.sqrt (A y * B y) = Real.sqrt (A y) * Real.sqrt (B y) :=
        Real.sqrt_mul (hA0 y) _
      rw [sq_abs, e3]
      linear_combination e1 + e2
    rw [Finset.sum_congr rfl h, Finset.sum_sub_distrib, Finset.sum_add_distrib, hA1, hB1,
      ← Finset.mul_sum, ← hr]
    ring
  have hsq2 : ∑ y, (Real.sqrt (A y) + Real.sqrt (B y)) ^ 2 = 2 + 2 * r := by
    have h : ∀ y ∈ Finset.univ, (Real.sqrt (A y) + Real.sqrt (B y)) ^ 2 =
        A y + B y + 2 * Real.sqrt (A y * B y) := by
      intro y _
      have e1 := Real.sq_sqrt (hA0 y)
      have e2 := Real.sq_sqrt (hB0 y)
      have e3 : Real.sqrt (A y * B y) = Real.sqrt (A y) * Real.sqrt (B y) :=
        Real.sqrt_mul (hA0 y) _
      rw [e3]
      linear_combination e1 + e2
    rw [Finset.sum_congr rfl h, Finset.sum_add_distrib, Finset.sum_add_distrib, hA1, hB1,
      ← Finset.mul_sum, ← hr]
    ring
  have hCS := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ
    (fun y => |Real.sqrt (A y) - Real.sqrt (B y)|)
    (fun y => Real.sqrt (A y) + Real.sqrt (B y))
  have hfac2 : Real.sqrt (∑ y, (Real.sqrt (A y) + Real.sqrt (B y)) ^ 2) ≤ 2 := by
    rw [hsq2]
    calc Real.sqrt (2 + 2 * r) ≤ Real.sqrt 4 := Real.sqrt_le_sqrt (by linarith)
      _ = 2 := by
          rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)]
  calc |(∑ y ∈ S, A y) - ∑ y ∈ S, B y|
      = |∑ y ∈ S, (A y - B y)| := by rw [Finset.sum_sub_distrib]
    _ ≤ ∑ y ∈ S, |A y - B y| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ y, |A y - B y| :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S)
          fun y _ _ => abs_nonneg _
    _ = ∑ y, |Real.sqrt (A y) - Real.sqrt (B y)| * (Real.sqrt (A y) + Real.sqrt (B y)) :=
        Finset.sum_congr rfl fun y _ => hpt y
    _ ≤ Real.sqrt (∑ y, |Real.sqrt (A y) - Real.sqrt (B y)| ^ 2) *
          Real.sqrt (∑ y, (Real.sqrt (A y) + Real.sqrt (B y)) ^ 2) := hCS
    _ ≤ Real.sqrt (2 - 2 * r) * 2 := by
        rw [hsq1]
        exact mul_le_mul le_rfl hfac2 (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    _ = 2 * Real.sqrt (2 * (1 - r)) := by
        rw [show (2 : ℝ) * (1 - r) = 2 - 2 * r by ring, mul_comm]

omit [MeasurableSpace I] [DiscreteMeasurableSpace I] in
/-- The product-law instantiation of `abs_sum_sub_sum_le`: two product laws on a finite
product alphabet differ on any event by at most `2 * √(2 * (1 - ∏ ρ))`, the product of the
per-coordinate Hellinger affinities. -/
theorem abs_sum_prod_sub_le {α : Type*} [Fintype α] (u v : α → I → ℝ)
    (hu0 : ∀ a i, 0 ≤ u a i) (hv0 : ∀ a i, 0 ≤ v a i)
    (hu1 : ∀ a, ∑ i, u a i = 1) (hv1 : ∀ a, ∑ i, v a i = 1) (S : Finset (α → I)) :
    |(∑ y ∈ S, ∏ a, u a (y a)) - ∑ y ∈ S, ∏ a, v a (y a)| ≤
      2 * Real.sqrt (2 * (1 - ∏ a, affinity (u a) (v a))) := by
  classical
  have hu1' : ∑ y : α → I, ∏ a, u a (y a) = 1 :=
    calc ∑ y : α → I, ∏ a, u a (y a) = ∏ a, ∑ i, u a i := (Fintype.prod_sum _).symm
      _ = 1 := by simp [hu1]
  have hv1' : ∑ y : α → I, ∏ a, v a (y a) = 1 :=
    calc ∑ y : α → I, ∏ a, v a (y a) = ∏ a, ∑ i, v a i := (Fintype.prod_sum _).symm
      _ = 1 := by simp [hv1]
  have h := abs_sum_sub_sum_le (fun y => ∏ a, u a (y a)) (fun y => ∏ a, v a (y a))
    (fun y => Finset.prod_nonneg fun a _ => hu0 a (y a))
    (fun y => Finset.prod_nonneg fun a _ => hv0 a (y a)) hu1' hv1' S
  have hAff : ∑ y : α → I, Real.sqrt ((∏ a, u a (y a)) * ∏ a, v a (y a)) =
      ∏ a, affinity (u a) (v a) := by
    have h1 : ∀ y : α → I, Real.sqrt ((∏ a, u a (y a)) * ∏ a, v a (y a)) =
        ∏ a, Real.sqrt (u a (y a) * v a (y a)) := by
      intro y
      rw [← Finset.prod_mul_distrib,
        Real.sqrt_prod _ fun a _ => mul_nonneg (hu0 a (y a)) (hv0 a (y a))]
    exact (Finset.sum_congr rfl fun y _ => h1 y).trans
      (Fintype.prod_sum fun a i => Real.sqrt (u a i * v a i)).symm
  calc |(∑ y ∈ S, ∏ a, u a (y a)) - ∑ y ∈ S, ∏ a, v a (y a)|
      ≤ 2 * Real.sqrt
          (2 * (1 - ∑ y : α → I, Real.sqrt ((∏ a, u a (y a)) * ∏ a, v a (y a)))) := h
    _ = 2 * Real.sqrt (2 * (1 - ∏ a, affinity (u a) (v a))) := by rw [hAff]

/-! ## The infinite product laws and their cylinder masses -/

/-- The infinite product law on `ℕ → I` with per-step mass functions `f t`. -/
noncomputable def productLaw (f : ℕ → I → ℝ) : Measure (ℕ → I) :=
  Measure.infinitePi fun t => stepMeasure (f t)

/-- The mass a product law gives a cylinder, as `ENNReal.ofReal` of a finite real sum of
finite real products: the base computation every later estimate reduces to. -/
theorem productLaw_cylinder (f : ℕ → I → ℝ) (hf0 : ∀ t i, 0 ≤ f t i)
    (hf1 : ∀ t, ∑ i, f t i = 1) (F : Finset ℕ) (S : Finset ((t : F) → I)) :
    productLaw f (cylinder F (↑S : Set ((t : F) → I))) =
      ENNReal.ofReal (∑ y ∈ S, ∏ t : F, f t (y t)) := by
  haveI : ∀ t, IsProbabilityMeasure (stepMeasure (f t)) := fun t =>
    isProbabilityMeasure_stepMeasure (hf0 t) (hf1 t)
  calc productLaw f (cylinder F (↑S : Set ((t : F) → I)))
      = Measure.pi (fun t : F => stepMeasure (f t)) ↑S :=
        Measure.infinitePi_cylinder _ MeasurableSet.of_discrete
    _ = ∑ y ∈ S, Measure.pi (fun t : F => stepMeasure (f t)) {y} :=
        sum_measure_singleton.symm
    _ = ∑ y ∈ S, ENNReal.ofReal (∏ t : F, f t (y t)) := by
        refine Finset.sum_congr rfl fun y _ => ?_
        rw [Measure.pi_singleton, ENNReal.ofReal_prod_of_nonneg fun t _ => hf0 _ (y t)]
        exact Finset.prod_congr rfl fun t _ => stepMeasure_singleton _ _
    _ = ENNReal.ofReal (∑ y ∈ S, ∏ t : F, f t (y t)) :=
        (ENNReal.ofReal_sum_of_nonneg fun y _ =>
          Finset.prod_nonneg fun t _ => hf0 _ (y t)).symm

omit [MeasurableSpace I] [DiscreteMeasurableSpace I] in
/-- Distribute a sum over the finite product alphabet through a product of per-coordinate
factors (`Fintype.prod_sum`, specialized to `ℝ≥0∞`). -/
theorem sum_prod_eq_prod_sum {α : Type*} [Fintype α] [DecidableEq α] (h : α → I → ℝ≥0∞) :
    ∑ y : α → I, ∏ a, h a (y a) = ∏ a, ∑ i, h a i :=
  (Fintype.prod_sum h).symm

omit [Fintype I] in
/-- **The finite-`N` product identity** behind the skeleton's `E_P[L N] = 1` and
`E_P[√(L N)] = ∏ ρ`: the `infinitePi`-integral of a finite product of per-coordinate
factors is the product of the per-coordinate integrals. -/
theorem lintegral_infinitePi_prod [Finite I]
    (μ : ℕ → Measure I) [∀ t, IsProbabilityMeasure (μ t)]
    (F : Finset ℕ) (g : ℕ → I → ℝ≥0∞) :
    ∫⁻ ω, ∏ t ∈ F, g t (ω t) ∂Measure.infinitePi μ = ∏ t ∈ F, ∫⁻ x, g t x ∂μ t := by
  letI := Fintype.ofFinite I
  have key : ∫⁻ y, (∏ t : F, g t (y t)) ∂Measure.pi (fun t : F => μ t) =
      ∏ t : F, ∫⁻ x, g t x ∂μ t := by
    rw [lintegral_fintype]
    calc ∑ y : (t : F) → I, (∏ t : F, g t (y t)) * Measure.pi (fun t : F => μ t) {y}
        = ∑ y : (t : F) → I, ∏ t : F, (g t (y t) * μ t {y t}) := by
          refine Finset.sum_congr rfl fun y _ => ?_
          rw [Measure.pi_singleton, Finset.prod_mul_distrib]
      _ = ∏ t : F, ∑ a : I, g t a * μ t {a} :=
          sum_prod_eq_prod_sum fun (t : F) (a : I) => g t a * μ t {a}
      _ = ∏ t : F, ∫⁻ x, g t x ∂μ t :=
          Finset.prod_congr rfl fun t _ => (lintegral_fintype _).symm
  have hres := lintegral_restrict_infinitePi (μ := μ) (s := F)
    (f := fun y : (t : F) → I => ∏ t : F, g t (y t)) Measurable.of_discrete
  calc ∫⁻ ω, ∏ t ∈ F, g t (ω t) ∂Measure.infinitePi μ
      = ∫⁻ ω, ∏ t : F, g t (F.restrict ω t) ∂Measure.infinitePi μ := by
        refine lintegral_congr fun ω => ?_
        rw [Finset.univ_eq_attach]
        exact (Finset.prod_attach F fun t => g t (ω t)).symm
    _ = ∏ t : F, ∫⁻ x, g t x ∂μ t := hres.trans key
    _ = ∏ t ∈ F, ∫⁻ x, g t x ∂μ t := by
        rw [Finset.univ_eq_attach]
        exact Finset.prod_attach F fun t => ∫⁻ x, g t x ∂μ t

/-! ## The density martingale at finite horizons -/

/-- The horizon-`N` likelihood ratio (the skeleton's `L N`), as an `ℝ≥0∞`-valued density:
`∏_{t < N} (q t (ω t)) / (p t (ω t))` with `ENNReal` division. -/
noncomputable def partialDensity (p q : ℕ → I → ℝ) (N : ℕ) (ω : ℕ → I) : ℝ≥0∞ :=
  ∏ t ∈ Finset.range N, ENNReal.ofReal (q t (ω t)) / ENNReal.ofReal (p t (ω t))

/-- The horizon-`N` hybrid family: play `q` strictly before time `N`, `p` from `N` on. -/
def hybrid (p q : ℕ → I → ℝ) (N t : ℕ) : I → ℝ := if t < N then q t else p t

omit [Fintype I] [MeasurableSpace I] [DiscreteMeasurableSpace I] in
theorem hybrid_of_lt {p q : ℕ → I → ℝ} {N t : ℕ} (h : t < N) : hybrid p q N t = q t :=
  if_pos h

omit [Fintype I] [MeasurableSpace I] [DiscreteMeasurableSpace I] in
theorem hybrid_of_le {p q : ℕ → I → ℝ} {N t : ℕ} (h : N ≤ t) : hybrid p q N t = p t :=
  if_neg (not_lt.mpr h)

omit [Fintype I] [MeasurableSpace I] [DiscreteMeasurableSpace I] in
theorem hybrid_nonneg {p q : ℕ → I → ℝ} (hp0 : ∀ t i, 0 ≤ p t i) (hq0 : ∀ t i, 0 ≤ q t i)
    (N : ℕ) : ∀ t i, 0 ≤ hybrid p q N t i := by
  intro t i
  by_cases h : t < N
  · rw [hybrid_of_lt h]; exact hq0 t i
  · rw [hybrid_of_le (not_lt.mp h)]; exact hp0 t i

omit [MeasurableSpace I] [DiscreteMeasurableSpace I] in
theorem hybrid_sum_one {p q : ℕ → I → ℝ} (hp1 : ∀ t, ∑ i, p t i = 1)
    (hq1 : ∀ t, ∑ i, q t i = 1) (N : ℕ) : ∀ t, ∑ i, hybrid p q N t i = 1 := by
  intro t
  by_cases h : t < N
  · rw [hybrid_of_lt h]; exact hq1 t
  · rw [hybrid_of_le (not_lt.mp h)]; exact hp1 t

/-- **The finite-horizon density identity**: the hybrid product law is `P` reweighted by the
horizon-`N` likelihood ratio. Proved by comparing box values through
`Measure.eq_infinitePi`; shared support (`hsupp`) is what cancels `ofReal (q)/ofReal (p) *
ofReal (p)` to `ofReal (q)` even at `p`-null points. -/
theorem productLaw_hybrid_eq_withDensity (p q : ℕ → I → ℝ)
    (hp0 : ∀ t i, 0 ≤ p t i) (hq0 : ∀ t i, 0 ≤ q t i)
    (hp1 : ∀ t, ∑ i, p t i = 1) (hq1 : ∀ t, ∑ i, q t i = 1)
    (hsupp : ∀ t i, p t i = 0 ↔ q t i = 0) (N : ℕ) :
    productLaw (hybrid p q N) =
      (productLaw p).withDensity (partialDensity p q N) := by
  classical
  haveI : ∀ t, IsProbabilityMeasure (stepMeasure (p t)) := fun t =>
    isProbabilityMeasure_stepMeasure (hp0 t) (hp1 t)
  haveI : ∀ t, IsProbabilityMeasure (stepMeasure (hybrid p q N t)) := fun t =>
    isProbabilityMeasure_stepMeasure (fun i => hybrid_nonneg hp0 hq0 N t i)
      (hybrid_sum_one hp1 hq1 N t)
  refine (Measure.eq_infinitePi _ fun s T hT => ?_).symm
  set G : ℕ → I → ℝ≥0∞ := fun t x =>
    (if t ∈ s then (T t).indicator (fun _ => (1 : ℝ≥0∞)) x else 1) *
      (if t < N then ENNReal.ofReal (q t x) / ENNReal.ofReal (p t x) else 1) with hG
  have hπ : MeasurableSet (Set.pi (↑s) T) :=
    MeasurableSet.pi s.countable_toSet fun i _ => MeasurableSet.of_discrete
  have hcancel : ∀ t x, ENNReal.ofReal (q t x) / ENNReal.ofReal (p t x) *
      ENNReal.ofReal (p t x) = ENNReal.ofReal (q t x) := by
    intro t x
    refine ENNReal.div_mul_cancel' (fun h0 => ?_) fun hI => absurd hI ENNReal.ofReal_ne_top
    rw [ENNReal.ofReal_eq_zero] at h0 ⊢
    exact le_of_eq ((hsupp t x).mp (le_antisymm h0 (hp0 t x)))
  have hpt : ∀ ω : ℕ → I, (Set.pi (↑s) T).indicator (partialDensity p q N) ω =
      ∏ t ∈ s ∪ Finset.range N, G t (ω t) := by
    intro ω
    by_cases hω : ω ∈ Set.pi (↑s) T
    · rw [Set.indicator_of_mem hω]
      have hfac : ∀ t ∈ s ∪ Finset.range N, G t (ω t) =
          if t < N then ENNReal.ofReal (q t (ω t)) / ENNReal.ofReal (p t (ω t)) else 1 := by
        intro t _
        simp only [hG]
        by_cases hts : t ∈ s
        · rw [if_pos hts,
            Set.indicator_of_mem (Set.mem_pi.mp hω t (Finset.mem_coe.mpr hts)), one_mul]
        · rw [if_neg hts, one_mul]
      rw [Finset.prod_congr rfl hfac,
        ← Finset.prod_subset Finset.subset_union_right
          (fun x _ hx => if_neg (by simpa using hx))]
      exact Finset.prod_congr rfl fun t ht => (if_pos (Finset.mem_range.mp ht)).symm
    · rw [Set.indicator_of_notMem hω]
      rw [Set.mem_pi] at hω
      push Not at hω
      obtain ⟨i, his, hiT⟩ := hω
      refine (Finset.prod_eq_zero (Finset.mem_union_left _ (Finset.mem_coe.mp his)) ?_).symm
      simp only [hG]
      rw [if_pos (Finset.mem_coe.mp his), Set.indicator_of_notMem hiT, zero_mul]
  have hval : ∀ t, ∫⁻ x, G t x ∂stepMeasure (p t) =
      if t ∈ s then stepMeasure (hybrid p q N t) (T t) else 1 := by
    intro t
    rw [lintegral_stepMeasure]
    by_cases hts : t ∈ s
    · rw [if_pos hts]
      by_cases htN : t < N
      · rw [hybrid_of_lt htN, stepMeasure_apply]
        refine Finset.sum_congr rfl fun i _ => ?_
        simp only [hG, if_pos hts, if_pos htN]
        rw [mul_assoc, hcancel t i]
        by_cases hiT : i ∈ T t
        · rw [Set.indicator_of_mem hiT, Set.indicator_of_mem hiT, one_mul]
        · rw [Set.indicator_of_notMem hiT, Set.indicator_of_notMem hiT, zero_mul]
      · rw [hybrid_of_le (not_lt.mp htN), stepMeasure_apply]
        refine Finset.sum_congr rfl fun i _ => ?_
        simp only [hG, if_pos hts, if_neg htN, mul_one]
        by_cases hiT : i ∈ T t
        · rw [Set.indicator_of_mem hiT, Set.indicator_of_mem hiT, one_mul]
        · rw [Set.indicator_of_notMem hiT, Set.indicator_of_notMem hiT, zero_mul]
    · rw [if_neg hts]
      by_cases htN : t < N
      · calc ∑ i, G t i * ENNReal.ofReal (p t i)
            = ∑ i, ENNReal.ofReal (q t i) := by
              refine Finset.sum_congr rfl fun i _ => ?_
              simp only [hG, if_neg hts, if_pos htN, one_mul]
              exact hcancel t i
          _ = 1 := by
              rw [← ENNReal.ofReal_sum_of_nonneg fun i _ => hq0 t i, hq1 t,
                ENNReal.ofReal_one]
      · calc ∑ i, G t i * ENNReal.ofReal (p t i)
            = ∑ i, ENNReal.ofReal (p t i) := by
              refine Finset.sum_congr rfl fun i _ => ?_
              simp only [hG, if_neg hts, if_neg htN, one_mul]
          _ = 1 := by
              rw [← ENNReal.ofReal_sum_of_nonneg fun i _ => hp0 t i, hp1 t,
                ENNReal.ofReal_one]
  calc (productLaw p).withDensity (partialDensity p q N) (Set.pi (↑s) T)
      = ∫⁻ ω, (Set.pi (↑s) T).indicator (partialDensity p q N) ω ∂productLaw p :=
        (withDensity_apply _ hπ).trans (lintegral_indicator hπ _).symm
    _ = ∫⁻ ω, ∏ t ∈ s ∪ Finset.range N, G t (ω t) ∂productLaw p := lintegral_congr hpt
    _ = ∏ t ∈ s ∪ Finset.range N, ∫⁻ x, G t x ∂stepMeasure (p t) :=
        lintegral_infinitePi_prod _ _ _
    _ = ∏ t ∈ s ∪ Finset.range N,
          (if t ∈ s then stepMeasure (hybrid p q N t) (T t) else 1) :=
        Finset.prod_congr rfl fun t _ => hval t
    _ = ∏ i ∈ s, (if i ∈ s then stepMeasure (hybrid p q N i) (T i) else 1) :=
        (Finset.prod_subset Finset.subset_union_left fun x _ hxs => if_neg hxs).symm
    _ = ∏ i ∈ s, stepMeasure (hybrid p q N i) (T i) :=
        Finset.prod_congr rfl fun i hi => if_pos hi

/-- Every `P`-null set is null for every finite-horizon hybrid law. -/
theorem productLaw_hybrid_absolutelyContinuous (p q : ℕ → I → ℝ)
    (hp0 : ∀ t i, 0 ≤ p t i) (hq0 : ∀ t i, 0 ≤ q t i)
    (hp1 : ∀ t, ∑ i, p t i = 1) (hq1 : ∀ t, ∑ i, q t i = 1)
    (hsupp : ∀ t i, p t i = 0 ↔ q t i = 0) (N : ℕ) :
    productLaw (hybrid p q N) ≪ productLaw p := by
  rw [productLaw_hybrid_eq_withDensity p q hp0 hq0 hp1 hq1 hsupp N]
  exact withDensity_absolutelyContinuous _ _

/-! ## The affinity tail -/

/-- The tail sum of Hellinger defects from time `N` on: `∑' k, (1 - ρ (k + N))`. -/
noncomputable def tailSum (p q : ℕ → I → ℝ) (N : ℕ) : ℝ :=
  ∑' k, (1 - affinity (p (k + N)) (q (k + N)))

omit [MeasurableSpace I] [DiscreteMeasurableSpace I] in
/-- Any finite set of Hellinger defects living at times `≥ N` is dominated by the tail sum. -/
theorem sum_one_sub_affinity_le_tailSum (p q : ℕ → I → ℝ)
    (hp0 : ∀ t i, 0 ≤ p t i) (hq0 : ∀ t i, 0 ≤ q t i)
    (hp1 : ∀ t, ∑ i, p t i = 1) (hq1 : ∀ t, ∑ i, q t i = 1)
    (hρ : Summable fun t => 1 - affinity (p t) (q t)) (N : ℕ)
    (G : Finset ℕ) (hG : ∀ t ∈ G, N ≤ t) :
    ∑ t ∈ G, (1 - affinity (p t) (q t)) ≤ tailSum p q N := by
  classical
  have hsum : Summable fun k => 1 - affinity (p (k + N)) (q (k + N)) :=
    (summable_nat_add_iff N).mpr hρ
  have himg : ∑ t ∈ G, (1 - affinity (p t) (q t)) =
      ∑ k ∈ G.image (· - N), (1 - affinity (p (k + N)) (q (k + N))) := by
    rw [Finset.sum_image (fun a ha b hb hab => by
      have := hG a ha; have := hG b hb; omega)]
    exact Finset.sum_congr rfl fun t ht => by rw [Nat.sub_add_cancel (hG t ht)]
  rw [himg]
  exact Summable.sum_le_tsum _
    (fun k _ => sub_nonneg.mpr (affinity_le_one (hp0 _) (hq0 _) (hp1 _) (hq1 _))) hsum

/-! ## Uniform cylinder comparison of `Q` with the hybrid laws -/

/-- **The uniform cylinder estimate**: on every measurable cylinder, `Q` exceeds the
horizon-`N` hybrid law by at most `2 * √(2 * tailSum N)` — the horizons `< N` cancel
(affinity `1`), and the finitely many horizons `≥ N` a cylinder can see are dominated by the
tail sum. -/
theorem productLaw_le_hybrid_add (p q : ℕ → I → ℝ)
    (hp0 : ∀ t i, 0 ≤ p t i) (hq0 : ∀ t i, 0 ≤ q t i)
    (hp1 : ∀ t, ∑ i, p t i = 1) (hq1 : ∀ t, ∑ i, q t i = 1)
    (hρ : Summable fun t => 1 - affinity (p t) (q t)) (N : ℕ)
    {C : Set (ℕ → I)} (hC : C ∈ measurableCylinders fun _ : ℕ => I) :
    productLaw q C ≤ productLaw (hybrid p q N) C +
      ENNReal.ofReal (2 * Real.sqrt (2 * tailSum p q N)) := by
  classical
  obtain ⟨F, S, -, rfl⟩ := (mem_measurableCylinders _).mp hC
  have hcoe : S = (↑S.toFinite.toFinset : Set ((t : F) → I)) := S.toFinite.coe_toFinset.symm
  rw [hcoe, productLaw_cylinder q hq0 hq1 F S.toFinite.toFinset,
    productLaw_cylinder (hybrid p q N) (hybrid_nonneg hp0 hq0 N) (hybrid_sum_one hp1 hq1 N)
      F S.toFinite.toFinset]
  set Sf := S.toFinite.toFinset
  have habs := abs_sum_prod_sub_le (fun t : F => hybrid p q N t) (fun t : F => q t)
    (fun t i => hybrid_nonneg hp0 hq0 N t i) (fun t i => hq0 t i)
    (fun t => hybrid_sum_one hp1 hq1 N t) (fun t => hq1 t) Sf
  have h1r : 1 - ∏ t : F, affinity (hybrid p q N t) (q t) ≤ tailSum p q N := by
    have hstep0 : 1 - ∏ t : F, affinity (hybrid p q N t) (q t) ≤
        ∑ t : F, (1 - affinity (hybrid p q N t) (q t)) :=
      one_sub_prod_le_sum_one_sub Finset.univ _
        (fun a _ => affinity_nonneg _ _)
        (fun a _ => affinity_le_one (fun i => hybrid_nonneg hp0 hq0 N a i) (hq0 a)
          (hybrid_sum_one hp1 hq1 N a) (hq1 a))
    have hattach : ∑ t : F, (1 - affinity (hybrid p q N t) (q t)) =
        ∑ t ∈ F, (1 - affinity (hybrid p q N t) (q t)) := by
      rw [Finset.univ_eq_attach]
      exact Finset.sum_attach F fun t => 1 - affinity (hybrid p q N t) (q t)
    have hfilter : ∑ t ∈ F, (1 - affinity (hybrid p q N t) (q t)) =
        ∑ t ∈ F.filter (fun t => N ≤ t), (1 - affinity (hybrid p q N t) (q t)) := by
      refine (Finset.sum_filter_of_ne fun t _ hne => ?_).symm
      by_contra hlt
      apply hne
      rw [hybrid_of_lt (by omega), affinity_self (hq0 t) (hq1 t), sub_self]
    have hcongr : ∑ t ∈ F.filter (fun t => N ≤ t), (1 - affinity (hybrid p q N t) (q t)) =
        ∑ t ∈ F.filter (fun t => N ≤ t), (1 - affinity (p t) (q t)) := by
      refine Finset.sum_congr rfl fun t ht => ?_
      rw [hybrid_of_le (Finset.mem_filter.mp ht).2]
    calc 1 - ∏ t : F, affinity (hybrid p q N t) (q t)
        ≤ ∑ t : F, (1 - affinity (hybrid p q N t) (q t)) := hstep0
      _ = ∑ t ∈ F.filter (fun t => N ≤ t), (1 - affinity (p t) (q t)) := by
          rw [hattach, hfilter, hcongr]
      _ ≤ tailSum p q N :=
          sum_one_sub_affinity_le_tailSum p q hp0 hq0 hp1 hq1 hρ N _
            fun t ht => (Finset.mem_filter.mp ht).2
  have hb : 2 * Real.sqrt (2 * (1 - ∏ t : F, affinity (hybrid p q N t) (q t))) ≤
      2 * Real.sqrt (2 * tailSum p q N) := by
    have := Real.sqrt_le_sqrt
      (by linarith :
        2 * (1 - ∏ t : F, affinity (hybrid p q N t) (q t)) ≤ 2 * tailSum p q N)
    linarith
  have hle : (∑ y ∈ Sf, ∏ t : F, q t (y t)) ≤
      (∑ y ∈ Sf, ∏ t : F, hybrid p q N t (y t)) + 2 * Real.sqrt (2 * tailSum p q N) := by
    have h1 := (abs_le.mp (habs.trans hb)).1
    linarith
  calc ENNReal.ofReal (∑ y ∈ Sf, ∏ t : F, q t (y t))
      ≤ ENNReal.ofReal ((∑ y ∈ Sf, ∏ t : F, hybrid p q N t (y t)) +
          2 * Real.sqrt (2 * tailSum p q N)) := ENNReal.ofReal_le_ofReal hle
    _ = ENNReal.ofReal (∑ y ∈ Sf, ∏ t : F, hybrid p q N t (y t)) +
          ENNReal.ofReal (2 * Real.sqrt (2 * tailSum p q N)) :=
        ENNReal.ofReal_add
          (Finset.sum_nonneg fun y _ =>
            Finset.prod_nonneg fun t _ => hybrid_nonneg hp0 hq0 N t (y t))
          (by positivity)

/-! ## Cylinder approximation -/

omit [Fintype I] [DiscreteMeasurableSpace I] in
/-- The measurable cylinders of `ℕ → I` form a set algebra. -/
theorem isSetAlgebra_measurableCylinders :
    IsSetAlgebra (measurableCylinders fun _ : ℕ => I) where
  empty_mem := empty_mem_measurableCylinders _
  compl_mem _ h := compl_mem_measurableCylinders h
  union_mem _ _ hs ht := union_mem_measurableCylinders hs ht

/-! ## Rung F1: the absolute-continuity direction of the Kakutani dichotomy -/

/-- **Kakutani dichotomy, product case, absolute-continuity direction** (rung F1, one
direction). Independent finite-alphabet steps with shared per-step support and summable
Hellinger defects `Summable (fun t => 1 - ρ t)` give `Q ≪ P` for the infinite product laws.
The proof: `P`-null sets are null for every finite-horizon hybrid law (the `withDensity`
identity), cylinders separate `Q` from the hybrids by at most `2√(2 · tailSum N)` uniformly,
measurable sets are cylinder-approximable in `(Q + hybrid)`-measure, and the tail vanishes. -/
theorem productLaw_absolutelyContinuous (p q : ℕ → I → ℝ)
    (hp0 : ∀ t i, 0 ≤ p t i) (hq0 : ∀ t i, 0 ≤ q t i)
    (hp1 : ∀ t, ∑ i, p t i = 1) (hq1 : ∀ t, ∑ i, q t i = 1)
    (hsupp : ∀ t i, p t i = 0 ↔ q t i = 0)
    (hρ : Summable fun t => 1 - affinity (p t) (q t)) :
    productLaw q ≪ productLaw p := by
  classical
  haveI : ∀ t, IsProbabilityMeasure (stepMeasure (p t)) := fun t =>
    isProbabilityMeasure_stepMeasure (hp0 t) (hp1 t)
  haveI : ∀ t, IsProbabilityMeasure (stepMeasure (q t)) := fun t =>
    isProbabilityMeasure_stepMeasure (hq0 t) (hq1 t)
  haveI hPq : IsProbabilityMeasure (productLaw q) := by unfold productLaw; infer_instance
  refine Measure.AbsolutelyContinuous.mk fun A hA hPA => ?_
  have key : ∀ N : ℕ, (productLaw q A).toReal ≤
      2 * Real.sqrt (2 * tailSum p q N) + (1 / ((N : ℝ) + 1) + 1 / ((N : ℝ) + 1)) := by
    intro N
    haveI : ∀ t, IsProbabilityMeasure (stepMeasure (hybrid p q N t)) := fun t =>
      isProbabilityMeasure_stepMeasure (fun i => hybrid_nonneg hp0 hq0 N t i)
        (hybrid_sum_one hp1 hq1 N t)
    haveI : IsProbabilityMeasure (productLaw (hybrid p q N)) := by
      unfold productLaw; infer_instance
    set R := productLaw (hybrid p q N) with hR
    have hRA : R A = 0 :=
      productLaw_hybrid_absolutelyContinuous p q hp0 hq0 hp1 hq1 hsupp N hPA
    have hdense : (productLaw q + R).MeasureDense (measurableCylinders fun _ : ℕ => I) :=
      Measure.MeasureDense.of_generateFrom_isSetAlgebra_finite _
        isSetAlgebra_measurableCylinders generateFrom_measurableCylinders.symm
    obtain ⟨C, hC, hCd⟩ :=
      hdense.approx A hA (measure_ne_top _ _) (1 / ((N : ℝ) + 1)) (by positivity)
    have hQd : productLaw q (A ∆ C) ≤ ENNReal.ofReal (1 / ((N : ℝ) + 1)) := by
      refine le_trans ?_ hCd.le
      rw [Measure.add_apply]
      exact self_le_add_right _ _
    have hRd : R (A ∆ C) ≤ ENNReal.ofReal (1 / ((N : ℝ) + 1)) := by
      refine le_trans ?_ hCd.le
      rw [Measure.add_apply]
      exact self_le_add_left _ _
    have hsub1 : A ⊆ C ∪ (A ∆ C) := by
      intro x hx
      by_cases hxC : x ∈ C
      · exact Or.inl hxC
      · exact Or.inr (Set.mem_symmDiff.mpr (Or.inl ⟨hx, hxC⟩))
    have hsub2 : C ⊆ A ∪ (A ∆ C) := by
      intro x hx
      by_cases hxA : x ∈ A
      · exact Or.inl hxA
      · exact Or.inr (Set.mem_symmDiff.mpr (Or.inr ⟨hx, hxA⟩))
    have h3 : R C ≤ ENNReal.ofReal (1 / ((N : ℝ) + 1)) := by
      have hRC : R C ≤ R A + R (A ∆ C) :=
        le_trans (measure_mono hsub2) (measure_union_le _ _)
      rw [hRA, zero_add] at hRC
      exact hRC.trans hRd
    have hclose := productLaw_le_hybrid_add p q hp0 hq0 hp1 hq1 hρ N hC
    have hchain : productLaw q A ≤ ENNReal.ofReal
        (2 * Real.sqrt (2 * tailSum p q N) + (1 / ((N : ℝ) + 1) + 1 / ((N : ℝ) + 1))) := by
      calc productLaw q A
          ≤ productLaw q C + productLaw q (A ∆ C) :=
            le_trans (measure_mono hsub1) (measure_union_le _ _)
        _ ≤ (R C + ENNReal.ofReal (2 * Real.sqrt (2 * tailSum p q N))) +
              ENNReal.ofReal (1 / ((N : ℝ) + 1)) := add_le_add hclose hQd
        _ ≤ (ENNReal.ofReal (1 / ((N : ℝ) + 1)) +
              ENNReal.ofReal (2 * Real.sqrt (2 * tailSum p q N))) +
              ENNReal.ofReal (1 / ((N : ℝ) + 1)) := by gcongr
        _ = ENNReal.ofReal
              (2 * Real.sqrt (2 * tailSum p q N) +
                (1 / ((N : ℝ) + 1) + 1 / ((N : ℝ) + 1))) := by
            rw [ENNReal.ofReal_add (by positivity) (by positivity),
              ENNReal.ofReal_add (by positivity) (by positivity)]
            ring
    exact ENNReal.toReal_le_of_le_ofReal (by positivity) hchain
  have hlim : Tendsto (fun N : ℕ =>
      2 * Real.sqrt (2 * tailSum p q N) + (1 / ((N : ℝ) + 1) + 1 / ((N : ℝ) + 1)))
      atTop (𝓝 0) := by
    have h1 : Tendsto (fun N => tailSum p q N) atTop (𝓝 0) := by
      simp only [tailSum]
      exact tendsto_sum_nat_add fun t => 1 - affinity (p t) (q t)
    have h2 : Tendsto (fun N => 2 * Real.sqrt (2 * tailSum p q N)) atTop (𝓝 0) := by
      have := ((h1.const_mul (2 : ℝ)).sqrt).const_mul (2 : ℝ)
      simpa using this
    have h3 : Tendsto (fun N : ℕ => 1 / ((N : ℝ) + 1) + 1 / ((N : ℝ) + 1)) atTop (𝓝 0) := by
      have h := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
      simpa using h.add h
    simpa using h2.add h3
  have h0 : (productLaw q A).toReal ≤ 0 :=
    ge_of_tendsto hlim (Filter.Eventually.of_forall key)
  have hzero : (productLaw q A).toReal = 0 := le_antisymm h0 ENNReal.toReal_nonneg
  exact (ENNReal.toReal_eq_zero_iff _).mp hzero |>.resolve_right (measure_ne_top _ _)

/-- **Rung F1, both directions**: mutual absolute continuity of the infinite product laws,
by symmetry of the hypotheses in `p` and `q` (the main lemma applied twice with the roles
swapped — no Kolmogorov 0-1 law). -/
theorem product_mutuallyAC (p q : ℕ → I → ℝ)
    (hp0 : ∀ t i, 0 ≤ p t i) (hq0 : ∀ t i, 0 ≤ q t i)
    (hp1 : ∀ t, ∑ i, p t i = 1) (hq1 : ∀ t, ∑ i, q t i = 1)
    (hsupp : ∀ t i, p t i = 0 ↔ q t i = 0)
    (hρ : Summable fun t => 1 - affinity (p t) (q t)) :
    productLaw q ≪ productLaw p ∧ productLaw p ≪ productLaw q :=
  ⟨productLaw_absolutelyContinuous p q hp0 hq0 hp1 hq1 hsupp hρ,
    productLaw_absolutelyContinuous q p hq0 hp0 hq1 hp1 (fun t i => (hsupp t i).symm)
      (hρ.congr fun t => by rw [affinity_comm])⟩

/-! ## The consumer bridge: mixtures with square-summable rates -/

omit [MeasurableSpace I] [DiscreteMeasurableSpace I] in
/-- The pointwise route from Hellinger defect to χ²: `1 - ρ ≤ (1/2) ∑ (g - f)² / f` for a
positive base `f`. Uses `1 - ρ = (1/2) ∑ (√f - √g)²` and `(√f - √g)² ≤ (f - g)² / f`. -/
theorem one_sub_affinity_le_half_chiSq {f g : I → ℝ} (hf_pos : ∀ i, 0 < f i)
    (hg0 : ∀ i, 0 ≤ g i) (hf1 : ∑ i, f i = 1) (hg1 : ∑ i, g i = 1) :
    1 - affinity f g ≤ (1 / 2) * ∑ i, (g i - f i) ^ 2 / f i := by
  have hid : 1 - affinity f g =
      (1 / 2) * ∑ i, (Real.sqrt (f i) - Real.sqrt (g i)) ^ 2 := by
    have hterm : ∀ i ∈ Finset.univ, (Real.sqrt (f i) - Real.sqrt (g i)) ^ 2 =
        f i + g i - 2 * Real.sqrt (f i * g i) := by
      intro i _
      have e1 := Real.sq_sqrt (hf_pos i).le
      have e2 := Real.sq_sqrt (hg0 i)
      have e3 : Real.sqrt (f i * g i) = Real.sqrt (f i) * Real.sqrt (g i) :=
        Real.sqrt_mul (hf_pos i).le _
      rw [e3]
      linear_combination e1 + e2
    rw [Finset.sum_congr rfl hterm, Finset.sum_sub_distrib, Finset.sum_add_distrib, hf1, hg1,
      ← Finset.mul_sum, affinity]
    ring
  rw [hid]
  have hterm2 : ∀ i ∈ Finset.univ, (Real.sqrt (f i) - Real.sqrt (g i)) ^ 2 ≤
      (g i - f i) ^ 2 / f i := by
    intro i _
    rw [le_div_iff₀ (hf_pos i)]
    have e1 := Real.sq_sqrt (hf_pos i).le
    have e2 := Real.sq_sqrt (hg0 i)
    have h1 := Real.sqrt_nonneg (f i)
    have h2 := Real.sqrt_nonneg (g i)
    nlinarith [sq_nonneg (Real.sqrt (f i) - Real.sqrt (g i)),
      sq_nonneg (Real.sqrt (f i) + Real.sqrt (g i)),
      mul_nonneg (mul_nonneg h1 h2) (sq_nonneg (Real.sqrt (f i) - Real.sqrt (g i)))]
  exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum hterm2) (by norm_num)

/-- **The consumer bridge** (layer-2 completion marker): for the mixture family
`q t i = (1 - δ t) * p t i + δ t * s t i` with mixing rates `δ t ∈ [0, 1/2]`, positive base
`p`, normalized direction `s`, uniform χ²-bound `C`, and square-summable rates, the baseline
product law is absolutely continuous with respect to the deviation product law: `P ≪ Q`.
This is E62's (`AnytimeDetectionConditional`) exact hypothesis shape
`Summable (fun t => δ t ^ 2) → P ≪ Q`, product instantiation. Mixtures with `δ ≤ 1/2` and
positive base automatically satisfy mutual per-step absolute continuity. -/
theorem hdich_of_product (p s : ℕ → I → ℝ) (δ : ℕ → ℝ) (C : ℝ)
    (hp_pos : ∀ t i, 0 < p t i) (hp1 : ∀ t, ∑ i, p t i = 1)
    (hs0 : ∀ t i, 0 ≤ s t i) (hs1 : ∀ t, ∑ i, s t i = 1)
    (hδ : ∀ t, δ t ∈ Set.Icc (0 : ℝ) (1 / 2))
    (hC : ∀ t, ∑ i, (s t i - p t i) ^ 2 / p t i ≤ C)
    (hδ2 : Summable fun t => δ t ^ 2) :
    productLaw p ≪ productLaw fun t i => (1 - δ t) * p t i + δ t * s t i := by
  set q : ℕ → I → ℝ := fun t i => (1 - δ t) * p t i + δ t * s t i with hq
  have hq_pos : ∀ t i, 0 < q t i := by
    intro t i
    have h1 : (0 : ℝ) < 1 - δ t := by linarith [(hδ t).2]
    exact add_pos_of_pos_of_nonneg (mul_pos h1 (hp_pos t i))
      (mul_nonneg (hδ t).1 (hs0 t i))
  have hq1 : ∀ t, ∑ i, q t i = 1 := by
    intro t
    simp only [hq]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hp1 t, hs1 t]
    ring
  have hsupp : ∀ t i, p t i = 0 ↔ q t i = 0 := fun t i =>
    iff_of_false (hp_pos t i).ne' (hq_pos t i).ne'
  have hρ : Summable fun t => 1 - affinity (p t) (q t) := by
    refine Summable.of_nonneg_of_le
      (fun t => sub_nonneg.mpr (affinity_le_one (fun i => (hp_pos t i).le)
        (fun i => (hq_pos t i).le) (hp1 t) (hq1 t)))
      (fun t => ?_) (hδ2.mul_left (C / 2))
    have h1 := one_sub_affinity_le_half_chiSq (hp_pos t) (fun i => (hq_pos t i).le)
      (hp1 t) (hq1 t)
    have h2 : ∑ i, (q t i - p t i) ^ 2 / p t i =
        δ t ^ 2 * ∑ i, (s t i - p t i) ^ 2 / p t i := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      have hqi : q t i - p t i = δ t * (s t i - p t i) := by simp only [hq]; ring
      rw [hqi, mul_pow, mul_div_assoc]
    have h3 : δ t ^ 2 * ∑ i, (s t i - p t i) ^ 2 / p t i ≤ δ t ^ 2 * C :=
      mul_le_mul_of_nonneg_left (hC t) (sq_nonneg _)
    calc 1 - affinity (p t) (q t)
        ≤ (1 / 2) * ∑ i, (q t i - p t i) ^ 2 / p t i := h1
      _ = (1 / 2) * (δ t ^ 2 * ∑ i, (s t i - p t i) ^ 2 / p t i) := by rw [h2]
      _ ≤ (1 / 2) * (δ t ^ 2 * C) := by
          exact mul_le_mul_of_nonneg_left h3 (by norm_num)
      _ = C / 2 * δ t ^ 2 := by ring
  exact productLaw_absolutelyContinuous q p (fun t i => (hq_pos t i).le)
    (fun t i => (hp_pos t i).le) hq1 hp1 (fun t i => (hsupp t i).symm)
    (hρ.congr fun t => by rw [affinity_comm])

end Research.KakutaniProductDichotomy
