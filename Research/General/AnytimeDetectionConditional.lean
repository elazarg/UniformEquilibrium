import Mathlib

/-!
# Q38's anytime-detection impossibility, conditional on the Kakutani dichotomy

`questions/old/Question38-LinearDebtQuadraticInformation.md` (Part B) shows that a
deviation rate `p_t := ε/(t+1)` accumulates unbounded incentive debt
(`∑ p_t = ∞`) while its squared rate is summable (`∑ p_t^2 < ∞`); under that
square-summability, the baseline and deviation path laws on infinite play are
mutually absolutely continuous, so every level-`α` anytime detector under the
baseline law misses the deviation law with probability at least `1 - α > 0`.

The mutual-absolute-continuity step is an instance of a **Kakutani dichotomy**
for adapted path laws: infinite product/adapted laws are either mutually
singular or (here, under summable squared deviation) mutually absolutely
continuous. That dichotomy is genuinely the hard analytic content and is
**not proved in this file**. Instead it is packaged as the explicit named
hypothesis `hdich` below, in exactly the one-directional form the detection
argument consumes (`P ≪ Q`, not the full equivalence `P ~ Q`). This file is
the exact consumer a future `kakutani-dichotomy` library must serve: supply a
term of type `Summable (fun t => δ t ^ 2) → P ≪ Q` for the adapted path laws
`P` (baseline) and `Q` (deviation), and `undetectable_unbounded_debt_of_dichotomy`
below discharges the rest of Q38 Part B's impossibility shape.

## Contents

1. `detector_misses_of_mutuallyAC` — the pure detection-theoretic step: a
   level-`α` detector under `P` misses a `P`-absolutely-continuous alternative
   `Q` with positive `Q`-probability. Only the direction `P ≪ Q` is used
   (**not** the reverse `Q ≪ P`, and **not** the full equivalence).
2. Harmonic witnesses: `∑ 1/(t+1) = ∞` but `∑ (1/(t+1))^2 < ∞`, pure
   `Mathlib.Analysis.PSeries` analysis, no measure theory.
3. `undetectable_unbounded_debt_of_dichotomy` — the packaged conditional
   theorem: given `hdich`, the harmonic deviation rate has unbounded debt yet
   is undetectable at every level `α < 1`.
4. `undetectable_unbounded_debt_of_dichotomy_of_summable_sq` — the same
   argument for an arbitrary nonnegative, square-summable, non-summable rate
   `δ`, with the harmonic case recovered as a corollary
   (`undetectable_unbounded_debt_of_dichotomy_via_general`).

## Nonclaims

* The Kakutani dichotomy itself is **not proved**: `hdich` is an explicit
  hypothesis, discharged nowhere in this file.
* No game or kernel model is instantiated: `Ω` is an abstract measurable
  space. The intended instantiation is the repo's
  `UniformEquilibrium.ProofView.Concepts.Stochastic.Core.Probability.InfinitePlayMeasure`
  play space, which is not imported or referenced here.
* Finite-horizon quantitative versions (explicit KL/Pinsker rate bounds) are
  not attempted here; they live in the companion probes `ProductKLBudget` and
  `FinitePinskerBH` (where present).
-/

namespace Research.AnytimeDetectionConditional

open MeasureTheory Filter ENNReal

/-! ## 1. Detection under absolute continuity

Read `D` as the event `{ω | τ ω < ∞}` that an anytime detector/stopping time
`τ` ever fires. The false-alarm condition `MeasureTheory.Measure.real`-style
constraint `P D ≤ α` (`α < 1`) says `τ` fires under the baseline law `P` with
probability at most `α`. `detector_misses_of_mutuallyAC` says: whenever the
deviation law `Q` is dominated by the baseline law (`P ≪ Q`), the detector
also fails to fire under `Q` with positive `Q`-probability, i.e. it misses the
deviation on a genuinely `Q`-positive set of paths. Only `P ≪ Q` is used; the
reverse direction `Q ≪ P` is not needed and not assumed. -/

variable {Ω : Type*} [MeasurableSpace Ω]

/-- A level-`α` anytime detector under the baseline law `P` misses the
deviation law `Q` with positive `Q`-probability whenever `P` is absolutely
continuous with respect to `Q`. Precisely: if `D` is measurable with
`P D ≤ α < 1` (the false-alarm bound), and `P ≪ Q`, then `Q Dᶜ > 0`.

The argument: if `Q Dᶜ = 0`, then `P ≪ Q` forces `P Dᶜ = 0`, i.e.
`P D = 1`; but `P D ≤ α < 1` rules that out. -/
theorem detector_misses_of_mutuallyAC (P Q : Measure Ω) [IsProbabilityMeasure P]
    (hPQ : P ≪ Q) {D : Set Ω} (hD : MeasurableSet D) {α : ℝ≥0∞}
    (hα : P D ≤ α) (hα1 : α < 1) : 0 < Q Dᶜ := by
  by_contra h
  push Not at h
  have hQ0 : Q Dᶜ = 0 := le_antisymm h zero_le
  have hP0 : P Dᶜ = 0 := hPQ hQ0
  rw [prob_compl_eq_one_sub hD] at hP0
  have h1 : (1 : ℝ≥0∞) ≤ P D := tsub_eq_zero_iff_le.mp hP0
  exact absurd (h1.trans hα) (not_le.mpr hα1)

/-! ## 2. Harmonic witnesses

Pure analysis, no measure theory: the harmonic rate `δ t := 1/(t+1)` has
divergent partial sums (linear incentive debt) but summable squares
(quadratic statistical information), matching Q38 Part B's example
`p_t = ε/(t+1)`. -/

/-- The harmonic series diverges: `∑ 1/(t+1)` is not summable. -/
theorem harmonic_not_summable : ¬ Summable (fun t : ℕ => (1 : ℝ) / (t + 1)) := by
  exact_mod_cast mt (summable_nat_add_iff 1).1 Real.not_summable_one_div_natCast

/-- The squared harmonic rate is summable: `∑ (1/(t+1))^2 < ∞`. -/
theorem harmonic_sq_summable : Summable (fun t : ℕ => ((1 : ℝ) / (t + 1)) ^ 2) := by
  have h : Summable (fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ 2) :=
    Real.summable_one_div_nat_pow.mpr one_lt_two
  have h' := (summable_nat_add_iff (f := fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ 2) 1).2 h
  refine h'.congr fun n => ?_
  push_cast
  rw [div_pow, one_pow]

/-- The harmonic partial sums diverge to `+∞`: the cumulative incentive debt
`∑_{t<N} 1/(t+1)` is unbounded. -/
theorem harmonic_partialSums_tendsto_atTop :
    Tendsto (fun N => ∑ t ∈ Finset.range N, (1 : ℝ) / (t + 1)) atTop atTop :=
  Real.tendsto_sum_range_one_div_nat_succ_atTop

/-! ## 3. The packaged conditional theorem

`hdich` is the Kakutani dichotomy hypothesis, taken exactly in the direction
the detection argument consumes: square-summability of the deviation rate
forces `P ≪ Q` for the adapted path laws. A full Kakutani dichotomy would
give the two-sided equivalence `P ~ Q`; only the one-sided consequence is
used here. -/

/-- Conditional on the Kakutani dichotomy `hdich`, the harmonic deviation rate
`δ t = 1/(t+1)` has unbounded cumulative debt yet is undetectable: every
level-`α` anytime detector (`α < 1`) under the baseline law `P` misses the
deviation law `Q` with positive `Q`-probability. -/
theorem undetectable_unbounded_debt_of_dichotomy (P Q : Measure Ω) [IsProbabilityMeasure P]
    (hdich : Summable (fun t : ℕ => ((1 : ℝ) / (t + 1)) ^ 2) → P ≪ Q) :
    Tendsto (fun N => ∑ t ∈ Finset.range N, (1 : ℝ) / (t + 1)) atTop atTop ∧
      ∀ D : Set Ω, MeasurableSet D → ∀ α : ℝ≥0∞, P D ≤ α → α < 1 → 0 < Q Dᶜ :=
  ⟨harmonic_partialSums_tendsto_atTop, fun _D hD _α hα hα1 =>
    detector_misses_of_mutuallyAC P Q (hdich harmonic_sq_summable) hD hα hα1⟩

/-! ## 4. Optional generalization

The same argument for an arbitrary nonnegative, square-summable, non-summable
deviation rate `δ`; the harmonic case is recovered as a corollary. -/

/-- Conditional on the Kakutani dichotomy `hdich` for a general nonnegative
deviation rate `δ` that is square-summable (`hδsq`) but not summable
(`hδdiv`): `δ`'s cumulative debt is unbounded, yet undetectable at every
level `α < 1`. -/
theorem undetectable_unbounded_debt_of_dichotomy_of_summable_sq (P Q : Measure Ω)
    [IsProbabilityMeasure P] (δ : ℕ → ℝ) (hδ0 : ∀ t, 0 ≤ δ t)
    (hδsq : Summable (fun t => δ t ^ 2)) (hδdiv : ¬ Summable δ)
    (hdich : Summable (fun t => δ t ^ 2) → P ≪ Q) :
    Tendsto (fun N => ∑ t ∈ Finset.range N, δ t) atTop atTop ∧
      ∀ D : Set Ω, MeasurableSet D → ∀ α : ℝ≥0∞, P D ≤ α → α < 1 → 0 < Q Dᶜ :=
  ⟨(not_summable_iff_tendsto_nat_atTop_of_nonneg hδ0).mp hδdiv, fun _D hD _α hα hα1 =>
    detector_misses_of_mutuallyAC P Q (hdich hδsq) hD hα hα1⟩

/-- The harmonic instance of `undetectable_unbounded_debt_of_dichotomy_of_summable_sq`
recovers `undetectable_unbounded_debt_of_dichotomy` as a corollary of the
general statement. -/
theorem undetectable_unbounded_debt_of_dichotomy_via_general (P Q : Measure Ω)
    [IsProbabilityMeasure P]
    (hdich : Summable (fun t : ℕ => ((1 : ℝ) / (t + 1)) ^ 2) → P ≪ Q) :
    Tendsto (fun N => ∑ t ∈ Finset.range N, (1 : ℝ) / (t + 1)) atTop atTop ∧
      ∀ D : Set Ω, MeasurableSet D → ∀ α : ℝ≥0∞, P D ≤ α → α < 1 → 0 < Q Dᶜ :=
  undetectable_unbounded_debt_of_dichotomy_of_summable_sq P Q (fun t => (1 : ℝ) / (t + 1))
    (fun t => by positivity) harmonic_sq_summable harmonic_not_summable hdich

end Research.AnytimeDetectionConditional
