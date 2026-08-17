/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import MathUE.LinearProgramming.R0Margin

/-!
# The copositivity margin, and the openness of strict copositivity

Copositivity and strict copositivity are homogeneous conditions of degree two on
the nonnegative orthant, so both are decided on the standard simplex: rescaling
a nonzero `z ≥ 0` to `z / ∑ z` divides the quadratic form by `(∑ z)²`.  The
least value of the quadratic form over the simplex is therefore the natural
margin, and it is attained because the simplex is compact.

* Nonnegative margin is exactly copositivity, and positive margin is exactly
  strict copositivity.  The two readings sit on either side of a single
  inequality, which is why copositivity is a *closed* condition and strict
  copositivity an *open* one.
* The quadratic form moves by at most the largest entrywise deviation
  (`abs_quadratic_sub_le`), so the margin is Lipschitz in the matrix with
  constant one.  Strict copositivity therefore survives every entrywise
  perturbation smaller than the margin.

That gives a two-sided perturbation statement for the `Q` placement: in the ball
of radius `copositiveMargin M` around a strictly copositive `M`, every matrix is
again strictly copositive, hence `R₀` by
`IsStrictlyCopositive.isR0Matrix`, hence standard `Q` by
`isStandardQ_of_strictlyCopositive`.  No separate `R₀` radius is needed, because
strict copositivity already carries `R₀`.

## Main definitions

* `copositiveMargin` — the least quadratic form value over the standard simplex

## Main results

* `copositiveMargin_nonneg_iff_isCopositive` and
  `copositiveMargin_pos_iff_isStrictlyCopositive` — the two readings
* `abs_copositiveMargin_sub_le` — the margin is Lipschitz in the matrix, with
  constant one
* `isStrictlyCopositive_of_copositiveMargin_lt` — strict copositivity is open,
  with a computable radius
* `isStandardQ_of_copositiveMargin_lt` — the resulting perturbation stability of
  the standard-`Q` placement
-/

noncomputable section

namespace Math.LinearProgramming

variable {ι : Type*} [Fintype ι]

/-! ## The quadratic form on the simplex -/

theorem continuous_simplexQuadratic (M : ι → ι → ℝ) :
    Continuous fun p : ι → ℝ => ∑ i, p i * ∑ j, p j * M i j := by
  have hrow : ∀ i : ι, Continuous fun p : ι → ℝ => ∑ j, p j * M i j := by
    intro i
    refine continuous_finsetSum _ fun j _ => ?_
    have hproj : Continuous fun p : ι → ℝ => p j := continuous_apply j
    exact hproj.mul_const (M i j)
  exact continuous_finsetSum _ fun i _ => (continuous_apply i).mul (hrow i)

/-- Rescaling divides the quadratic form by the square of the scale. -/
theorem quadratic_div (M : ι → ι → ℝ) (z : ι → ℝ) {s : ℝ} (hs : s ≠ 0) :
    (∑ i, (z i / s) * ∑ j, (z j / s) * M i j) =
      (∑ i, z i * ∑ j, z j * M i j) / (s * s) := by
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hrow : (∑ j, (z j / s) * M i j) = (∑ j, z j * M i j) / s := by
    rw [Finset.sum_div]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [hrow]
  field_simp

/-! ## The margin -/

/-- The copositivity margin of `M`: the least value of the quadratic form over
the standard simplex. -/
def copositiveMargin (M : ι → ι → ℝ) : ℝ :=
  ⨅ p : stdSimplex ℝ ι, ∑ i, p.val i * ∑ j, p.val j * M i j

/-- **The margin is attained.**  The simplex is compact and the quadratic form
is continuous. -/
theorem exists_mem_stdSimplex_isMinOn_quadratic [Nonempty ι] (M : ι → ι → ℝ) :
    ∃ p ∈ stdSimplex ℝ ι, ∀ y ∈ stdSimplex ℝ ι,
      (∑ i, p i * ∑ j, p j * M i j) ≤ ∑ i, y i * ∑ j, y j * M i j := by
  haveI := nonempty_coe_stdSimplex (ι := ι)
  obtain ⟨p₀⟩ := ‹Nonempty (stdSimplex ℝ ι)›
  obtain ⟨p, hp, hmin⟩ :=
    (isCompact_stdSimplex ℝ (ι := ι)).exists_isMinOn ⟨p₀.val, p₀.property⟩
      (continuous_simplexQuadratic M).continuousOn
  exact ⟨p, hp, fun y hy => isMinOn_iff.mp hmin y hy⟩

theorem bddBelow_range_quadratic [Nonempty ι] (M : ι → ι → ℝ) :
    BddBelow (Set.range fun p : stdSimplex ℝ ι => ∑ i, p.val i * ∑ j, p.val j * M i j) := by
  obtain ⟨p, hp, hmin⟩ := exists_mem_stdSimplex_isMinOn_quadratic M
  refine ⟨∑ i, p i * ∑ j, p j * M i j, ?_⟩
  rintro x ⟨y, rfl⟩
  exact hmin y.val y.property

/-- The margin is a lower bound for the quadratic form at every simplex
point. -/
theorem copositiveMargin_le [Nonempty ι] (M : ι → ι → ℝ) {p : ι → ℝ}
    (hp : p ∈ stdSimplex ℝ ι) :
    copositiveMargin M ≤ ∑ i, p i * ∑ j, p j * M i j :=
  ciInf_le (bddBelow_range_quadratic M) (⟨p, hp⟩ : stdSimplex ℝ ι)

/-- Any lower bound for the quadratic form on the simplex bounds the margin. -/
theorem le_copositiveMargin [Nonempty ι] (M : ι → ι → ℝ) {c : ℝ}
    (h : ∀ p ∈ stdSimplex ℝ ι, c ≤ ∑ i, p i * ∑ j, p j * M i j) :
    c ≤ copositiveMargin M := by
  haveI := nonempty_coe_stdSimplex (ι := ι)
  exact le_ciInf fun p => h p.val p.property

theorem exists_mem_stdSimplex_quadratic_eq_copositiveMargin [Nonempty ι]
    (M : ι → ι → ℝ) :
    ∃ p ∈ stdSimplex ℝ ι, (∑ i, p i * ∑ j, p j * M i j) = copositiveMargin M := by
  obtain ⟨p, hp, hmin⟩ := exists_mem_stdSimplex_isMinOn_quadratic M
  exact ⟨p, hp, le_antisymm (le_copositiveMargin M fun y hy => hmin y hy)
    (copositiveMargin_le M hp)⟩

/-! ## The two readings of the margin -/

/-- A nonzero nonnegative vector rescales to a simplex point. -/
theorem mem_stdSimplex_div_sum {z : ι → ℝ} (hz : ∀ i, 0 ≤ z i)
    (hs : 0 < ∑ i, z i) : (fun i => z i / ∑ i, z i) ∈ stdSimplex ℝ ι :=
  ⟨fun i => div_nonneg (hz i) hs.le, by rw [← Finset.sum_div]; exact div_self hs.ne'⟩

/-- **Nonnegative margin is copositivity.** -/
theorem copositiveMargin_nonneg_iff_isCopositive [Nonempty ι] (M : ι → ι → ℝ) :
    0 ≤ copositiveMargin M ↔ IsCopositive M := by
  constructor
  · intro hmargin z hz
    rcases eq_or_lt_of_le (Finset.sum_nonneg fun i _ => hz i : (0 : ℝ) ≤ ∑ i, z i) with
      heq | hs
    · have hzero : ∀ i, z i = 0 := fun i =>
        (Finset.sum_eq_zero_iff_of_nonneg fun j _ => hz j).mp heq.symm i
          (Finset.mem_univ i)
      simp [hzero]
    · have hmem := mem_stdSimplex_div_sum hz hs
      have hlow := copositiveMargin_le M hmem
      rw [quadratic_div M z hs.ne'] at hlow
      have hss : (0 : ℝ) < (∑ i, z i) * ∑ i, z i := mul_pos hs hs
      rw [le_div_iff₀ hss] at hlow
      nlinarith [hlow]
  · intro hcop
    exact le_copositiveMargin M fun p hp => hcop p hp.1

/-- **Positive margin is strict copositivity.** -/
theorem copositiveMargin_pos_iff_isStrictlyCopositive [Nonempty ι] (M : ι → ι → ℝ) :
    0 < copositiveMargin M ↔ IsStrictlyCopositive M := by
  constructor
  · intro hmargin z hz hne
    obtain ⟨i₀, hi₀⟩ := hne
    have hs : 0 < ∑ i, z i :=
      Finset.sum_pos' (fun i _ => hz i)
        ⟨i₀, Finset.mem_univ i₀, lt_of_le_of_ne (hz i₀) (Ne.symm hi₀)⟩
    have hmem := mem_stdSimplex_div_sum hz hs
    have hlow := copositiveMargin_le M hmem
    rw [quadratic_div M z hs.ne'] at hlow
    have hss : (0 : ℝ) < (∑ i, z i) * ∑ i, z i := mul_pos hs hs
    rw [le_div_iff₀ hss] at hlow
    nlinarith [hlow]
  · intro hstrict
    obtain ⟨p, hp, hval⟩ := exists_mem_stdSimplex_quadratic_eq_copositiveMargin M
    obtain ⟨i₀, hi₀⟩ : ∃ i, p i ≠ 0 := by
      by_contra hnone
      push Not at hnone
      have := hp.2
      simp [hnone] at this
    rw [← hval]
    exact hstrict p hp.1 ⟨i₀, hi₀⟩

/-! ## Openness of strict copositivity -/

/-- **The margin is Lipschitz in the matrix**, with constant one. -/
theorem abs_copositiveMargin_sub_le [Nonempty ι] (M N : ι → ι → ℝ) {δ : ℝ}
    (hδ : ∀ i j, |M i j - N i j| ≤ δ) :
    |copositiveMargin M - copositiveMargin N| ≤ δ := by
  have hforward : copositiveMargin M - δ ≤ copositiveMargin N := by
    refine le_copositiveMargin N fun p hp => ?_
    have hle := (abs_le.mp (abs_quadratic_sub_le M N hδ hp)).2
    linarith [copositiveMargin_le M hp]
  have hreverse : copositiveMargin N - δ ≤ copositiveMargin M := by
    refine le_copositiveMargin M fun p hp => ?_
    have hle := (abs_le.mp (abs_quadratic_sub_le M N hδ hp)).1
    linarith [copositiveMargin_le N hp]
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- **Strict copositivity is an open condition, with a computable radius.**  Any
matrix whose entries deviate from those of a strictly copositive matrix `M` by
less than `copositiveMargin M` is again strictly copositive. -/
theorem isStrictlyCopositive_of_copositiveMargin_lt [Nonempty ι] {M N : ι → ι → ℝ}
    {δ : ℝ} (hδ : ∀ i j, |M i j - N i j| ≤ δ) (hlt : δ < copositiveMargin M) :
    IsStrictlyCopositive N := by
  refine (copositiveMargin_pos_iff_isStrictlyCopositive N).mp ?_
  have hle := (abs_le.mp (abs_copositiveMargin_sub_le M N hδ)).2
  linarith

/-- `R₀` is inherited in the same ball, through strict copositivity. -/
theorem isR0Matrix_of_copositiveMargin_lt [Nonempty ι] {M N : ι → ι → ℝ} {δ : ℝ}
    (hδ : ∀ i j, |M i j - N i j| ≤ δ) (hlt : δ < copositiveMargin M) :
    IsR0Matrix N :=
  (isStrictlyCopositive_of_copositiveMargin_lt hδ hlt).isR0Matrix

/-- **Two-sided perturbation stability of the standard-`Q` placement.**  Every
matrix within entrywise distance `copositiveMargin M` of a strictly copositive
`M` is itself strictly copositive and `R₀`, hence a standard `Q`-matrix.

Unlike the copositive route, nothing here is carried as a hypothesis on the
perturbed matrix: strict copositivity is inherited, and it already implies
`R₀`, so no separate `R₀` radius enters. -/
theorem isStandardQ_of_copositiveMargin_lt [Nonempty ι] {M N : ι → ι → ℝ} {δ : ℝ}
    (hδ : ∀ i j, |M i j - N i j| ≤ δ) (hlt : δ < copositiveMargin M) :
    IsStandardQ N :=
  isStandardQ_of_strictlyCopositive (isStrictlyCopositive_of_copositiveMargin_lt hδ hlt)

end Math.LinearProgramming
