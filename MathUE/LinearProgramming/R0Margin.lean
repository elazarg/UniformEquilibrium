/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import MathUE.LinearProgramming.CopositiveQCorollaries

/-!
# The `R₀` margin, and the openness of `R₀`

The homogeneous violation of `MathUE/LinearProgramming/CopositiveQ.lean`
measures how far a simplex point is from solving `LCP(M, 0)`.  Its least value
over the standard simplex is the **`R₀` margin** of `M`.  Because the simplex is
compact and the violation is continuous, that least value is attained, and it is
positive exactly when `M` is an `R₀` matrix.

The margin turns two qualitative statements into quantitative ones.

* The uniform solution bound under `R₀` becomes explicit: every solution of
  `LCP(M, q)` has total mass at most `(card ι + 1) * B / r0Margin M` for any
  coordinatewise bound `B` on `q`.
* The violation is Lipschitz in the matrix, uniformly over the simplex, with
  constant `card ι + 1` against the largest entrywise deviation.  The margin
  inherits that estimate, so `R₀` is an *open* condition on matrices with a
  computable radius.

Openness gives a perturbation statement for the `Q` placement of
`copositive_isR0Matrix_isStandardQ`: a matrix close enough to an `R₀` matrix is
itself `R₀`, hence standard `Q` as soon as it is copositive.  Copositivity is
carried as a hypothesis on the perturbed matrix rather than inherited, because
it is a closed condition and can fail arbitrarily close to a copositive matrix.

## Main definitions

* `r0Margin` — the least homogeneous violation over the standard simplex

## Main results

* `r0Margin_pos_iff_isR0Matrix` — the margin is positive exactly on `R₀`
  matrices
* `sum_le_of_isStandardLCPSolution` — the explicit uniform solution bound
* `abs_matrixAction_sub_le` and `abs_quadratic_sub_le` — the entrywise
  perturbation estimates on the simplex
* `abs_r0Margin_sub_le` — the margin is Lipschitz in the matrix
* `isR0Matrix_of_r0Margin_lt` — `R₀` is open, with a computable radius
* `isStandardQ_of_copositive_of_r0Margin_lt` — perturbation stability of the
  copositive `R₀` route to standard `Q`
-/

noncomputable section

namespace Math.LinearProgramming

variable {ι : Type*} [Fintype ι]

/-! ## The standard simplex is inhabited -/

/-- With at least one coordinate the standard simplex has a vertex. -/
theorem nonempty_coe_stdSimplex [Nonempty ι] : Nonempty (stdSimplex ℝ ι) := by
  classical
  obtain ⟨i₀⟩ := ‹Nonempty ι›
  exact ⟨⟨fun k => if k = i₀ then 1 else 0,
    fun k => by by_cases h : k = i₀ <;> simp [h], by simp⟩⟩

/-! ## The margin -/

/-- The `R₀` margin of `M`: the least homogeneous violation over the standard
simplex. -/
def r0Margin (M : ι → ι → ℝ) : ℝ :=
  ⨅ p : stdSimplex ℝ ι, homogeneousViolation M p.val

theorem bddBelow_range_homogeneousViolation (M : ι → ι → ℝ) :
    BddBelow (Set.range fun p : stdSimplex ℝ ι => homogeneousViolation M p.val) := by
  refine ⟨0, ?_⟩
  rintro x ⟨p, rfl⟩
  exact homogeneousViolation_nonneg M p.val

/-- The margin is a lower bound for the violation at every simplex point. -/
theorem r0Margin_le (M : ι → ι → ℝ) {p : ι → ℝ} (hp : p ∈ stdSimplex ℝ ι) :
    r0Margin M ≤ homogeneousViolation M p :=
  ciInf_le (bddBelow_range_homogeneousViolation M) (⟨p, hp⟩ : stdSimplex ℝ ι)

/-- Any lower bound for the violation on the simplex bounds the margin. -/
theorem le_r0Margin [Nonempty ι] (M : ι → ι → ℝ) {c : ℝ}
    (h : ∀ p ∈ stdSimplex ℝ ι, c ≤ homogeneousViolation M p) : c ≤ r0Margin M := by
  haveI := nonempty_coe_stdSimplex (ι := ι)
  exact le_ciInf fun p => h p.val p.property

theorem r0Margin_nonneg [Nonempty ι] (M : ι → ι → ℝ) : 0 ≤ r0Margin M :=
  le_r0Margin M fun p _ => homogeneousViolation_nonneg M p

/-- **The margin is attained.**  The simplex is compact and the violation is
continuous, so some simplex point realizes the least violation. -/
theorem exists_mem_stdSimplex_homogeneousViolation_eq_r0Margin [Nonempty ι]
    (M : ι → ι → ℝ) :
    ∃ p ∈ stdSimplex ℝ ι, homogeneousViolation M p = r0Margin M := by
  classical
  haveI := nonempty_coe_stdSimplex (ι := ι)
  obtain ⟨p₀⟩ := ‹Nonempty (stdSimplex ℝ ι)›
  obtain ⟨p, hp, hmin⟩ :=
    (isCompact_stdSimplex ℝ (ι := ι)).exists_isMinOn ⟨p₀.val, p₀.property⟩
      (continuous_homogeneousViolation M).continuousOn
  refine ⟨p, hp, le_antisymm ?_ (r0Margin_le M hp)⟩
  exact le_r0Margin M fun y hy => isMinOn_iff.mp hmin y hy

/-! ## The margin detects `R₀` -/

/-- A homogeneous simplex solution has zero violation: complementarity kills
the quadratic form and the residual sign condition kills the negative parts. -/
theorem homogeneousViolation_eq_zero_of_singletonLCPFeasible {M : ι → ι → ℝ}
    (h : SingletonLCPFeasible M) :
    ∃ p ∈ stdSimplex ℝ ι, homogeneousViolation M p = 0 := by
  obtain ⟨lam, hres, hcomp⟩ := h
  refine ⟨lam.val, lam.property, ?_⟩
  have hrow : ∀ i, (∑ j, lam.val j * M i j) = singletonLCPResidual M lam i :=
    fun i => rfl
  have hquad : (∑ i, lam.val i * ∑ j, lam.val j * M i j) = 0 := by
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [hrow i]
    exact hcomp i
  have hneg : ∀ i, max 0 (-(∑ j, lam.val j * M i j)) = 0 := by
    intro i
    rw [hrow i]
    exact max_eq_left (by linarith [hres i])
  rw [homogeneousViolation, hquad]
  simp [hneg]

/-- **The margin is positive exactly on `R₀` matrices.** -/
theorem r0Margin_pos_iff_isR0Matrix [Nonempty ι] (M : ι → ι → ℝ) :
    0 < r0Margin M ↔ IsR0Matrix M := by
  rw [isR0Matrix_iff_not_singletonLCPFeasible]
  constructor
  · intro hpos hfeasible
    obtain ⟨p, hp, hzero⟩ := homogeneousViolation_eq_zero_of_singletonLCPFeasible hfeasible
    have := r0Margin_le M hp
    rw [hzero] at this
    linarith
  · intro hno
    rcases lt_or_eq_of_le (r0Margin_nonneg M) with hpos | hzero
    · exact hpos
    · obtain ⟨p, hp, hval⟩ := exists_mem_stdSimplex_homogeneousViolation_eq_r0Margin M
      exact absurd (singletonLCPFeasible_of_violation_nonpos M hp (by rw [hval, ← hzero]))
        hno

/-! ## The explicit uniform solution bound -/

/-- **The explicit `R₀` solution bound.**  Under a positive margin, every
solution of `LCP(M, q)` has total mass at most `(card ι + 1) * B / r0Margin M`,
for any coordinatewise bound `B` on `q`. -/
theorem sum_le_of_isStandardLCPSolution [Nonempty ι] (M : ι → ι → ℝ)
    (hmargin : 0 < r0Margin M) {B : ℝ} (hB : 0 ≤ B) (q z : ι → ℝ)
    (hq : ∀ i, |q i| ≤ B) (hsol : IsStandardLCPSolution M q z) :
    (∑ i, z i) ≤ ((Fintype.card ι : ℝ) + 1) * B / r0Margin M := by
  classical
  have hznn : (0 : ℝ) ≤ ∑ i, z i :=
    Finset.sum_nonneg fun i _ => hsol.weight_nonneg i
  have hcard : (0 : ℝ) ≤ (Fintype.card ι : ℝ) + 1 := by positivity
  rcases eq_or_lt_of_le hznn with heq | hr
  · rw [← heq]
    positivity
  · have hviol :=
      homogeneousViolation_normalized_le_of_isStandardLCPSolution_of_bound M q z hsol
        hr hB hq rfl
    have hmem : (fun i => z i / ∑ i, z i) ∈ stdSimplex ℝ ι :=
      ⟨fun i => div_nonneg (hsol.weight_nonneg i) hr.le,
        by rw [← Finset.sum_div]; exact div_self hr.ne'⟩
    have hlow := (r0Margin_le M hmem).trans hviol
    rw [le_div_iff₀ hr] at hlow
    rw [le_div_iff₀ hmargin]
    nlinarith [hlow]

/-! ## Lipschitz dependence on the matrix

The two estimates below are the entrywise-perturbation plumbing shared by every
margin taken over the standard simplex: on the simplex the weights are
nonnegative and sum to one, so a weighted average of entrywise deviations never
exceeds the largest of them. -/

/-- **The matrix action is Lipschitz in the matrix.**  At a simplex point the
rows of `M` and of `N` differ by at most the largest entrywise deviation. -/
theorem abs_matrixAction_sub_le (M N : ι → ι → ℝ) {δ : ℝ}
    (hδ : ∀ i j, |M i j - N i j| ≤ δ) {p : ι → ℝ} (hp : p ∈ stdSimplex ℝ ι) (i : ι) :
    |(∑ j, p j * M i j) - ∑ j, p j * N i j| ≤ δ := by
  have hsplit : (∑ j, p j * M i j) - (∑ j, p j * N i j) =
      ∑ j, p j * (M i j - N i j) := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [hsplit]
  calc |∑ j, p j * (M i j - N i j)| ≤ ∑ j, |p j * (M i j - N i j)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j, p j * δ := by
        refine Finset.sum_le_sum fun j _ => ?_
        rw [abs_mul, abs_of_nonneg (hp.1 j)]
        exact mul_le_mul_of_nonneg_left (hδ i j) (hp.1 j)
    _ = δ := by rw [← Finset.sum_mul, hp.2, one_mul]

/-- **The quadratic form is Lipschitz in the matrix**, with constant one: at a
simplex point it moves by at most the largest entrywise deviation. -/
theorem abs_quadratic_sub_le (M N : ι → ι → ℝ) {δ : ℝ}
    (hδ : ∀ i j, |M i j - N i j| ≤ δ) {p : ι → ℝ} (hp : p ∈ stdSimplex ℝ ι) :
    |(∑ i, p i * ∑ j, p j * M i j) - ∑ i, p i * ∑ j, p j * N i j| ≤ δ := by
  have hsplit : (∑ i, p i * ∑ j, p j * M i j) - (∑ i, p i * ∑ j, p j * N i j) =
      ∑ i, p i * ((∑ j, p j * M i j) - ∑ j, p j * N i j) := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [hsplit]
  calc |∑ i, p i * ((∑ j, p j * M i j) - ∑ j, p j * N i j)| ≤
        ∑ i, |p i * ((∑ j, p j * M i j) - ∑ j, p j * N i j)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, p i * δ := by
        refine Finset.sum_le_sum fun i _ => ?_
        rw [abs_mul, abs_of_nonneg (hp.1 i)]
        exact mul_le_mul_of_nonneg_left (abs_matrixAction_sub_le M N hδ hp i) (hp.1 i)
    _ = δ := by rw [← Finset.sum_mul, hp.2, one_mul]

/-- **The violation is Lipschitz in the matrix.**  On the standard simplex the
homogeneous violation of `M` and of `N` differ by at most `card ι + 1` times the
largest entrywise deviation. -/
theorem abs_homogeneousViolation_sub_le (M N : ι → ι → ℝ) {δ : ℝ}
    (hδ : ∀ i j, |M i j - N i j| ≤ δ) {p : ι → ℝ} (hp : p ∈ stdSimplex ℝ ι) :
    |homogeneousViolation M p - homogeneousViolation N p| ≤
      ((Fintype.card ι : ℝ) + 1) * δ := by
  classical
  have hrow : ∀ i, |(∑ j, p j * M i j) - ∑ j, p j * N i j| ≤ δ :=
    abs_matrixAction_sub_le M N hδ hp
  have hquad : |(∑ i, p i * ∑ j, p j * M i j) - ∑ i, p i * ∑ j, p j * N i j| ≤ δ :=
    abs_quadratic_sub_le M N hδ hp
  have hmax : |max 0 (∑ i, p i * ∑ j, p j * M i j) -
      max 0 (∑ i, p i * ∑ j, p j * N i j)| ≤ δ := by
    have hcomm : ∀ x : ℝ, max 0 x = max x 0 := fun x => max_comm 0 x
    rw [hcomm, hcomm]
    exact (abs_max_sub_max_le_abs _ _ _).trans hquad
  have hparts : |(∑ i, max 0 (-(∑ j, p j * M i j))) -
      ∑ i, max 0 (-(∑ j, p j * N i j))| ≤ (Fintype.card ι : ℝ) * δ := by
    have hsplit : (∑ i, max 0 (-(∑ j, p j * M i j))) -
        (∑ i, max 0 (-(∑ j, p j * N i j))) =
        ∑ i, (max 0 (-(∑ j, p j * M i j)) - max 0 (-(∑ j, p j * N i j))) := by
      rw [← Finset.sum_sub_distrib]
    rw [hsplit]
    calc |∑ i, (max 0 (-(∑ j, p j * M i j)) - max 0 (-(∑ j, p j * N i j)))| ≤
          ∑ i, |max 0 (-(∑ j, p j * M i j)) - max 0 (-(∑ j, p j * N i j))| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i : ι, δ := by
          refine Finset.sum_le_sum fun i _ => ?_
          have hcomm : ∀ x : ℝ, max 0 x = max x 0 := fun x => max_comm 0 x
          rw [hcomm, hcomm]
          refine (abs_max_sub_max_le_abs _ _ _).trans ?_
          have : -(∑ j, p j * M i j) - -(∑ j, p j * N i j) =
              -((∑ j, p j * M i j) - ∑ j, p j * N i j) := by ring
          rw [this, abs_neg]
          exact hrow i
      _ = (Fintype.card ι : ℝ) * δ := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hsum : homogeneousViolation M p - homogeneousViolation N p =
      (max 0 (∑ i, p i * ∑ j, p j * M i j) -
        max 0 (∑ i, p i * ∑ j, p j * N i j)) +
      ((∑ i, max 0 (-(∑ j, p j * M i j))) -
        ∑ i, max 0 (-(∑ j, p j * N i j))) := by
    rw [homogeneousViolation, homogeneousViolation]
    ring
  rw [hsum]
  refine (abs_add_le _ _).trans ?_
  nlinarith [hmax, hparts]

/-- **The margin is Lipschitz in the matrix**, with the same constant. -/
theorem abs_r0Margin_sub_le [Nonempty ι] (M N : ι → ι → ℝ) {δ : ℝ}
    (hδ : ∀ i j, |M i j - N i j| ≤ δ) :
    |r0Margin M - r0Margin N| ≤ ((Fintype.card ι : ℝ) + 1) * δ := by
  have hforward : r0Margin M - ((Fintype.card ι : ℝ) + 1) * δ ≤ r0Margin N := by
    refine le_r0Margin N fun p hp => ?_
    have hbound := abs_homogeneousViolation_sub_le M N hδ hp
    have hle := (abs_le.mp hbound).2
    linarith [r0Margin_le M hp]
  have hreverse : r0Margin N - ((Fintype.card ι : ℝ) + 1) * δ ≤ r0Margin M := by
    refine le_r0Margin M fun p hp => ?_
    have hbound := abs_homogeneousViolation_sub_le M N hδ hp
    have hle := (abs_le.mp hbound).1
    linarith [r0Margin_le N hp]
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-! ## `R₀` is open -/

/-- **`R₀` is an open condition, with a computable radius.**  Any matrix whose
entries deviate from those of an `R₀` matrix by less than
`r0Margin M / (card ι + 1)` is again `R₀`. -/
theorem isR0Matrix_of_r0Margin_lt [Nonempty ι] {M N : ι → ι → ℝ} {δ : ℝ}
    (hδ : ∀ i j, |M i j - N i j| ≤ δ)
    (hlt : ((Fintype.card ι : ℝ) + 1) * δ < r0Margin M) : IsR0Matrix N := by
  refine (r0Margin_pos_iff_isR0Matrix N).mp ?_
  have hbound := abs_r0Margin_sub_le M N hδ
  have hle := (abs_le.mp hbound).2
  linarith

/-- **Perturbation stability of the copositive `R₀` route to standard `Q`.**
A copositive matrix whose entries are within `r0Margin M / (card ι + 1)` of an
`R₀` matrix `M` is a standard `Q`-matrix.

Copositivity appears as a hypothesis on the perturbed matrix rather than as an
inherited property: it is a closed condition, and can fail at matrices
arbitrarily close to a copositive one. -/
theorem isStandardQ_of_copositive_of_r0Margin_lt [Nonempty ι] {M N : ι → ι → ℝ}
    {δ : ℝ} (hδ : ∀ i j, |M i j - N i j| ≤ δ)
    (hlt : ((Fintype.card ι : ℝ) + 1) * δ < r0Margin M) (hcop : IsCopositive N) :
    IsStandardQ N :=
  copositive_isR0Matrix_isStandardQ N hcop (isR0Matrix_of_r0Margin_lt hδ hlt)

end Math.LinearProgramming
