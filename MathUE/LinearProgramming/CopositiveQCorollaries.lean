/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import MathUE.LinearProgramming.CopositiveQ

/-!
# Corollaries of the copositive `Q` theorem

This file collects the elementary consequences of `CopositiveQ.lean` that do
not need any game semantics: the strictly positive right-hand side, strict
copositivity, uniform solution bounds under `R₀`, and the principal
subtournament dichotomy for integral tournaments.

Everything here uses the repository's row convention
`(Mz) i = ∑ j, z j * M i j`, as in `CopositiveQ.lean`.

## Main definitions

* `IsStrictlyCopositive` — `⟨z, Mz⟩ > 0` for every nonzero `z ≥ 0`
* `IsIntegralTournament` — a fractional tournament with `0/1` pair weights

## Main results

* `weight_mul_eq_zero_of_quadratic_nonneg` — for a nonnegative `q`, a
  nonnegative complementary weight vector is supported on the zero set of `q`;
  no residual sign condition is used, and copositivity is needed only at the
  weight vector itself
* `weight_eq_zero_of_copositive_of_pos` — the special case of an everywhere
  positive `q`, where that zero set is empty
* `isStandardLCPSolution_iff_eq_zero_of_copositive_of_pos` — the same
  statement as a uniqueness theorem for `LCP(M, q)`
* `isStandardQ_of_strictlyCopositive` — Karamardian's corollary
* `homogeneousViolation_normalized_le_of_isStandardLCPSolution_of_bound` — the
  `O(1/r)` violation bound at an exact solution, against any coordinatewise
  bound on `q` and with no copositivity input;
  `homogeneousViolation_normalized_le_of_isStandardLCPSolution` is its `‖q‖₁`
  reading
* `exists_bound_sum_of_isR0Matrix` — under `R₀`, solutions of `LCP(M, q)` are
  bounded uniformly over any coordinatewise-bounded set of right-hand sides
* `IsStrictlyCopositive.eq_zero_of_complementary` — strict copositivity kills
  every nonzero complementary nonnegative vector, residual sign or not
* `isStandardQ_or_singletonLCPFeasible_of_isIntegralTournament` — the
  dichotomy for integral tournaments: standard `Q`, or an explicit homogeneous
  simplex witness at an all-loser vertex
-/

noncomputable section

namespace Math.LinearProgramming

variable {ι : Type*} [Fintype ι]

/-! ## Strictly positive right-hand sides

Copositivity alone forces the zero weight vector once the right-hand side is
strictly positive.  Only nonnegativity and complementarity of the weights are
used; the residual sign condition is not needed. -/

/-- **Nonnegative right-hand sides confine complementary weights to the zero
set of `q`.**  Complementarity makes the pairing `⟨z, q + Mz⟩` vanish, so
`⟨z, q⟩ = -⟨z, Mz⟩ ≤ 0` as soon as the quadratic form is nonnegative at `z`,
while every term of `⟨z, q⟩` is nonnegative; the terms therefore vanish one by
one.  Only the value of the quadratic form at this single `z` enters, so
copositivity of `M` is more than is needed. -/
theorem weight_mul_eq_zero_of_quadratic_nonneg (M : ι → ι → ℝ)
    (q z : ι → ℝ) (hquad : 0 ≤ ∑ i, z i * ∑ j, z j * M i j)
    (hq : ∀ i, 0 ≤ q i) (hz : ∀ i, 0 ≤ z i)
    (hcomp : ∀ i, z i * lcpResidual M q z i = 0) :
    ∀ i, z i * q i = 0 := by
  classical
  have hsum : (∑ i, z i * lcpResidual M q z i) = 0 :=
    Finset.sum_eq_zero fun i _ => hcomp i
  have hsplit : (∑ i, z i * lcpResidual M q z i) =
      (∑ i, z i * q i) + ∑ i, z i * ∑ j, z j * M i j := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by rw [lcpResidual_def]; ring
  have hzq_nonneg : 0 ≤ ∑ i, z i * q i :=
    Finset.sum_nonneg fun i _ => mul_nonneg (hz i) (hq i)
  have hzq : (∑ i, z i * q i) = 0 := by rw [hsplit] at hsum; linarith
  exact fun i =>
    (Finset.sum_eq_zero_iff_of_nonneg
      (fun j _ => mul_nonneg (hz j) (hq j))).mp hzq i (Finset.mem_univ i)

/-- **A copositive complementary weight vanishes wherever a nonnegative
right-hand side is strictly positive.** -/
theorem weight_eq_zero_of_copositive_of_nonneg (M : ι → ι → ℝ)
    (hcop : IsCopositive M) (q z : ι → ℝ) (hq : ∀ i, 0 ≤ q i) (hz : ∀ i, 0 ≤ z i)
    (hcomp : ∀ i, z i * lcpResidual M q z i = 0) {i : ι} (hqi : 0 < q i) :
    z i = 0 := by
  rcases mul_eq_zero.mp
      (weight_mul_eq_zero_of_quadratic_nonneg M q z (hcop z hz) hq hz hcomp i) with
    h | h
  · exact h
  · exact absurd h hqi.ne'

/-- **Positive right-hand sides kill copositive weights.** If `M` is
copositive, `q` is strictly positive, and `z ≥ 0` is complementary to the
residual `q + Mz`, then `z = 0`. -/
theorem weight_eq_zero_of_copositive_of_pos (M : ι → ι → ℝ) (hcop : IsCopositive M)
    (q z : ι → ℝ) (hq : ∀ i, 0 < q i) (hz : ∀ i, 0 ≤ z i)
    (hcomp : ∀ i, z i * lcpResidual M q z i = 0) :
    ∀ i, z i = 0 :=
  fun i =>
    weight_eq_zero_of_copositive_of_nonneg M hcop q z (fun j => (hq j).le) hz hcomp
      (hq i)

/-- The zero vector solves `LCP(M, q)` whenever `q` is nonnegative. -/
theorem isStandardLCPSolution_zero (M : ι → ι → ℝ) {q : ι → ℝ} (hq : ∀ i, 0 ≤ q i) :
    IsStandardLCPSolution M q 0 := by
  refine ⟨fun i => le_rfl, fun i => ?_, fun i => ?_⟩ <;> simp [lcpResidual, hq i]

/-- **Unique solvability for positive right-hand sides.** For a copositive `M`
and a strictly positive `q` the zero vector is the one and only solution of
`LCP(M, q)`. -/
theorem isStandardLCPSolution_iff_eq_zero_of_copositive_of_pos (M : ι → ι → ℝ)
    (hcop : IsCopositive M) {q : ι → ℝ} (hq : ∀ i, 0 < q i) (z : ι → ℝ) :
    IsStandardLCPSolution M q z ↔ z = 0 := by
  constructor
  · intro hsol
    funext i
    exact weight_eq_zero_of_copositive_of_pos M hcop q z hq hsol.weight_nonneg
      hsol.complementary i
  · rintro rfl
    exact isStandardLCPSolution_zero M fun i => (hq i).le

/-- The tournament positive-right-hand-side statement of `Tournament.lean` is
the copositive statement above: the tournament quadratic form is nonnegative
on the orthant for `1 ≤ t`, which is exactly copositivity.  The original
`positive_rhs_tournament_weight_eq_zero` is kept as the self-contained
tournament-only argument. -/
theorem positive_rhs_tournamentSkewMatrix_weight_eq_zero (t : ℝ) (A : ι → ι → ℝ)
    (hA : IsFractionalTournament A) (ht : 1 ≤ t) (d z : ι → ℝ) (hd : ∀ i, 0 < d i)
    (hz : ∀ i, 0 ≤ z i)
    (hcomp : ∀ i, z i * (d i + ∑ j, z j * tournamentSkewMatrix t A i j) = 0) :
    ∀ i, z i = 0 :=
  weight_eq_zero_of_copositive_of_pos (tournamentSkewMatrix t A)
    (fun y hy => tournamentSkewMatrix_quadratic_nonneg t A hA ht y hy) d z hd hz hcomp

/-! ## Strict copositivity -/

/-- Strict copositivity: the quadratic form is strictly positive at every
nonzero nonnegative vector. -/
def IsStrictlyCopositive (M : ι → ι → ℝ) : Prop :=
  ∀ z : ι → ℝ, (∀ i, 0 ≤ z i) → (∃ i, z i ≠ 0) → 0 < ∑ i, z i * ∑ j, z j * M i j

/-- Strict copositivity implies copositivity. -/
theorem IsStrictlyCopositive.isCopositive {M : ι → ι → ℝ}
    (h : IsStrictlyCopositive M) : IsCopositive M := by
  intro z hz
  by_cases hne : ∃ i, z i ≠ 0
  · exact (h z hz hne).le
  · have hzero : ∀ i, z i = 0 := by
      intro i
      by_contra hi
      exact hne ⟨i, hi⟩
    simp [hzero]

/-- **Strict copositivity forbids every nonzero complementary nonnegative
vector.**  Coordinatewise complementarity `z i * (Mz) i = 0` alone makes the
quadratic form vanish, which a strictly copositive matrix allows only at the
origin.  No sign condition on `Mz` is used, so this is stronger than `R₀`. -/
theorem IsStrictlyCopositive.eq_zero_of_complementary {M : ι → ι → ℝ}
    (h : IsStrictlyCopositive M) (z : ι → ℝ) (hz : ∀ i, 0 ≤ z i)
    (hcomp : ∀ i, z i * ∑ j, z j * M i j = 0) : ∀ i, z i = 0 := by
  intro i
  by_contra hi
  have hpos := h z hz ⟨i, hi⟩
  have hzero : (∑ k, z k * ∑ j, z j * M k j) = 0 :=
    Finset.sum_eq_zero fun k _ => hcomp k
  linarith

/-- Strict copositivity implies `R₀`: a homogeneous solution is in particular
a complementary nonnegative vector. -/
theorem IsStrictlyCopositive.isR0Matrix {M : ι → ι → ℝ}
    (h : IsStrictlyCopositive M) : IsR0Matrix M := by
  intro z hsol
  refine h.eq_zero_of_complementary z hsol.weight_nonneg fun k => ?_
  have hc := hsol.complementary k
  rwa [lcpResidual_zero] at hc

/-- **Karamardian's corollary.** A strictly copositive matrix is a standard
`Q`-matrix. -/
theorem isStandardQ_of_strictlyCopositive {M : ι → ι → ℝ}
    (h : IsStrictlyCopositive M) : IsStandardQ M :=
  copositive_isR0Matrix_isStandardQ M h.isCopositive h.isR0Matrix

/-! ## Uniform solution bounds under `R₀`

At an exact solution the residual sign condition and complementarity are
available as equalities, so the normalized homogeneous violation is `O(1/r)`
with no copositivity input and with a better constant than the variational
inequality bound of `CopositiveQ.lean`. -/

/-- **The violation bound at an exact solution.** If `z` solves `LCP(M, q)`
and has total mass `r > 0`, then the normalized point `z / r` has homogeneous
violation at most `(card ι + 1) * ‖q‖₁ / r`.  Copositivity is not used. -/
theorem homogeneousViolation_normalized_le_of_isStandardLCPSolution_of_bound (M : ι → ι → ℝ)
    (q z : ι → ℝ) (hsol : IsStandardLCPSolution M q z) {r Bq : ℝ} (hr : 0 < r)
    (hBq_nonneg : 0 ≤ Bq) (hq_le : ∀ i, |q i| ≤ Bq) (hsum : (∑ i, z i) = r) :
    homogeneousViolation M (fun i => z i / r) ≤
      ((Fintype.card ι : ℝ) + 1) * Bq / r := by
  classical
  -- Complementarity makes the pairing vanish, which bounds the quadratic form.
  have hpair : (∑ i, z i * lcpResidual M q z i) = 0 :=
    Finset.sum_eq_zero fun i _ => hsol.complementary i
  have hsplit : (∑ i, z i * lcpResidual M q z i) =
      (∑ i, z i * q i) + ∑ i, z i * ∑ j, z j * M i j := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by rw [lcpResidual_def]; ring
  have hzq_ge : -(r * Bq) ≤ ∑ i, z i * q i := by
    have hterm : ∀ i, -(z i * Bq) ≤ z i * q i := by
      intro i
      have h1 : -(z i * |q i|) ≤ z i * q i := by
        nlinarith [neg_abs_le (q i), hsol.weight_nonneg i]
      have h2 : z i * |q i| ≤ z i * Bq :=
        mul_le_mul_of_nonneg_left (hq_le i) (hsol.weight_nonneg i)
      linarith
    have hsum_le : (∑ i, -(z i * Bq)) ≤ ∑ i, z i * q i :=
      Finset.sum_le_sum fun i _ => hterm i
    have hconst : (∑ i, -(z i * Bq)) = -(r * Bq) := by
      rw [Finset.sum_neg_distrib, ← Finset.sum_mul, hsum]
    linarith [hconst.symm.le, hconst.le]
  have hquad_le : (∑ i, z i * ∑ j, z j * M i j) ≤ r * Bq := by
    rw [hsplit] at hpair; linarith
  -- The residual sign condition bounds every row of the matrix action.
  have hres_ge : ∀ i, -Bq ≤ ∑ j, z j * M i j := by
    intro i
    have h := hsol.residual_nonneg i
    rw [lcpResidual_def] at h
    have habs := le_abs_self (q i)
    linarith [hq_le i]
  -- Normalize.
  set p : ι → ℝ := fun i => z i / r with hp
  have hrow : ∀ i, (∑ j, p j * M i j) = (∑ j, z j * M i j) / r := by
    intro i
    rw [Finset.sum_div]
    exact Finset.sum_congr rfl fun j _ => by rw [hp]; ring
  have hquadp : (∑ i, p i * ∑ j, p j * M i j) =
      (∑ i, z i * ∑ j, z j * M i j) / (r * r) := by
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hrow i, hp]
    field_simp
  have hquadp_le : (∑ i, p i * ∑ j, p j * M i j) ≤ Bq / r := by
    have hrr : (0 : ℝ) < r * r := by positivity
    rw [hquadp, div_le_iff₀ hrr]
    have hclear : Bq / r * (r * r) = Bq * r := by field_simp
    rw [hclear]
    nlinarith [hquad_le]
  have hrowp_ge : ∀ i, -(Bq / r) ≤ ∑ j, p j * M i j := by
    intro i
    have hdiv : (-Bq) / r ≤ (∑ j, z j * M i j) / r := by gcongr; exact hres_ge i
    rw [hrow i, ← neg_div]
    exact hdiv
  -- Assemble the two pieces of the violation.
  have hpiece1 : max 0 (∑ i, p i * ∑ j, p j * M i j) ≤ Bq / r :=
    max_le (by positivity) hquadp_le
  have hpiece2 : (∑ i, max 0 (-(∑ j, p j * M i j))) ≤ (Fintype.card ι : ℝ) * (Bq / r) := by
    have hbound : ∀ i, max 0 (-(∑ j, p j * M i j)) ≤ Bq / r := by
      intro i
      exact max_le (by positivity) (by linarith [hrowp_ge i])
    calc (∑ i, max 0 (-(∑ j, p j * M i j))) ≤ ∑ _i : ι, Bq / r :=
          Finset.sum_le_sum fun i _ => hbound i
      _ = (Fintype.card ι : ℝ) * (Bq / r) := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [homogeneousViolation]
  have hfinal : Bq / r + (Fintype.card ι : ℝ) * (Bq / r) =
      ((Fintype.card ι : ℝ) + 1) * Bq / r := by
    field_simp
    ring
  linarith [hpiece1, hpiece2, hfinal.symm.le, hfinal.le]

/-- The `‖q‖₁` reading of the violation bound at an exact solution: the total
`∑ i, |q i|` bounds every coordinate. -/
theorem homogeneousViolation_normalized_le_of_isStandardLCPSolution (M : ι → ι → ℝ)
    (q z : ι → ℝ) (hsol : IsStandardLCPSolution M q z) {r : ℝ} (hr : 0 < r)
    (hsum : (∑ i, z i) = r) :
    homogeneousViolation M (fun i => z i / r) ≤
      ((Fintype.card ι : ℝ) + 1) * (∑ i, |q i|) / r :=
  homogeneousViolation_normalized_le_of_isStandardLCPSolution_of_bound M q z hsol hr
    (Finset.sum_nonneg fun _ _ => abs_nonneg _)
    (fun i => Finset.single_le_sum (f := fun i => |q i|) (fun _ _ => abs_nonneg _)
      (Finset.mem_univ i))
    hsum

/-- **Uniform solution bounds under `R₀`.** For an `R₀` matrix and any
coordinatewise bound `B` on `q`, all solutions of `LCP(M, q)` have total mass
at most a single constant `C`.  An unbounded family of solutions would
normalize to simplex points of vanishing homogeneous violation, and the
compactness limit of `CopositiveQ.lean` would then produce an exact homogeneous
solution.  A bound on `‖q‖₁` is one such coordinatewise bound, so this covers a
strictly larger family of right-hand sides for the same `B`. -/
theorem exists_bound_sum_of_isR0Matrix (M : ι → ι → ℝ) (hR0 : IsR0Matrix M) {B : ℝ}
    (hB : 0 ≤ B) :
    ∃ C : ℝ, ∀ q z : ι → ℝ, (∀ i, |q i| ≤ B) → IsStandardLCPSolution M q z →
      (∑ i, z i) ≤ C := by
  classical
  by_contra hno
  push Not at hno
  set D : ℝ := ((Fintype.card ι : ℝ) + 1) * B with hD
  have hD_nonneg : 0 ≤ D := by
    have hcard : (0 : ℝ) ≤ (Fintype.card ι : ℝ) + 1 := by positivity
    exact mul_nonneg hcard hB
  refine (isR0Matrix_iff_not_singletonLCPFeasible M).mp hR0 ?_
  refine singletonLCPFeasible_of_approximate M fun ε hε => ?_
  set C : ℝ := max 1 (D / ε) with hC
  obtain ⟨q, z, hq, hsol, hlt⟩ := hno C
  have hC_ge_one : (1 : ℝ) ≤ C := le_max_left _ _
  have hr : 0 < ∑ i, z i := lt_of_lt_of_le (by linarith) hlt.le
  set r : ℝ := ∑ i, z i with hrdef
  have hmem : (fun i => z i / r) ∈ stdSimplex ℝ ι :=
    ⟨fun i => div_nonneg (hsol.weight_nonneg i) hr.le,
      by rw [← Finset.sum_div, ← hrdef]; exact div_self hr.ne'⟩
  refine ⟨fun i => z i / r, hmem, ?_⟩
  have hviol :=
    homogeneousViolation_normalized_le_of_isStandardLCPSolution_of_bound M q z hsol
      hr hB hq rfl
  have hCr : D / r ≤ D / C := by
    refine div_le_div_of_nonneg_left hD_nonneg (by linarith) hlt.le
  have hCε : D / C ≤ ε := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < C)]
    have hdiv : D / ε ≤ C := le_max_right _ _
    rw [div_le_iff₀ hε] at hdiv
    nlinarith [hdiv, hC_ge_one, hε]
  linarith

/-! ## Integral tournaments and principal subtournaments -/

/-- An integral tournament: a fractional tournament all of whose pair weights
are `0` or `1`. -/
def IsIntegralTournament (A : ι → ι → ℝ) : Prop :=
  IsFractionalTournament A ∧ ∀ i j, A i j = 0 ∨ A i j = 1

section Restriction

variable {κ : Type*} [Fintype κ]

omit [Fintype ι] [Fintype κ] in
/-- An injective relabelling of a fractional tournament is again one. -/
theorem isFractionalTournament_comp {A : ι → ι → ℝ} (hA : IsFractionalTournament A)
    (f : κ → ι) (hf : Function.Injective f) :
    IsFractionalTournament fun a b => A (f a) (f b) :=
  ⟨fun a => hA.1 (f a), fun a b => hA.2.1 (f a) (f b),
    fun a b hab => hA.2.2 (f a) (f b) fun h => hab (hf h)⟩

omit [Fintype ι] [Fintype κ] in
/-- An injective relabelling of an integral tournament is again one. -/
theorem isIntegralTournament_comp {A : ι → ι → ℝ} (hA : IsIntegralTournament A)
    (f : κ → ι) (hf : Function.Injective f) :
    IsIntegralTournament fun a b => A (f a) (f b) :=
  ⟨isFractionalTournament_comp hA.1 f hf, fun a b => hA.2 (f a) (f b)⟩

omit [Fintype ι] [Fintype κ] in
/-- The skew-dominant matrix commutes with relabelling. -/
theorem tournamentSkewMatrix_comp (t : ℝ) (A : ι → ι → ℝ) (f : κ → ι) :
    (tournamentSkewMatrix t fun a b => A (f a) (f b)) =
      fun a b => tournamentSkewMatrix t A (f a) (f b) := rfl

end Restriction

/-- **The all-loser witness.** If some vertex has no outgoing weight at all,
its column of the skew-dominant matrix is nonnegative and its diagonal entry
vanishes, so the homogeneous simplex LCP is feasible. -/
theorem singletonLCPFeasible_tournamentSkewMatrix_of_row_eq_zero {t : ℝ} {A : ι → ι → ℝ}
    (hA : IsFractionalTournament A) (ht : 0 ≤ t) {i : ι} (hrow : ∀ j, A i j = 0) :
    SingletonLCPFeasible (tournamentSkewMatrix t A) := by
  refine singletonLCPFeasible_of_diag_eq_zero i ?_ fun j => ?_
  · show t * A i i - A i i = 0
    rw [hA.1 i]; ring
  · show 0 ≤ t * A j i - A i j
    rw [hrow j]
    have hji : 0 ≤ A j i := hA.2.1 j i
    nlinarith

/-- **The integral-tournament dichotomy.** For `t > 1` an integral tournament
either has a unit out-neighbour at every vertex, and then its skew-dominant
matrix is standard `Q`, or some vertex loses to everybody, and then the
homogeneous simplex LCP is feasible.

The dichotomy is exhaustive only because the pair weights are `0` or `1`; for
a genuinely fractional tournament a vertex can have outgoing weight without
having a unit out-neighbour, and neither branch need apply. -/
theorem isStandardQ_or_singletonLCPFeasible_of_isIntegralTournament (t : ℝ)
    {A : ι → ι → ℝ} (hA : IsIntegralTournament A) (ht : 1 < t) :
    IsStandardQ (tournamentSkewMatrix t A) ∨
      SingletonLCPFeasible (tournamentSkewMatrix t A) := by
  classical
  by_cases hunit : FractionalTournamentHasUnitOutneighbor A
  · exact Or.inl (isStandardQ_tournamentSkewMatrix t A hA.1 hunit ht)
  · right
    have hloser : ∃ i, ∀ j, i ≠ j → A i j ≠ 1 := by
      by_contra hcon
      push Not at hcon
      exact hunit hcon
    obtain ⟨i, hi⟩ := hloser
    have hrow : ∀ j, A i j = 0 := by
      intro j
      by_cases hij : i = j
      · rw [hij]; exact hA.1.1 j
      · rcases hA.2 i j with h | h
        · exact h
        · exact absurd h (hi j hij)
    exact singletonLCPFeasible_tournamentSkewMatrix_of_row_eq_zero hA.1
      (lt_trans zero_lt_one ht).le hrow

omit [Fintype ι] in
/-- The dichotomy transported to an injective relabelling, which is the form
consumed by principal-submatrix statements. -/
theorem isStandardQ_or_singletonLCPFeasible_comp_of_isIntegralTournament
    {κ : Type*} [Fintype κ] (t : ℝ) {A : ι → ι → ℝ} (hA : IsIntegralTournament A)
    (ht : 1 < t) (f : κ → ι) (hf : Function.Injective f) :
    IsStandardQ (fun a b => tournamentSkewMatrix t A (f a) (f b)) ∨
      SingletonLCPFeasible fun a b => tournamentSkewMatrix t A (f a) (f b) := by
  have h := isStandardQ_or_singletonLCPFeasible_of_isIntegralTournament t
    (isIntegralTournament_comp hA f hf) ht
  rwa [tournamentSkewMatrix_comp] at h

end Math.LinearProgramming
