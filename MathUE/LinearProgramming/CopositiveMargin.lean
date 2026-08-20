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
* `copositiveMargin_sub_le_copositiveMargin` — the one-sided estimate: an
  explicit lower bound for the margin of a perturbed matrix
* `abs_copositiveMargin_sub_le` — the margin is Lipschitz in the matrix, with
  constant one
* `isStrictlyCopositive_of_copositiveMargin_lt` — strict copositivity is open,
  with a computable radius
* `isStandardQ_of_copositiveMargin_lt` — the resulting perturbation stability of
  the standard-`Q` placement
* `IsCopositive.mono`, `IsStrictlyCopositive.mono` and `copositiveMargin_mono` —
  the entrywise order
* `copositiveMargin_le_r0Margin` — comparison with the `R₀` margin
* `copositiveMargin_unit` and `r0Margin_unit` — both margins in the one-by-one
  case, where the two perturbation radii separate in both directions

Unlike the `R₀` margin, this one is monotone in the entrywise order: the
quadratic form is the whole of the functional, and raising an entry raises it at
every nonnegative vector.  The comparison `copositiveMargin M ≤ r0Margin M` is
unconditional, but it does not order the two perturbation radii
`copositiveMargin M` and `r0Margin M / (card ι + 1)`, and nothing else does
either: `r0Margin_div_lt_copositiveMargin_unit_one` and
`copositiveMargin_lt_r0Margin_div_unit_neg_one` separate them in both
directions.
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

/-- **The perturbed margin has an explicit lower bound.**  At entrywise
deviation `δ` the margin of `N` is at least the margin of `M` diminished by `δ`.

This one-sided form is what composes along a sequence of perturbations; the
two-sided estimate `abs_copositiveMargin_sub_le` discards the direction. -/
theorem copositiveMargin_sub_le_copositiveMargin [Nonempty ι] (M N : ι → ι → ℝ)
    {δ : ℝ} (hδ : ∀ i j, |M i j - N i j| ≤ δ) :
    copositiveMargin M - δ ≤ copositiveMargin N := by
  refine le_copositiveMargin N fun p hp => ?_
  have hle := (abs_le.mp (abs_quadratic_sub_le M N hδ hp)).2
  linarith [copositiveMargin_le M hp]

/-- **The margin is Lipschitz in the matrix**, with constant one. -/
theorem abs_copositiveMargin_sub_le [Nonempty ι] (M N : ι → ι → ℝ) {δ : ℝ}
    (hδ : ∀ i j, |M i j - N i j| ≤ δ) :
    |copositiveMargin M - copositiveMargin N| ≤ δ := by
  have hswap : ∀ i j, |N i j - M i j| ≤ δ := fun i j => by
    rw [abs_sub_comm]; exact hδ i j
  exact abs_sub_le_iff.mpr
    ⟨by linarith [copositiveMargin_sub_le_copositiveMargin M N hδ],
      by linarith [copositiveMargin_sub_le_copositiveMargin N M hswap]⟩

/-- **Strict copositivity is an open condition, with a computable radius.**  Any
matrix whose entries deviate from those of a strictly copositive matrix `M` by
less than `copositiveMargin M` is again strictly copositive.

The margin of the perturbed matrix is bounded below explicitly by
`copositiveMargin_sub_le_copositiveMargin`. -/
theorem isStrictlyCopositive_of_copositiveMargin_lt [Nonempty ι] {M N : ι → ι → ℝ}
    {δ : ℝ} (hδ : ∀ i j, |M i j - N i j| ≤ δ) (hlt : δ < copositiveMargin M) :
    IsStrictlyCopositive N := by
  refine (copositiveMargin_pos_iff_isStrictlyCopositive N).mp ?_
  linarith [copositiveMargin_sub_le_copositiveMargin M N hδ]

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

/-! ## The entrywise order

Raising an entry raises the quadratic form at every nonnegative vector, so
copositivity, strict copositivity and the margin are all monotone in the
entrywise order.  This is a one-sided stability statement of a different shape
from the perturbation balls above: it constrains the sign of the change instead
of its size, and it is unbounded in the favourable direction. -/

/-- On the nonnegative orthant the quadratic form is monotone in the entries. -/
theorem quadratic_le_of_entrywise_le {M N : ι → ι → ℝ} (h : ∀ i j, M i j ≤ N i j)
    {z : ι → ℝ} (hz : ∀ i, 0 ≤ z i) :
    (∑ i, z i * ∑ j, z j * M i j) ≤ ∑ i, z i * ∑ j, z j * N i j :=
  Finset.sum_le_sum fun i _ =>
    mul_le_mul_of_nonneg_left
      (Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (h i j) (hz j)) (hz i)

/-- **Copositivity is upward closed in the entrywise order.** -/
theorem IsCopositive.mono {M N : ι → ι → ℝ} (hM : IsCopositive M)
    (h : ∀ i j, M i j ≤ N i j) : IsCopositive N :=
  fun z hz => (hM z hz).trans (quadratic_le_of_entrywise_le h hz)

/-- **Strict copositivity is upward closed in the entrywise order.** -/
theorem IsStrictlyCopositive.mono {M N : ι → ι → ℝ} (hM : IsStrictlyCopositive M)
    (h : ∀ i j, M i j ≤ N i j) : IsStrictlyCopositive N :=
  fun z hz hne => (hM z hz hne).trans_le (quadratic_le_of_entrywise_le h hz)

/-- **The margin is monotone in the entrywise order.**  It is the quantitative
form of `IsCopositive.mono` and `IsStrictlyCopositive.mono`, which are the two
readings of this inequality at the thresholds `0 ≤ ·` and `0 < ·`. -/
theorem copositiveMargin_mono [Nonempty ι] {M N : ι → ι → ℝ}
    (h : ∀ i j, M i j ≤ N i j) : copositiveMargin M ≤ copositiveMargin N :=
  le_copositiveMargin N fun _ hp =>
    (copositiveMargin_le M hp).trans (quadratic_le_of_entrywise_le h hp.1)

/-! ## Comparison with the `R₀` margin -/

/-- **The copositivity margin never exceeds the `R₀` margin.**  The homogeneous
violation dominates the quadratic form at every simplex point, because it adds
the total negative part of the matrix action to the positive part of that form.

This is the quantitative reading of `IsStrictlyCopositive.isR0Matrix`: a
positive copositivity margin forces a positive `R₀` margin, which is strict
copositivity forcing `R₀` by `r0Margin_pos_iff_isR0Matrix`. -/
theorem copositiveMargin_le_r0Margin [Nonempty ι] (M : ι → ι → ℝ) :
    copositiveMargin M ≤ r0Margin M := by
  refine le_r0Margin M fun p hp => ?_
  have hmax : (∑ i, p i * ∑ j, p j * M i j) ≤ max 0 (∑ i, p i * ∑ j, p j * M i j) :=
    le_max_right _ _
  have hneg : (0 : ℝ) ≤ ∑ i, max 0 (-(∑ j, p j * M i j)) :=
    Finset.sum_nonneg fun _ _ => le_max_left _ _
  rw [homogeneousViolation]
  linarith [copositiveMargin_le M hp]

/-! ## The one-by-one case

On a one-element index type the standard simplex is a single point and both
margins are read off the single entry: the copositivity margin is that entry,
and the `R₀` margin is its absolute value, because the negative part of the
matrix action replaces the quadratic form as soon as the entry is negative.

This already settles the comparison of the two perturbation radii
`copositiveMargin M` and `r0Margin M / (card ι + 1)`: neither bounds the other,
even though `copositiveMargin_le_r0Margin` orders the margins themselves. -/

/-- On a one-element index type the standard simplex is the single point `1`. -/
theorem mem_stdSimplex_unit_iff {p : Unit → ℝ} :
    p ∈ stdSimplex ℝ Unit ↔ p () = 1 := by
  constructor
  · intro hp
    simpa using hp.2
  · intro hp
    exact ⟨fun i => by cases i; rw [hp]; exact zero_le_one, by simpa using hp⟩

/-- The copositivity margin of a one-by-one matrix is its entry. -/
theorem copositiveMargin_unit (x : ℝ) : copositiveMargin (fun _ _ : Unit => x) = x := by
  have hmem : (fun _ : Unit => (1 : ℝ)) ∈ stdSimplex ℝ Unit :=
    mem_stdSimplex_unit_iff.mpr rfl
  refine le_antisymm ?_ (le_copositiveMargin _ fun p hp => ?_)
  · simpa using copositiveMargin_le (fun _ _ : Unit => x) hmem
  · rw [mem_stdSimplex_unit_iff] at hp
    simp [hp]

/-- The `R₀` margin of a one-by-one matrix is the absolute value of its
entry. -/
theorem r0Margin_unit (x : ℝ) : r0Margin (fun _ _ : Unit => x) = |x| := by
  have habs : max 0 x + max 0 (-x) = |x| := by
    rcases le_total 0 x with hx | hx
    · rw [max_eq_right hx, max_eq_left (by linarith), abs_of_nonneg hx, add_zero]
    · rw [max_eq_left hx, max_eq_right (by linarith), abs_of_nonpos hx, zero_add]
  have hval : ∀ p ∈ stdSimplex ℝ Unit,
      homogeneousViolation (fun _ _ : Unit => x) p = |x| := by
    intro p hp
    rw [mem_stdSimplex_unit_iff] at hp
    simp [homogeneousViolation, hp, habs]
  have hmem : (fun _ : Unit => (1 : ℝ)) ∈ stdSimplex ℝ Unit :=
    mem_stdSimplex_unit_iff.mpr rfl
  refine le_antisymm ?_ (le_r0Margin _ fun p hp => (hval p hp).ge)
  exact (r0Margin_le (fun _ _ : Unit => x) hmem).trans (hval _ hmem).le

/-- **The `R₀` radius does not bound the copositivity radius.**  At the
one-by-one matrix with entry `1` the copositivity radius is `1` and the `R₀`
radius is `1 / 2`. -/
theorem r0Margin_div_lt_copositiveMargin_unit_one :
    r0Margin (fun _ _ : Unit => (1 : ℝ)) / ((Fintype.card Unit : ℝ) + 1) <
      copositiveMargin (fun _ _ : Unit => (1 : ℝ)) := by
  rw [copositiveMargin_unit, r0Margin_unit]
  norm_num

/-- **The copositivity radius does not bound the `R₀` radius.**  At the
one-by-one matrix with entry `-1` the copositivity margin is `-1` and the `R₀`
radius is `1 / 2`. -/
theorem copositiveMargin_lt_r0Margin_div_unit_neg_one :
    copositiveMargin (fun _ _ : Unit => (-1 : ℝ)) <
      r0Margin (fun _ _ : Unit => (-1 : ℝ)) / ((Fintype.card Unit : ℝ) + 1) := by
  rw [copositiveMargin_unit, r0Margin_unit]
  norm_num

end Math.LinearProgramming
