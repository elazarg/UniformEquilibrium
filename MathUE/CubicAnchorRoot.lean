/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Order.IntermediateValue

/-!
# Roots of an anchor cubic and their backward partial sums

An *anchor cubic* is the polynomial `a + bβ + cβ² + dβ³` read as a discounted
sum of four successive coefficients at a common per-step survival factor `β`.
Two facts about such a cubic are recorded here.

* If the leading coefficient `a` is negative and the total `a + b + c + d` is
  positive, the intermediate value theorem places a root strictly inside
  `(0, 1)`.
* At a root with `β > 0` the *backward partial sum* `b + cβ + dβ²` — the anchor
  cubic with its first coefficient dropped and the rest advanced one step —
  equals `-a / β`.  When `a < 0` this is positive: the anchor equation itself
  funds the deepest partial sum, with no further sign hypothesis on
  `b`, `c`, `d`.

## Main definitions

* `cubicAnchor` — the value `a + bβ + cβ² + dβ³`
* `cubicAnchorTail` — the backward partial sum `b + cβ + dβ²`

Each root statement is given on an arbitrary interval, which is what locates a
root on the side of a prescribed point rather than merely inside the unit
interval, and in both orientations: the ascending one crosses zero upward, the
primed descending one crosses it downward.

When the two higher coefficients are nonnegative the unit-interval statement
reverses: a root in `(0, 1)` forces the total to be positive, so for `a < 0`,
`0 ≤ c` and `0 ≤ d` the positive total and the interior root are equivalent.
Setting `d = 0` reads all of this at quadratic degree.

## Main results

* `exists_cubicAnchor_root_mem_Ioo_of_neg_of_pos`,
  `exists_cubicAnchor_root_mem_Ioc_of_neg_of_nonneg`,
  `exists_cubicAnchor_root_mem_Ioo_of_pos_of_neg` and
  `exists_cubicAnchor_root_mem_Ioc_of_pos_of_nonpos` — a root in a prescribed
  interval, in either orientation
* `exists_cubicAnchor_root_mem_Ioo` and `exists_cubicAnchor_root_mem_Ioo'` —
  the root in `(0, 1)`
* `cubicAnchor_total_pos_of_root_mem_Ioo` and
  `cubicAnchor_total_pos_iff_exists_root_mem_Ioo` — the converse and the
  resulting criterion at nonnegative higher coefficients
* `exists_quadratic_root_mem_Ioo` and
  `quadratic_total_pos_iff_exists_root_mem_Ioo` — the quadratic reading
* `cubicAnchorTail_eq_of_root` — the backward partial sum at a nonzero root
* `cubicAnchorTail_pos_of_root` — its positivity at a positive root of an
  anchor cubic with negative leading coefficient

A third fact runs the other way, excluding roots rather than producing them.
Writing the cubic as a nonnegative multiple of `(β + r)(β - t)²` plus an
affine remainder certifies a lower bound on `[0, 1]`: the square is
nonnegative, the linear factor is nonnegative there as soon as `r` is, and an
affine function on a segment is bounded below by the smaller of its two
endpoint values.  A positive bound excludes every root in the segment.  This
is the sign-analysis direction the intermediate value theorem cannot supply.

* `cubicAnchor_ge_of_square_add_affine` — the lower bound from such a
  certificate
* `cubicAnchor_ne_zero_of_square_add_affine` — the root exclusion it yields
-/

noncomputable section

namespace Math

/-- The anchor cubic `a + bβ + cβ² + dβ³` at survival factor `β`. -/
def cubicAnchor (a b c d β : ℝ) : ℝ := a + b * β + c * β ^ 2 + d * β ^ 3

/-- The backward partial sum `b + cβ + dβ²`: the anchor cubic with its first
coefficient dropped and the remaining ones advanced by one step. -/
def cubicAnchorTail (b c d β : ℝ) : ℝ := b + c * β + d * β ^ 2

@[simp] theorem cubicAnchor_zero (a b c d : ℝ) : cubicAnchor a b c d 0 = a := by
  simp [cubicAnchor]

@[simp] theorem cubicAnchor_one (a b c d : ℝ) :
    cubicAnchor a b c d 1 = a + b + c + d := by
  simp [cubicAnchor]

theorem continuous_cubicAnchor (a b c d : ℝ) : Continuous (cubicAnchor a b c d) := by
  unfold cubicAnchor
  fun_prop

/-- **A root strictly inside a prescribed interval.**  An anchor cubic that is
negative at the left endpoint and positive at the right vanishes strictly
between them. -/
theorem exists_cubicAnchor_root_mem_Ioo_of_neg_of_pos {a b c d lo hi : ℝ}
    (hle : lo ≤ hi) (hlo : cubicAnchor a b c d lo < 0)
    (hhi : 0 < cubicAnchor a b c d hi) :
    ∃ β ∈ Set.Ioo lo hi, cubicAnchor a b c d β = 0 :=
  intermediate_value_Ioo hle (continuous_cubicAnchor a b c d).continuousOn
    ⟨hlo, hhi⟩

/-- **A root in a prescribed half-open interval.**  An anchor cubic that is
negative at the left endpoint and nonnegative at the right vanishes past the
left endpoint and no later than the right one. -/
theorem exists_cubicAnchor_root_mem_Ioc_of_neg_of_nonneg {a b c d lo hi : ℝ}
    (hle : lo ≤ hi) (hlo : cubicAnchor a b c d lo < 0)
    (hhi : 0 ≤ cubicAnchor a b c d hi) :
    ∃ β ∈ Set.Ioc lo hi, cubicAnchor a b c d β = 0 :=
  intermediate_value_Ioc hle (continuous_cubicAnchor a b c d).continuousOn
    ⟨hlo, hhi⟩

/-- **A root strictly inside the unit interval.**  An anchor cubic that starts
negative at `β = 0` and is positive at `β = 1` vanishes somewhere in between. -/
theorem exists_cubicAnchor_root_mem_Ioo {a b c d : ℝ} (ha : a < 0)
    (htotal : 0 < a + b + c + d) :
    ∃ β ∈ Set.Ioo (0 : ℝ) 1, cubicAnchor a b c d β = 0 :=
  exists_cubicAnchor_root_mem_Ioo_of_neg_of_pos zero_le_one
    (by rwa [cubicAnchor_zero]) (by rwa [cubicAnchor_one])

/-- **A root strictly inside a prescribed interval, descending.**  An anchor
cubic that is positive at the left endpoint and negative at the right vanishes
strictly between them. -/
theorem exists_cubicAnchor_root_mem_Ioo_of_pos_of_neg {a b c d lo hi : ℝ}
    (hle : lo ≤ hi) (hlo : 0 < cubicAnchor a b c d lo)
    (hhi : cubicAnchor a b c d hi < 0) :
    ∃ β ∈ Set.Ioo lo hi, cubicAnchor a b c d β = 0 :=
  intermediate_value_Ioo' hle (continuous_cubicAnchor a b c d).continuousOn
    ⟨hhi, hlo⟩

/-- **A root in a prescribed half-open interval, descending.**  An anchor cubic
that is positive at the left endpoint and nonpositive at the right vanishes past
the left endpoint and no later than the right one. -/
theorem exists_cubicAnchor_root_mem_Ioc_of_pos_of_nonpos {a b c d lo hi : ℝ}
    (hle : lo ≤ hi) (hlo : 0 < cubicAnchor a b c d lo)
    (hhi : cubicAnchor a b c d hi ≤ 0) :
    ∃ β ∈ Set.Ioc lo hi, cubicAnchor a b c d β = 0 :=
  intermediate_value_Ioc' hle (continuous_cubicAnchor a b c d).continuousOn
    ⟨hhi, hlo⟩

/-- **A root strictly inside the unit interval, descending.**  An anchor cubic
that starts positive at `β = 0` and is negative at `β = 1` vanishes somewhere in
between. -/
theorem exists_cubicAnchor_root_mem_Ioo' {a b c d : ℝ} (ha : 0 < a)
    (htotal : a + b + c + d < 0) :
    ∃ β ∈ Set.Ioo (0 : ℝ) 1, cubicAnchor a b c d β = 0 :=
  exists_cubicAnchor_root_mem_Ioo_of_pos_of_neg zero_le_one
    (by rwa [cubicAnchor_zero]) (by rwa [cubicAnchor_one])

/-! ## The converse at nonnegative higher coefficients

With `a < 0` and the two higher coefficients nonnegative, a root in `(0, 1)`
forces the total to be positive, so the hypothesis of
`exists_cubicAnchor_root_mem_Ioo` is not merely sufficient but necessary.  The
identity behind it is

`β * (a + b + c + d) = (1 - β) * (-a + cβ + dβ + dβ²) + cubicAnchor a b c d β`,

whose right-hand side is a product of positive factors at a root with
`0 < β < 1`.  No sign hypothesis on `b` enters. -/

/-- **A root inside the unit interval forces a positive total.**  At `a < 0`
with `c` and `d` nonnegative, a root of the anchor cubic strictly between `0`
and `1` makes `a + b + c + d` positive. -/
theorem cubicAnchor_total_pos_of_root_mem_Ioo {a b c d β : ℝ} (ha : a < 0)
    (hc : 0 ≤ c) (hd : 0 ≤ d) (hβ : β ∈ Set.Ioo (0 : ℝ) 1)
    (hroot : cubicAnchor a b c d β = 0) : 0 < a + b + c + d := by
  obtain ⟨hβ0, hβ1⟩ := hβ
  have hcβ : 0 ≤ c * β := mul_nonneg hc hβ0.le
  have hdβ : 0 ≤ d * β := mul_nonneg hd hβ0.le
  have hdβ2 : 0 ≤ d * β ^ 2 := mul_nonneg hd (sq_nonneg β)
  have hfac : 0 < (1 - β) * (-a + c * β + d * β + d * β ^ 2) :=
    mul_pos (by linarith) (by linarith)
  have hkey : β * (a + b + c + d) = (1 - β) * (-a + c * β + d * β + d * β ^ 2) := by
    rw [cubicAnchor] at hroot
    have hexp : (1 - β) * (-a + c * β + d * β + d * β ^ 2) =
        β * (a + b + c + d) - (a + b * β + c * β ^ 2 + d * β ^ 3) := by ring
    rw [hexp, hroot, sub_zero]
  have hprod : 0 < β * (a + b + c + d) := by rw [hkey]; exact hfac
  by_contra hcon
  rw [not_lt] at hcon
  exact absurd hprod (not_lt.mpr (mul_nonpos_of_nonneg_of_nonpos hβ0.le hcon))

/-- **The unit-interval root criterion.**  For an anchor cubic with negative
leading coefficient and nonnegative higher coefficients, a positive total and a
root strictly inside `(0, 1)` are the same condition. -/
theorem cubicAnchor_total_pos_iff_exists_root_mem_Ioo {a b c d : ℝ} (ha : a < 0)
    (hc : 0 ≤ c) (hd : 0 ≤ d) :
    0 < a + b + c + d ↔ ∃ β ∈ Set.Ioo (0 : ℝ) 1, cubicAnchor a b c d β = 0 :=
  ⟨exists_cubicAnchor_root_mem_Ioo ha,
    fun ⟨_, hβ, hroot⟩ => cubicAnchor_total_pos_of_root_mem_Ioo ha hc hd hβ hroot⟩

/-! ## The quadratic companion

Setting `d = 0` turns the anchor cubic into `a + bβ + cβ²`.  The statements
below are that reading, spelled out so that a consumer at quadratic degree does
not have to unfold `cubicAnchor`. -/

/-- **A quadratic root strictly inside the unit interval.** -/
theorem exists_quadratic_root_mem_Ioo {a b c : ℝ} (ha : a < 0)
    (htotal : 0 < a + b + c) :
    ∃ β ∈ Set.Ioo (0 : ℝ) 1, a + b * β + c * β ^ 2 = 0 := by
  obtain ⟨β, hβ, hroot⟩ :=
    exists_cubicAnchor_root_mem_Ioo (a := a) (b := b) (c := c) (d := 0) ha
      (by linarith)
  exact ⟨β, hβ, by simpa [cubicAnchor] using hroot⟩

/-- **The unit-interval root criterion at quadratic degree.**  For `a < 0` and
`0 ≤ c`, the total `a + b + c` is positive exactly when `a + bβ + cβ²` has a
root strictly between `0` and `1`. -/
theorem quadratic_total_pos_iff_exists_root_mem_Ioo {a b c : ℝ} (ha : a < 0)
    (hc : 0 ≤ c) :
    0 < a + b + c ↔ ∃ β ∈ Set.Ioo (0 : ℝ) 1, a + b * β + c * β ^ 2 = 0 := by
  refine ⟨fun htotal => exists_quadratic_root_mem_Ioo ha htotal, ?_⟩
  rintro ⟨β, hβ, hroot⟩
  have h := cubicAnchor_total_pos_of_root_mem_Ioo (a := a) (b := b) (c := c)
    (d := 0) ha hc le_rfl hβ (by simpa [cubicAnchor] using hroot)
  linarith

/-- **The anchor equation funds the backward partial sum.**  At a nonzero root
of the anchor cubic the backward partial sum is exactly `-a / β`. -/
theorem cubicAnchorTail_eq_of_root {a b c d β : ℝ} (hβ : β ≠ 0)
    (hroot : cubicAnchor a b c d β = 0) : cubicAnchorTail b c d β = -a / β := by
  rw [cubicAnchorTail, eq_div_iff hβ]
  simp only [cubicAnchor] at hroot
  have hexpand : (b + c * β + d * β ^ 2) * β = b * β + c * β ^ 2 + d * β ^ 3 := by
    ring
  rw [hexpand]
  linarith

/-- **Automatic patience.**  At a positive root of an anchor cubic with
negative leading coefficient the backward partial sum is positive, whatever
the signs of the remaining coefficients. -/
theorem cubicAnchorTail_pos_of_root {a b c d β : ℝ} (hβ : 0 < β) (ha : a < 0)
    (hroot : cubicAnchor a b c d β = 0) : 0 < cubicAnchorTail b c d β := by
  rw [cubicAnchorTail_eq_of_root hβ.ne' hroot]
  exact div_pos (neg_pos.mpr ha) hβ

/-! ## Excluding roots by a square-plus-affine certificate -/

/-- **A lower bound on the unit segment.**  If the anchor cubic is a
nonnegative multiple of `(β + r)(β - t)²` plus the affine function
`p + q β`, with `r` nonnegative, then on `[0, 1]` it is bounded below by the
smaller of the affine function's two endpoint values.

Both factors of the cubic term are nonnegative on the segment — the square
always, the linear factor because `β` and `r` are — so the cubic term only
adds, and an affine function on a segment is least at an endpoint. -/
theorem cubicAnchor_ge_of_square_add_affine {a b c d k r t lin₀ lin₁ : ℝ}
    (hcert : ∀ β : ℝ,
      cubicAnchor a b c d β = k * ((β + r) * (β - t) ^ 2) + (lin₀ + lin₁ * β))
    (hk : 0 ≤ k) (hr : 0 ≤ r) {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1) :
    min lin₀ (lin₀ + lin₁) ≤ cubicAnchor a b c d β := by
  have hsquare : 0 ≤ k * ((β + r) * (β - t) ^ 2) :=
    mul_nonneg hk (mul_nonneg (by linarith) (sq_nonneg _))
  have haffine : min lin₀ (lin₀ + lin₁) ≤ lin₀ + lin₁ * β := by
    rcases le_or_gt 0 lin₁ with hlin | hlin
    · exact le_trans (min_le_left _ _) (by nlinarith)
    · exact le_trans (min_le_right _ _) (by nlinarith)
  rw [hcert β]
  linarith

/-- **Root exclusion.**  A square-plus-affine certificate whose affine part is
positive at both endpoints leaves the anchor cubic without a root in
`[0, 1]`. -/
theorem cubicAnchor_ne_zero_of_square_add_affine {a b c d k r t lin₀ lin₁ : ℝ}
    (hcert : ∀ β : ℝ,
      cubicAnchor a b c d β = k * ((β + r) * (β - t) ^ 2) + (lin₀ + lin₁ * β))
    (hk : 0 ≤ k) (hr : 0 ≤ r) (hp : 0 < lin₀) (hpq : 0 < lin₀ + lin₁)
    {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1) : cubicAnchor a b c d β ≠ 0 := by
  have hmin : 0 < min lin₀ (lin₀ + lin₁) := lt_min hp hpq
  have hbound := cubicAnchor_ge_of_square_add_affine hcert hk hr hβ0 hβ1
  exact ne_of_gt (lt_of_lt_of_le hmin hbound)

end Math
