/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.BooleanAlgebra
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import MathUE.Finset.ProdLtOne

/-!
# Coalition mass over independent Bernoulli marginals

For a finite index type `ι` and a family `x : ι → ℝ` of per-coordinate "acting"
probabilities, this file records the two elementary identities behind the
coalition decomposition of a product of independent Bernoulli trials, together
with their telescoping consequence along a sequence of rows.

* `continueMass x` is the probability that every coordinate stays put.
* `coalitionMass x J` is the probability that exactly the coordinates in `J`
  act and every other coordinate stays put.
* `survivalMass x t` is the probability that every row before stage `t` leaves
  every coordinate unacted upon.
* `absorbedMass x t` is the total mass absorbed by some nonempty coalition at
  some stage strictly before `t`.

For a family of probabilities the continuation mass lies in `[0, 1]`, it
vanishes as soon as one coordinate acts for sure, and it is strictly below one
as soon as one coordinate acts with positive probability
(`continueMass_lt_one_of_pos`); equivalently, certain continuation forces every
coordinate to be zero (`eq_zero_of_continueMass_eq_one`). Over a finite
schedule of rows the same witness puts the product of the continuation masses
strictly below one (`prod_continueMass_lt_one_of_pos`).

Neither `sum_coalitionMass_nonempty` nor `sum_survivalMass_mul_sub_continueMass`
below uses `0 ≤ x i` or `x i ≤ 1`: they are algebraic consequences of
`x i + (1 - x i) = 1`, valid for any real family. The bounds are only needed
for the intended reading of `x i` as a probability, and for `absorbedMass` to
be an honest arclength (the accumulated-mass path is `1`-Lipschitz in `ℓ¹`
exactly because `absorbedMass_eq_one_sub_survivalMass` holds with no slack).
-/

namespace Math.PMFProduct

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The probability that every coordinate of `x` stays put. -/
def continueMass (x : ι → ℝ) : ℝ := ∏ i, (1 - x i)

omit [DecidableEq ι] in
/-- Continuation mass is nonnegative as soon as no coordinate acts with
probability above one. No lower bound on `x` is needed. -/
theorem continueMass_nonneg {x : ι → ℝ} (h1 : ∀ i, x i ≤ 1) : 0 ≤ continueMass x :=
  Finset.prod_nonneg fun i _ ↦ by linarith [h1 i]

omit [DecidableEq ι] in
/-- Continuation mass is at most one for a family of probabilities. -/
theorem continueMass_le_one {x : ι → ℝ} (h0 : ∀ i, 0 ≤ x i) (h1 : ∀ i, x i ≤ 1) :
    continueMass x ≤ 1 :=
  Finset.prod_le_one (fun i _ ↦ by linarith [h1 i]) (fun i _ ↦ by linarith [h0 i])

omit [DecidableEq ι] in
/-- A coordinate acting for sure annihilates the continuation mass. No bounds
on the other coordinates are needed. -/
theorem continueMass_eq_zero_of_eq_one {x : ι → ℝ} {i : ι} (hi : x i = 1) :
    continueMass x = 0 :=
  Finset.prod_eq_zero (Finset.mem_univ i) (by rw [hi]; ring)

omit [DecidableEq ι] in
/-- **A positive coordinate breaks certain continuation.** One coordinate
acting with positive probability puts the continuation mass strictly below
one. -/
theorem continueMass_lt_one_of_pos {x : ι → ℝ} (h0 : ∀ i, 0 ≤ x i)
    (h1 : ∀ i, x i ≤ 1) {i₀ : ι} (hpos : 0 < x i₀) : continueMass x < 1 :=
  Math.Finset.prod_lt_one_of_mem Finset.univ (fun i ↦ 1 - x i) i₀
    (Finset.mem_univ i₀) (fun i _ _ ↦ by linarith [h1 i]) (fun i _ _ ↦ by linarith [h0 i])
    (by linarith)

omit [DecidableEq ι] in
/-- **Certain continuation forces inaction.** A family of probabilities whose
continuation mass is one is identically zero. -/
theorem eq_zero_of_continueMass_eq_one {x : ι → ℝ} (h0 : ∀ i, 0 ≤ x i)
    (h1 : ∀ i, x i ≤ 1) (hone : continueMass x = 1) (i : ι) : x i = 0 := by
  refine le_antisymm (not_lt.mp fun hpos ↦ ?_) (h0 i)
  exact absurd hone (continueMass_lt_one_of_pos h0 h1 hpos).ne

omit [DecidableEq ι] in
/-- **A positive coordinate at one stage breaks certain continuation over the
whole schedule.** One coordinate acting with positive probability at one stage
puts the product of the continuation masses of an arbitrary finite schedule
strictly below one. -/
theorem prod_continueMass_lt_one_of_pos {Stage : Type*} (stages : Finset Stage)
    {x : Stage → ι → ℝ} (h0 : ∀ s i, 0 ≤ x s i) (h1 : ∀ s i, x s i ≤ 1)
    {s₀ : Stage} (hs₀ : s₀ ∈ stages) {i₀ : ι} (hpos : 0 < x s₀ i₀) :
    (∏ s ∈ stages, continueMass (x s)) < 1 :=
  Math.Finset.prod_lt_one_of_mem stages (fun s ↦ continueMass (x s)) s₀ hs₀
    (fun s _ _ ↦ continueMass_nonneg (h1 s)) (fun s _ _ ↦ continueMass_le_one (h0 s) (h1 s))
    (continueMass_lt_one_of_pos (h0 s₀) (h1 s₀) hpos)

/-- The probability that exactly the coordinates in `J` act, and every
coordinate outside `J` stays put. -/
def coalitionMass (x : ι → ℝ) (J : Finset ι) : ℝ :=
  (∏ i ∈ J, x i) * ∏ i ∈ Jᶜ, (1 - x i)

/-- Coalition mass is nonnegative for Bernoulli parameters. -/
theorem coalitionMass_nonneg (x : ι → ℝ)
    (h0 : ∀ i, 0 ≤ x i) (h1 : ∀ i, x i ≤ 1) (J : Finset ι) :
    0 ≤ coalitionMass x J := by
  unfold coalitionMass
  exact mul_nonneg
    (Finset.prod_nonneg fun i _ => h0 i)
    (Finset.prod_nonneg fun i _ => sub_nonneg.mpr (h1 i))

/-- The coalition mass at the empty coalition is exactly the continuation
mass: nobody acting is the same event as everyone staying put. -/
@[simp] lemma coalitionMass_empty (x : ι → ℝ) :
    coalitionMass x (∅ : Finset ι) = continueMass x := by
  simp [coalitionMass, continueMass]

/-- **Total mass.** The coalition masses of the `2 ^ #ι` coalitions sum to
`1`. This is the binomial expansion of `∏ i, (x i + (1 - x i))`, so it holds
for any real family, not only for probabilities. -/
theorem sum_coalitionMass (x : ι → ℝ) : ∑ J : Finset ι, coalitionMass x J = 1 := by
  have h := Fintype.prod_add x (fun i => 1 - x i)
  have hlhs : (∏ a : ι, (x a + (1 - x a))) = (1 : ℝ) := by
    have hfun : (fun a : ι => x a + (1 - x a)) = (fun _ : ι => (1 : ℝ)) := by
      funext a; ring
    rw [hfun, Finset.prod_const_one]
  rw [hlhs] at h
  simpa [coalitionMass] using h.symm

/-- **Coalition sum.** Summing the coalition mass over every nonempty
coalition recovers exactly the mass not accounted for by universal
continuation. The sum ranges over `Finset.univ.erase ∅`, i.e. exactly the
finsets `J` with `J ≠ ∅`, equivalently `J.Nonempty` by
`Finset.nonempty_iff_ne_empty`. -/
theorem sum_coalitionMass_nonempty (x : ι → ℝ) :
    ∑ J ∈ Finset.univ.erase (∅ : Finset ι), coalitionMass x J = 1 - continueMass x := by
  have hone : ∑ J : Finset ι, coalitionMass x J = 1 := sum_coalitionMass x
  have hsplit :
      coalitionMass x (∅ : Finset ι) +
          ∑ J ∈ Finset.univ.erase (∅ : Finset ι), coalitionMass x J
        = ∑ J : Finset ι, coalitionMass x J :=
    Finset.add_sum_erase Finset.univ (coalitionMass x) (Finset.mem_univ ∅)
  rw [coalitionMass_empty] at hsplit
  linarith

/-- The probability that every row before stage `t` leaves every coordinate
unacted upon. -/
def survivalMass (x : ℕ → ι → ℝ) (t : ℕ) : ℝ :=
  ∏ u ∈ Finset.range t, continueMass (x u)

omit [DecidableEq ι] in
/-- Survival through stage `0` is certain. -/
@[simp] lemma survivalMass_zero (x : ℕ → ι → ℝ) : survivalMass x 0 = 1 := by
  simp [survivalMass]

omit [DecidableEq ι] in
/-- Survival advances by one row's continuation mass at each stage. -/
lemma survivalMass_succ (x : ℕ → ι → ℝ) (t : ℕ) :
    survivalMass x (t + 1) = survivalMass x t * continueMass (x t) := by
  simp [survivalMass, Finset.prod_range_succ]

omit [DecidableEq ι] in
/-- **Survival telescope.** The survival-weighted absorption at each stage
before `t` telescopes: each summand is `survivalMass x u - survivalMass x (u+1)`,
so the sum collapses to the drop from certainty at stage `0` down to
`survivalMass x t`. -/
theorem sum_survivalMass_mul_sub_continueMass (x : ℕ → ι → ℝ) (t : ℕ) :
    ∑ u ∈ Finset.range t, survivalMass x u * (1 - continueMass (x u))
      = 1 - survivalMass x t := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [Finset.sum_range_succ, ih, survivalMass_succ]
    ring

/-- Total mass absorbed by some nonempty coalition at some stage strictly
before `t`. -/
def absorbedMass (x : ℕ → ι → ℝ) (t : ℕ) : ℝ :=
  ∑ u ∈ Finset.range t, ∑ J ∈ Finset.univ.erase (∅ : Finset ι),
    survivalMass x u * coalitionMass (x u) J

/-- **Arclength corollary.** The total mass absorbed by some nonempty
coalition at some stage before `t` equals `1 - survivalMass x t`, combining
the coalition sum (Lemma 1) row by row with the survival telescope (Lemma 2).
This is the identity making accumulated mass an exact arclength: the path
`t ↦ absorbedMass x t` advances by exactly the survival-weighted coalition
split at each stage, so it is `1`-Lipschitz in `ℓ¹`. -/
theorem absorbedMass_eq_one_sub_survivalMass (x : ℕ → ι → ℝ) (t : ℕ) :
    absorbedMass x t = 1 - survivalMass x t := by
  unfold absorbedMass
  have hstep : ∀ u : ℕ,
      ∑ J ∈ Finset.univ.erase (∅ : Finset ι), survivalMass x u * coalitionMass (x u) J
        = survivalMass x u * (1 - continueMass (x u)) := by
    intro u
    rw [← Finset.mul_sum, sum_coalitionMass_nonempty]
  simp_rw [hstep]
  exact sum_survivalMass_mul_sub_continueMass x t

end Math.PMFProduct
