/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring

/-!
# Bernoulli weights over the powerset of a finset

For a family `x` of per-coordinate acting probabilities and a finset `A`, the
*relative Bernoulli weight* of `J ⊆ A` is the probability that exactly the
coordinates in `J` act and every other coordinate of `A` stays put.  Summed
over the powerset of `A` these weights total one.

`MathUE/PMFProduct/CoalitionMass.lean` records the same identity relative to
the whole index type, where the complement is `Jᶜ`.  The statement here is
relative to an arbitrary `A`, which is what a computation conditioned on one
distinguished coordinate — summing over the subsets of the *other*
coordinates — actually reads.

Like the whole-type version this is the binomial expansion of
`∏ j ∈ A, (x j + (1 - x j))` and needs no bounds on `x`: it is an algebraic
consequence of `x j + (1 - x j) = 1`, valid for any family in a commutative
ring.

## Main definitions

* `Math.Finset.bernoulliWeight` — the relative weight of a subset

## Main results

* `Math.Finset.sum_bernoulliWeight` — the weights of the powerset sum to one
* `Math.Finset.bernoulliWeight_empty_const` and
  `Math.Finset.bernoulliWeight_singleton_const` — the two weights a common
  rate assigns to the empty subset and to a singleton
-/

namespace Math.Finset

variable {ι : Type*} [DecidableEq ι] {R : Type*} [CommRing R]

/-- The probability that exactly the coordinates in `J` act and every other
coordinate of `A` stays put. -/
def bernoulliWeight (x : ι → R) (A J : Finset ι) : R :=
  (∏ j ∈ J, x j) * ∏ j ∈ A \ J, (1 - x j)

/-- **Total mass over a finset.**  The relative Bernoulli weights of the
subsets of `A` sum to one. -/
theorem sum_bernoulliWeight (x : ι → R) (A : Finset ι) :
    ∑ J ∈ A.powerset, bernoulliWeight x A J = 1 := by
  have hexpand := Finset.prod_add (fun j ↦ x j) (fun j ↦ 1 - x j) A
  have hone : (∏ j ∈ A, (x j + (1 - x j))) = 1 :=
    Finset.prod_eq_one fun j _ ↦ by ring
  rw [hone] at hexpand
  simp only [bernoulliWeight]
  exact hexpand.symm

/-- At a common rate the empty subset carries the whole survival product. -/
theorem bernoulliWeight_empty_const (p : R) (A : Finset ι) :
    bernoulliWeight (fun _ ↦ p) A ∅ = (1 - p) ^ A.card := by
  rw [bernoulliWeight, Finset.prod_empty, one_mul, Finset.sdiff_empty,
    Finset.prod_const]

/-- At a common rate a singleton of `A` carries one acting factor and the
survival of the rest. -/
theorem bernoulliWeight_singleton_const (p : R) {A : Finset ι} {j : ι} (hj : j ∈ A) :
    bernoulliWeight (fun _ ↦ p) A {j} = p * (1 - p) ^ (A.card - 1) := by
  have hcard : (A \ {j}).card = A.card - 1 := by
    rw [Finset.card_sdiff, Finset.inter_eq_left.mpr (Finset.singleton_subset_iff.mpr hj),
      Finset.card_singleton]
  rw [bernoulliWeight, Finset.prod_singleton, Finset.prod_const, hcard]

end Math.Finset
