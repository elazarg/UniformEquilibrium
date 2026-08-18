/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Tactic.Linarith
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Order.Basic

/-!
# A finite maximum is nonexpansive, and preserves nullity

A real quantity aggregated as the maximum over a nonempty finite index set is
a `Finset.sup'`.  Two facts about that aggregation are needed wherever a
coordinatewise estimate has to be promoted to an estimate on the aggregate.

* `abs_sup'_sub_sup'_le`: two maxima differ by at most the maximum of the
  coordinatewise differences, with `abs_sup'_sub_sup'_le_const` the
  uniform-constant form.  A coordinatewise perturbation bound therefore
  transfers to the maximum with no loss.
* `tendsto_sup'_nhds_zero`: a finite family of nonnegative null nets has null
  maximum, via `sup'_le_sum`.  Finiteness of the index set is what makes this
  work; the statement fails for infinite families.

These are order and topology facts about real-valued families on a finite
index set.  Nothing here interprets the index set as players, the values as
payoffs or errors, or the maximum as an exploitability.
-/

namespace Math.Finset

open Filter
open scoped Topology

variable {Index : Type*} {indices : Finset Index}

/-- **A finite maximum is nonexpansive.**  Two `sup'`s over the same index set
differ by at most the `sup'` of any pointwise bound on the coordinatewise
differences. -/
theorem abs_sup'_sub_sup'_le
    (hindices : indices.Nonempty) (first second bound : Index → ℝ)
    (hbound : ∀ index ∈ indices, |first index - second index| ≤ bound index) :
    |indices.sup' hindices first - indices.sup' hindices second| ≤
      indices.sup' hindices bound := by
  have key : ∀ u v : Index → ℝ,
      (∀ index ∈ indices, |u index - v index| ≤ bound index) →
      indices.sup' hindices u ≤
        indices.sup' hindices v + indices.sup' hindices bound := by
    intro u v huv
    refine Finset.sup'_le hindices u fun index hindex => ?_
    have hdiff : u index - v index ≤ bound index :=
      (le_abs_self _).trans (huv index hindex)
    have hv := Finset.le_sup' v hindex
    have hb := Finset.le_sup' bound hindex
    linarith
  have hfs := key first second hbound
  have hsf := key second first fun index hindex => by
    rw [abs_sub_comm]
    exact hbound index hindex
  rw [abs_sub_le_iff]
  exact ⟨by linarith, by linarith⟩

/-- Uniform-constant form of nonexpansiveness. -/
theorem abs_sup'_sub_sup'_le_const
    (hindices : indices.Nonempty) (first second : Index → ℝ) {bound : ℝ}
    (hbound : ∀ index ∈ indices, |first index - second index| ≤ bound) :
    |indices.sup' hindices first - indices.sup' hindices second| ≤ bound := by
  have haggregate :=
    abs_sup'_sub_sup'_le hindices first second (fun _ => bound) hbound
  rwa [Finset.sup'_const] at haggregate

/-- A finite maximum of nonnegative values is below their sum. -/
theorem sup'_le_sum
    (hindices : indices.Nonempty) (value : Index → ℝ)
    (hnonneg : ∀ index ∈ indices, 0 ≤ value index) :
    indices.sup' hindices value ≤ ∑ index ∈ indices, value index :=
  Finset.sup'_le hindices value fun _index hindex =>
    Finset.single_le_sum hnonneg hindex

/-- **A finite maximum of null nets is null.**  Finiteness of the index set is
essential: the maximum is squeezed between zero and the sum, and only a finite
sum of null nets is null. -/
theorem tendsto_sup'_nhds_zero {Point : Type*} {source : Filter Point}
    (hindices : indices.Nonempty) (value : Index → Point → ℝ)
    (hnonneg : ∀ index ∈ indices, ∀ point, 0 ≤ value index point)
    (hnull : ∀ index ∈ indices, Tendsto (value index) source (𝓝 0)) :
    Tendsto (fun point => indices.sup' hindices fun index => value index point)
      source (𝓝 0) := by
  have hsum : Tendsto (fun point => ∑ index ∈ indices, value index point)
      source (𝓝 0) := by
    have haggregate := tendsto_finsetSum indices fun index hindex =>
      hnull index hindex
    simpa using haggregate
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum
    (fun point => ?_) (fun point => ?_)
  · obtain ⟨index, hindex⟩ := hindices
    exact (hnonneg index hindex point).trans
      (Finset.le_sup' (fun index => value index point) hindex)
  · exact sup'_le_sum hindices _ fun index hindex => hnonneg index hindex point

end Math.Finset
