import Mathlib

/-!
# Continuation compatibility from a common lattice orientation

This standalone experiment proves the order-theoretic gluing mechanism from
`ideas/CoalitionSecurityWelfareAssembly.md`.

Playerwise feasibility normally does not imply coupled feasibility.  It does
when the ambient continuation domain has finite joins and every player's
feasible set is upward closed in the same order: join the separate witnesses.
The dual statement uses finite meets and downward-closed feasible sets.
-/

namespace Research.ContinuationLatticeGluing

open Set

/-- Membership survives moving upward in the ambient order. -/
def IsUpwardClosed {α : Type*} [LE α] (set : Set α) : Prop :=
  ∀ ⦃lower⦄, lower ∈ set → ∀ ⦃upper⦄, lower ≤ upper → upper ∈ set

/-- Membership survives moving downward in the ambient order. -/
def IsDownwardClosed {α : Type*} [LE α] (set : Set α) : Prop :=
  ∀ ⦃upper⦄, upper ∈ set → ∀ ⦃lower⦄, lower ≤ upper → lower ∈ set

/-- A finite family of nonempty feasible sets has a common point when all
sets are upward closed in one join-semilattice order. -/
theorem exists_common_of_nonempty_of_upwardClosed
    {ι α : Type*} [Finite ι] [Nonempty ι]
    [SemilatticeSup α] [OrderBot α]
    (feasible : ι → Set α)
    (nonempty : ∀ i, (feasible i).Nonempty)
    (upward : ∀ i, IsUpwardClosed (feasible i)) :
    ∃ common, ∀ i, common ∈ feasible i := by
  classical
  letI := Fintype.ofFinite ι
  choose witness witness_mem using nonempty
  let common : α := Finset.univ.sup witness
  refine ⟨common, fun i => upward i (witness_mem i) ?_⟩
  exact Finset.le_sup (s := Finset.univ) (f := witness)
    (Finset.mem_univ i)

/-- Dual gluing by the meet of separately feasible witnesses. -/
theorem exists_common_of_nonempty_of_downwardClosed
    {ι α : Type*} [Finite ι] [Nonempty ι]
    [SemilatticeInf α] [OrderTop α]
    (feasible : ι → Set α)
    (nonempty : ∀ i, (feasible i).Nonempty)
    (downward : ∀ i, IsDownwardClosed (feasible i)) :
    ∃ common, ∀ i, common ∈ feasible i := by
  classical
  letI := Fintype.ofFinite ι
  choose witness witness_mem using nonempty
  let common : α := Finset.univ.inf witness
  refine ⟨common, fun i => downward i (witness_mem i) ?_⟩
  exact Finset.inf_le (s := Finset.univ) (f := witness)
    (Finset.mem_univ i)

/-- Coordinatewise continuation-vector specialization.  The lattice instance
on functions takes joins pointwise, so the common witness is the coordinatewise
maximum of the separate player witnesses. -/
theorem exists_common_continuation_of_upwardClosed
    {ι κ : Type*} [Finite ι] [Nonempty ι]
    (feasible : ι → Set (κ → WithBot ℝ))
    (nonempty : ∀ i, (feasible i).Nonempty)
    (upward : ∀ i, IsUpwardClosed (feasible i)) :
    ∃ common, ∀ i, common ∈ feasible i :=
  exists_common_of_nonempty_of_upwardClosed feasible nonempty upward

/-- Quantitative approximate version: if every constraint's violation is
antitone, taking the join cannot increase any player's violation. -/
theorem violation_join_le
    {α : Type*} [SemilatticeSup α]
    (violation : α → ℝ)
    (antitone : Antitone violation)
    (left right : α) :
    violation (left ⊔ right) ≤ min (violation left) (violation right) := by
  apply le_min
  · exact antitone le_sup_left
  · exact antitone le_sup_right

end Research.ContinuationLatticeGluing
