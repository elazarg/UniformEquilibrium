import Mathlib.Topology.MetricSpace.Closeds
import Mathlib.Topology.Semicontinuity.Hemicontinuity

/-! # Incidence and selections for converging nonempty compact sets

The Vietoris open-subset and open-hit characterizations give the upper and
lower hemicontinuity hypotheses of Mathlib's existing limit theorems.
Nonemptiness fills the exceptional indices of a convergent selection, so its
membership guarantee holds at every index, not only eventually.
-/

noncomputable section

open Set Filter TopologicalSpace
open scoped Topology

namespace Math.Topology

variable {X : Type*} [MetricSpace X]

private theorem upperHemicontinuous_nonemptyCompacts_coe :
    UpperHemicontinuous (fun K : NonemptyCompacts X => (K : Set X)) := by
  apply upperHemicontinuous_iff_forall_isOpen.mpr
  intro K U hU hKU
  exact (NonemptyCompacts.isOpen_subsets_of_isOpen hU).mem_nhds hKU

private theorem lowerHemicontinuous_nonemptyCompacts_coe :
    LowerHemicontinuous (fun K : NonemptyCompacts X => (K : Set X)) := by
  apply lowerHemicontinuous_iff_isOpen_inter_nonempty.mpr
  intro U hU
  exact NonemptyCompacts.isOpen_inter_nonempty_of_isOpen hU

/-- Limits of eventually incident points belong to the limiting nonempty compact set. -/
theorem mem_limit_of_nonemptyCompacts_tendsto {sets : ℕ → NonemptyCompacts X}
    {limit : NonemptyCompacts X} {points : ℕ → X} {point : X}
    (hsets : Tendsto sets atTop (𝓝 limit)) (hpoints : Tendsto points atTop (𝓝 point))
    (hmem : ∀ᶠ k in atTop, points k ∈ sets k) : point ∈ limit :=
  (upperHemicontinuous_nonemptyCompacts_coe.upperHemicontinuousAt limit).mem_of_tendsto
    limit.isCompact.isClosed hsets hmem.frequently hpoints

/-- Every limit point has a convergent same-index selection with membership at every index. -/
theorem exists_mem_tendsto_of_nonemptyCompacts_tendsto
    {sets : ℕ → NonemptyCompacts X} {limit : NonemptyCompacts X}
    (hsets : Tendsto sets atTop (𝓝 limit)) {point : X} (hpoint : point ∈ limit) :
    ∃ points : ℕ → X, (∀ k, points k ∈ sets k) ∧ Tendsto points atTop (𝓝 point) := by
  classical
  have hlower := lowerHemicontinuous_nonemptyCompacts_coe.lowerHemicontinuousAt limit
  obtain ⟨selected, hmem, hselected⟩ := hlower.exists_seq_tendsto hsets hpoint
  let points (k : ℕ) :=
    if selected k ∈ (sets k : Set X) then selected k else (sets k).nonempty.choose
  refine ⟨points, ?_, hselected.congr' ?_⟩
  · intro k
    change points k ∈ (sets k : Set X)
    by_cases hk : selected k ∈ (sets k : Set X)
    · simpa only [points, ite_eq_left hk] using hk
    · simpa only [points, ite_eq_right hk] using (sets k).nonempty.choose_spec
  · filter_upwards [hmem] with k hk
    change selected k ∈ (sets k : Set X) at hk
    simp only [points, ite_eq_left hk]

end Math.Topology
