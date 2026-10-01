import Mathlib.Topology.Separation.Profinite

/-!
# Separating closed sets that meet no common connected component

This is the compact Hausdorff component-separation lemma, obtained from the canonical
totally disconnected component quotient and its clopen separation theorem.
-/

namespace Math

open Set

/-- Two closed sets in a compact Hausdorff space which meet no common connected component
are separated by a clopen set. Empty sets and empty spaces are allowed. -/
theorem exists_isClopen_separator_of_no_common_component
    {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    {A B : Set X} (hA : IsClosed A) (hB : IsClosed B)
    (hcomponent : ∀ a ∈ A, ∀ b ∈ B, b ∉ connectedComponent a) :
    ∃ U : Set X, IsClopen U ∧ A ⊆ U ∧ Disjoint U B := by
  let q : X → ConnectedComponents X := ConnectedComponents.mk
  have hq : Continuous q := ConnectedComponents.continuous_coe
  have hAB : Disjoint (q '' A) (q '' B) := by
    apply Set.disjoint_left.mpr
    rintro _ ⟨a, ha, rfl⟩ ⟨b, hb, hba⟩
    exact hcomponent a ha b hb (ConnectedComponents.coe_eq_coe'.mp hba)
  obtain ⟨V, hV, hAV, hVB⟩ := exists_clopen_of_closed_subset_open
    (hA.isCompact.image hq).isClosed (hB.isCompact.image hq).isClosed.isOpen_compl
    (Set.disjoint_left.mp hAB)
  refine ⟨q ⁻¹' V, hV.preimage hq, ?_, ?_⟩
  · intro a ha
    exact hAV ⟨a, ha, rfl⟩
  · apply Set.disjoint_left.mpr
    intro b hbU hb
    exact hVB hbU ⟨b, hb, rfl⟩

end Math
