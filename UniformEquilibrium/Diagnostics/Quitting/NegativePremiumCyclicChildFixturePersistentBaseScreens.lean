import UniformEquilibrium.Quitting.Examples.NegativePremiumCyclicChildFixturePunishmentRoots
import UniformEquilibrium.Quitting.Root.ForcedQuitEndpointStability
import UniformEquilibrium.Diagnostics.Quitting.Collision.Toggles.LargePersistentBaseActualAdapter

/-! # Every persistent-base screen of the negative-premium fixture

Every induced Nash law at every nonempty base and disjoint free carrier has
strictly positive concrete excess. The compact induced-Nash alternative gives
a common positive gap for each carrier choice. Missing outsiders retain their
Continue inequalities; partial free carriers are not replaced by complements.
These are failures of the named source screens, not uniform-equilibrium exclusion.
-/

noncomputable section

namespace GameTheory.NegativePremiumCyclicChild.Fixtures

private theorem largeCertificate_rootNash {base free : Finset Player}
    {root : Player → PMF Bool}
    (certificate : QuittingPersistentBaseCertificate survivorReward base free root) :
    IsεQuittingRootNash survivorReward (fun _ => lower) 0 root := by
  apply (isZeroQuittingRootEndpointNash_iff_isZeroQuittingRootNash
    survivorReward (fun _ => lower) root).mp
  intro who
  obtain ⟨opponent, hopponent, hne⟩ := certificate.exists_base_opponent who
  rw [quittingRootEndpointDifference_eq_zeroTail_of_sureOpponent
    survivorReward (fun _ => lower) root hne.symm (certificate.base_quits _ hopponent)]
  have hconditions := certificate.endpointNash who
  rw [certificate.endpointDifference_actual_eq_zeroTail who] at hconditions
  exact hconditions

/-- Every induced Nash law fails the nonpositive large-base screen, including partial free sets. -/
theorem largeBaseExcess_pos_of_inducedNash (base free : Finset Player)
    (hdisjoint : Disjoint base free) (hbase : 2 ≤ base.card)
    (point : mixedPolytope (quittingBinaryForm free).sig)
    (hpoint : point ∈ quittingPersistentBaseNashSet survivorReward base free) :
    0 < quittingPersistentLargeBaseExcess survivorReward base free point := by
  by_contra hnot
  obtain ⟨hleave, hjoin⟩ :=
    (quittingPersistentLargeBaseExcess_nonpos_iff survivorReward base free point).mp
      (not_lt.mp hnot)
  obtain ⟨certificate⟩ := nonempty_quittingPersistentBaseCertificate_of_inducedNash
    survivorReward base free hdisjoint hbase point hpoint hleave hjoin
  obtain ⟨owner, howner⟩ := certificate.base_nonempty
  have hsure : hazardOfRoot (quittingPersistentBaseRoot base free point) owner = 1 := by
    simp [hazardOfRoot, certificate.base_quits owner howner]
  exact not_rootNash_of_sureCoordinate _ owner hsure (largeCertificate_rootNash certificate)

/-- Every singleton-base induced Nash law fails the actual-punishment screen. -/
theorem singletonBaseExcess_pos_of_inducedNash (owner : Player) (free : Finset Player)
    (howner : owner ∉ free)
    (point : mixedPolytope (quittingBinaryForm free).sig)
    (hpoint : point ∈ quittingPersistentBaseNashSet survivorReward {owner} free) :
    0 < quittingSingletonBaseExcess survivorReward owner free point := by
  by_contra hnot
  obtain ⟨hfloor, hjoin⟩ :=
    (quittingSingletonBaseExcess_nonpos_iff survivorReward owner free point).mp
      (not_lt.mp hnot)
  obtain ⟨certificate⟩ := nonempty_quittingSingletonBaseCertificate_of_inducedNash
    survivorReward owner free howner point hpoint hfloor hjoin
  let root := quittingPersistentBaseRoot {owner} free point
  have hownerQuit : root owner = PMF.pure true := certificate.owner_quits
  have hownerGap : 0 ≤ quittingRootEndpointDifference survivorReward
      (fun _ => lower) root owner := by
    rw [quittingSingletonBaseOwnerFloorExcess_eq_neg_endpoint_of_sureQuit
      survivorReward owner root certificate.owner_quits, punishmentValue_eq_lower] at hfloor
    linarith
  have hnash : IsεQuittingRootNash survivorReward (fun _ => lower) 0 root := by
    apply (isZeroQuittingRootEndpointNash_iff_isZeroQuittingRootNash
      survivorReward (fun _ => lower) root).mp
    intro who
    by_cases hwho : who = owner
    · subst who
      simpa [hownerQuit] using hownerGap
    · rw [quittingRootEndpointDifference_eq_zeroTail_of_sureOpponent
        survivorReward (fun _ => lower) root hwho certificate.owner_quits]
      simpa only [neg_zero] using certificate.other_endpointNash who hwho
  have hsure : hazardOfRoot root owner = 1 := by
    simp [hazardOfRoot, hownerQuit]
  exact not_rootNash_of_sureCoordinate root owner hsure hnash

/-- The large-base Nash carrier has one positive gap before every induced Nash law. -/
theorem exists_largeBase_uniform_gap (base free : Finset Player)
    (hdisjoint : Disjoint base free) (hbase : 2 ≤ base.card) :
    ∃ gamma : ℝ, 0 < gamma ∧
      ∀ point ∈ quittingPersistentBaseNashSet survivorReward base free,
        gamma ≤ quittingPersistentLargeBaseExcess survivorReward base free point := by
  rcases exists_persistentBaseNash_nonpos_or_pos_gap survivorReward base free
      (quittingPersistentLargeBaseExcess survivorReward base free)
      (continuous_quittingPersistentLargeBaseExcess survivorReward base free) with
    haccepted | hgap
  · obtain ⟨point, hpoint, hnonpos⟩ := haccepted
    exact ((not_le_of_gt
      (largeBaseExcess_pos_of_inducedNash base free hdisjoint hbase point hpoint)) hnonpos).elim
  · exact hgap

/-- The singleton Nash carrier has one positive actual-punishment gap. -/
theorem exists_singletonBase_uniform_gap (owner : Player) (free : Finset Player)
    (howner : owner ∉ free) :
    ∃ gamma : ℝ, 0 < gamma ∧
      ∀ point ∈ quittingPersistentBaseNashSet survivorReward {owner} free,
        gamma ≤ quittingSingletonBaseExcess survivorReward owner free point := by
  rcases exists_persistentBaseNash_nonpos_or_pos_gap survivorReward {owner} free
      (quittingSingletonBaseExcess survivorReward owner free)
      (continuous_quittingSingletonBaseExcess survivorReward owner free) with
    haccepted | hgap
  · obtain ⟨point, hpoint, hnonpos⟩ := haccepted
    exact ((not_le_of_gt
      (singletonBaseExcess_pos_of_inducedNash owner free howner point hpoint)) hnonpos).elim
  · exact hgap

/-- Every nonempty base and every disjoint free carrier has the appropriate positive gap. -/
theorem every_nonempty_base_has_positive_gap (base free : Finset Player)
    (hbase : base.Nonempty) (hdisjoint : Disjoint base free) :
    (2 ≤ base.card ∧ ∃ gamma : ℝ, 0 < gamma ∧
      ∀ point ∈ quittingPersistentBaseNashSet survivorReward base free,
        gamma ≤ quittingPersistentLargeBaseExcess survivorReward base free point) ∨
    (∃ owner : Player, base = {owner} ∧ ∃ gamma : ℝ, 0 < gamma ∧
      ∀ point ∈ quittingPersistentBaseNashSet survivorReward base free,
        gamma ≤ quittingSingletonBaseExcess survivorReward owner free point) := by
  by_cases hlarge : 2 ≤ base.card
  · exact Or.inl ⟨hlarge, exists_largeBase_uniform_gap base free hdisjoint hlarge⟩
  · have hcard : base.card = 1 := by
      have hpositive := Finset.card_pos.mpr hbase
      omega
    obtain ⟨owner, heq⟩ := Finset.card_eq_one.mp hcard
    have howner : owner ∉ free := by
      intro hmem
      exact Finset.disjoint_left.mp hdisjoint (heq.symm ▸ Finset.mem_singleton_self owner) hmem
    refine Or.inr ⟨owner, heq, ?_⟩
    rw [heq]
    exact exists_singletonBase_uniform_gap owner free howner

end GameTheory.NegativePremiumCyclicChild.Fixtures
