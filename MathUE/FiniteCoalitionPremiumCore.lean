import MathUE.FiniteCoalitionSupportPeelingOrder

/-! # Greatest finite coalition premium core

The relation is abstract. Reward nonnegativity enters only in game adapters.
-/

namespace MathUE

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- A nonempty support where each member has a related coalition inside it. -/
def IsFiniteCoalitionPremiumTrap
    (positive : ι → Finset ι → Prop) (active : Finset ι) : Prop :=
  active.Nonempty ∧ ∀ player ∈ active,
    ∃ coalition ⊆ active, player ∈ coalition ∧ positive player coalition

/-- The union of all finite premium traps. -/
noncomputable def finiteCoalitionPremiumCore
    (positive : ι → Finset ι → Prop) : Finset ι := by
  classical
  exact Finset.univ.filter fun player =>
    ∃ active, IsFiniteCoalitionPremiumTrap positive active ∧ player ∈ active

omit [DecidableEq ι] in
theorem mem_finiteCoalitionPremiumCore_iff
    (positive : ι → Finset ι → Prop) (player : ι) :
    player ∈ finiteCoalitionPremiumCore positive ↔
      ∃ active, IsFiniteCoalitionPremiumTrap positive active ∧ player ∈ active := by
  classical
  simp [finiteCoalitionPremiumCore]

omit [Fintype ι] in
theorem IsFiniteCoalitionPremiumTrap.union
    {positive : ι → Finset ι → Prop} {first second : Finset ι}
    (hfirst : IsFiniteCoalitionPremiumTrap positive first)
    (hsecond : IsFiniteCoalitionPremiumTrap positive second) :
    IsFiniteCoalitionPremiumTrap positive (first ∪ second) := by
  refine ⟨hfirst.1.mono Finset.subset_union_left, ?_⟩
  intro player hplayer
  rcases Finset.mem_union.mp hplayer with hplayer | hplayer
  · obtain ⟨coalition, hsubset, hmember, hpositive⟩ := hfirst.2 player hplayer
    exact ⟨coalition, hsubset.trans Finset.subset_union_left, hmember, hpositive⟩
  · obtain ⟨coalition, hsubset, hmember, hpositive⟩ := hsecond.2 player hplayer
    exact ⟨coalition, hsubset.trans Finset.subset_union_right, hmember, hpositive⟩

omit [DecidableEq ι] in
theorem IsFiniteCoalitionPremiumTrap.subset_core
    {positive : ι → Finset ι → Prop} {active : Finset ι}
    (hactive : IsFiniteCoalitionPremiumTrap positive active) :
    active ⊆ finiteCoalitionPremiumCore positive := by
  intro player hplayer
  exact (mem_finiteCoalitionPremiumCore_iff positive player).mpr
    ⟨active, hactive, hplayer⟩

omit [DecidableEq ι] in
theorem isFiniteCoalitionPremiumTrap_core
    (positive : ι → Finset ι → Prop)
    (hcore : (finiteCoalitionPremiumCore positive).Nonempty) :
    IsFiniteCoalitionPremiumTrap positive (finiteCoalitionPremiumCore positive) := by
  refine ⟨hcore, ?_⟩
  intro player hplayer
  obtain ⟨active, hactive, hmember⟩ :=
    (mem_finiteCoalitionPremiumCore_iff positive player).mp hplayer
  obtain ⟨coalition, hsubset, hmember, hpositive⟩ := hactive.2 player hmember
  exact ⟨coalition, hsubset.trans hactive.subset_core, hmember, hpositive⟩

omit [Fintype ι] [DecidableEq ι] in
theorem not_isFiniteCoalitionPremiumTrap_iff
    (positive : ι → Finset ι → Prop) (active : Finset ι)
    (hactive : active.Nonempty) :
    ¬IsFiniteCoalitionPremiumTrap positive active ↔
      ∃ player ∈ active, ∀ coalition : Finset ι,
        coalition ⊆ active → player ∈ coalition → ¬positive player coalition := by
  classical
  simp only [IsFiniteCoalitionPremiumTrap, hactive, true_and]
  push Not
  rfl

omit [DecidableEq ι] in
theorem finiteCoalitionPremiumCore_eq_empty_iff
    (positive : ι → Finset ι → Prop) :
    finiteCoalitionPremiumCore positive = ∅ ↔
      HasFiniteCoalitionSupportPeeling positive := by
  classical
  constructor
  · intro hempty active hactive
    apply (not_isFiniteCoalitionPremiumTrap_iff positive active hactive).mp
    intro htrap
    obtain ⟨player, hplayer⟩ := hactive
    have := htrap.subset_core hplayer
    simp [hempty] at this
  · intro hpeel
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro player hplayer
    obtain ⟨active, htrap, _hmember⟩ :=
      (mem_finiteCoalitionPremiumCore_iff positive player).mp hplayer
    obtain ⟨chosen, hchosen, hflat⟩ := hpeel active htrap.1
    obtain ⟨coalition, hsubset, hmember, hpositive⟩ := htrap.2 chosen hchosen
    exact hflat coalition hsubset hmember hpositive

omit [Fintype ι] [DecidableEq ι] in
theorem not_isFiniteCoalitionPremiumTrap_singleton
    (positive : ι → Finset ι → Prop)
    (hsingleton : ∀ player, ¬positive player {player}) (player : ι) :
    ¬IsFiniteCoalitionPremiumTrap positive {player} := by
  intro htrap
  obtain ⟨coalition, hsubset, hmember, hpositive⟩ := htrap.2 player (by simp)
  have heq : coalition = {player} :=
    Finset.Subset.antisymm hsubset (Finset.singleton_subset_iff.mpr hmember)
  exact hsingleton player (heq ▸ hpositive)

omit [Fintype ι] in
theorem IsFiniteCoalitionPremiumTrap.insert_of_positive
    {positive : ι → Finset ι → Prop} {active coalition : Finset ι}
    (htrap : IsFiniteCoalitionPremiumTrap positive active) (player : ι)
    (hsubset : coalition ⊆ insert player active) (hmember : player ∈ coalition)
    (hpositive : positive player coalition) :
    IsFiniteCoalitionPremiumTrap positive (insert player active) := by
  refine ⟨Finset.insert_nonempty player active, ?_⟩
  intro other hother
  rcases Finset.mem_insert.mp hother with rfl | hother
  · exact ⟨coalition, hsubset, hmember, hpositive⟩
  · obtain ⟨witness, hwitness, hmember, hpositive⟩ := htrap.2 other hother
    exact ⟨witness, hwitness.trans (Finset.subset_insert player active),
      hmember, hpositive⟩

theorem not_positive_on_core_insert
    (positive : ι → Finset ι → Prop)
    (hcore : (finiteCoalitionPremiumCore positive).Nonempty)
    (player : ι) (houtside : player ∉ finiteCoalitionPremiumCore positive)
    (coalition : Finset ι)
    (hsubset : coalition ⊆ insert player (finiteCoalitionPremiumCore positive))
    (hmember : player ∈ coalition) : ¬positive player coalition := by
  intro hpositive
  have htrap := (isFiniteCoalitionPremiumTrap_core positive hcore).insert_of_positive
    player hsubset hmember hpositive
  exact houtside (htrap.subset_core (Finset.mem_insert_self player _))

omit [Fintype ι] in
theorem IsFiniteCoalitionPremiumTrap.eq_pair_of_subset
    {positive : ι → Finset ι → Prop}
    (hsingleton : ∀ player, ¬positive player {player})
    {active : Finset ι} (htrap : IsFiniteCoalitionPremiumTrap positive active)
    (first second : ι) (hsubset : active ⊆ {first, second}) :
    active = {first, second} := by
  have member : ∀ left right : ι, active ⊆ {left, right} → left ∈ active := by
    intro left right hsub
    by_contra hleft
    have hsingle : active ⊆ {right} := by
      intro player hplayer
      have hpair := hsub hplayer
      simp only [Finset.mem_insert, Finset.mem_singleton] at hpair ⊢
      exact hpair.resolve_left (fun heq => hleft (heq ▸ hplayer))
    obtain ⟨player, hplayer⟩ := htrap.1
    have hright : right ∈ active := by
      have heq : player = right := Finset.mem_singleton.mp (hsingle hplayer)
      exact heq ▸ hplayer
    have heq : active = {right} :=
      Finset.Subset.antisymm hsingle (Finset.singleton_subset_iff.mpr hright)
    exact not_isFiniteCoalitionPremiumTrap_singleton positive hsingleton right
      (heq ▸ htrap)
  apply Finset.Subset.antisymm hsubset
  intro player hplayer
  simp only [Finset.mem_insert, Finset.mem_singleton] at hplayer
  rcases hplayer with heq | heq
  · exact heq.symm ▸ member first second hsubset
  · have hsecond := member second first (by
      simpa [Finset.pair_comm] using hsubset)
    exact heq.symm ▸ hsecond

theorem not_isFiniteCoalitionPremiumTrap_of_pair_core_ne
    (positive : ι → Finset ι → Prop)
    (hsingleton : ∀ player, ¬positive player {player})
    (first second : ι) (hcore : finiteCoalitionPremiumCore positive = {first, second})
    (active : Finset ι) (hne : active ≠ finiteCoalitionPremiumCore positive) :
    ¬IsFiniteCoalitionPremiumTrap positive active := by
  intro htrap
  apply hne
  rw [hcore]
  exact htrap.eq_pair_of_subset hsingleton first second (by
    simpa [hcore] using htrap.subset_core)

end MathUE
