import UniformEquilibrium.Quitting.Stationary.GuardedCrossedResponseWeakHalfPerturbation

/-! # Weak four-player lower rankings become strict under the literal perturbation -/

noncomputable section

namespace GameTheory

/-- The weak form of packet (L), as finite comparisons of actual reward rows. -/
def QuittingCrossedWeakLowerRanking
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (recipient partner : Fin 4) : Prop :=
  ∀ own other : Finset (Fin 4),
    own ⊆ quittingCrossedRawOutsiders recipient partner →
    other ⊆ quittingCrossedRawOutsiders recipient partner →
    other.Nonempty →
    weightOfReward reward other recipient ≤
      weightOfReward reward (insert recipient own) recipient

private theorem weakHalf_outsiders_first :
    quittingCrossedRawOutsiders (0 : Fin 4) 1 = {2, 3} := by decide

private theorem weakHalf_outsiders_second :
    quittingCrossedRawOutsiders (1 : Fin 4) 0 = {2, 3} := by decide

private theorem weakHalf_external_subset_cases
    (other : Finset (Fin 4)) (hsubset : other ⊆ ({2, 3} : Finset (Fin 4)))
    (hnonempty : other.Nonempty) :
    other = {2} ∨ other = {3} ∨ other = {2, 3} := by
  have hmem : other ∈ ({2, 3} : Finset (Fin 4)).powerset :=
    Finset.mem_powerset.mpr hsubset
  rw [show ({2, 3} : Finset (Fin 4)).powerset =
      ({∅, {2}, {3}, {2, 3}} : Finset (Finset (Fin 4))) by decide] at hmem
  have hne : other ≠ ∅ := Finset.nonempty_iff_ne_empty.mp hnonempty
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
  rcases hmem with hzero | htwo | hthree | hpair
  · exact False.elim (hne hzero)
  · exact Or.inl htwo
  · exact Or.inr (Or.inl hthree)
  · exact Or.inr (Or.inr hpair)

private theorem weakHalf_own_reward_unchanged
    (epsilon : ℝ)
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (recipient partner : Fin 4)
    (hrecipient : recipient = 0 ∨ recipient = 1)
    (hpartner : partner = 0 ∨ partner = 1)
    (hdistinct : recipient ≠ partner)
    (own : Finset (Fin 4))
    (hown : own ⊆ quittingCrossedRawOutsiders recipient partner) :
    weightOfReward (quittingCrossedWeakHalfPerturb epsilon reward)
      (insert recipient own) recipient =
      weightOfReward reward (insert recipient own) recipient := by
  have hpartnerNotOwn : partner ∉ own := by
    intro hmem
    have h := hown hmem
    simp [quittingCrossedRawOutsiders] at h
  have hnotExternal :
      insert recipient own ≠ ({2, 3} : Finset (Fin 4)) := by
    intro heq
    have hmem : recipient ∈ insert recipient own := Finset.mem_insert_self _ _
    rw [heq] at hmem
    rcases hrecipient with hfirst | hsecond
    · subst recipient
      simp at hmem
    · subst recipient
      simp at hmem
  have hnotBoth : ¬(0 ∈ insert recipient own ∧ 1 ∈ insert recipient own) := by
    rcases hrecipient with hfirst | hsecond
    · subst recipient
      rcases hpartner with hp | hp
      · exact False.elim (hdistinct hp.symm)
      · subst partner
        simp [hpartnerNotOwn]
    · subst recipient
      rcases hpartner with hp | hp
      · subst partner
        simp [hpartnerNotOwn]
      · exact False.elim (hdistinct hp.symm)
  simp [weightOfReward, quittingCrossedWeakHalfPerturb, hnotExternal]
  intro _ hzero hone
  exact False.elim (hnotBoth ⟨Finset.mem_insert.mpr hzero,
    Finset.mem_insert.mpr hone⟩)

private theorem weakHalf_external_reward_sub
    (epsilon : ℝ)
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (recipient : Fin 4) (hselected : recipient = 0 ∨ recipient = 1)
    (other : Finset (Fin 4)) (hsubset : other ⊆ ({2, 3} : Finset (Fin 4)))
    (hnonempty : other.Nonempty) :
    weightOfReward (quittingCrossedWeakHalfPerturb epsilon reward) other recipient =
      weightOfReward reward other recipient - epsilon := by
  rcases weakHalf_external_subset_cases other hsubset hnonempty with
    htwo | hthree | hpair
  · subst other
    rcases hselected with hzero | hone
    · subst recipient
      simp [weightOfReward, quittingCrossedWeakHalfPerturb]
    · subst recipient
      simp [weightOfReward, quittingCrossedWeakHalfPerturb]
  · subst other
    rcases hselected with hzero | hone
    · subst recipient
      simp [weightOfReward, quittingCrossedWeakHalfPerturb]
    · subst recipient
      simp [weightOfReward, quittingCrossedWeakHalfPerturb]
  · subst other
    rcases hselected with hzero | hone
    · subst recipient
      simp [weightOfReward, quittingCrossedWeakHalfPerturb]
    · subst recipient
      simp [weightOfReward, quittingCrossedWeakHalfPerturb]

/-- Every weak selected lower comparison gains the same positive margin `ε`. -/
theorem quittingCrossed_strictLowerRanking_of_weakHalfPerturb
    (epsilon : ℝ) (hepsilon : 0 < epsilon)
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (recipient partner : Fin 4)
    (hpair : (recipient = 0 ∧ partner = 1) ∨
      (recipient = 1 ∧ partner = 0))
    (hweak : QuittingCrossedWeakLowerRanking reward recipient partner) :
    QuittingCrossedStrictLowerRanking
      (quittingCrossedWeakHalfPerturb epsilon reward) recipient partner := by
  intro own other hown hother hnonempty
  have hselected : recipient = 0 ∨ recipient = 1 :=
    hpair.elim (fun h => Or.inl h.1) (fun h => Or.inr h.1)
  have hpartner : partner = 0 ∨ partner = 1 :=
    hpair.elim (fun h => Or.inr h.2) (fun h => Or.inl h.2)
  have hne : recipient ≠ partner := by
    rcases hpair with ⟨hr, hp⟩ | ⟨hr, hp⟩ <;> subst recipient <;> subst partner <;>
      decide
  have hotherPair : other ⊆ ({2, 3} : Finset (Fin 4)) := by
    rcases hpair with ⟨hr, hp⟩ | ⟨hr, hp⟩
    · simpa [hr, hp, weakHalf_outsiders_first] using hother
    · simpa [hr, hp, weakHalf_outsiders_second] using hother
  rw [weakHalf_external_reward_sub epsilon reward recipient hselected
    other hotherPair hnonempty,
    weakHalf_own_reward_unchanged epsilon reward recipient partner
      hselected hpartner hne own hown]
  have hcompare := hweak own other hown hother hnonempty
  linarith

end GameTheory
