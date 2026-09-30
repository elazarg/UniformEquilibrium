import UniformEquilibrium.Quitting.Stationary.GuardedCrossedResponseRawProducer
import UniformEquilibrium.Quitting.Classification.LCP.NonnegativeInverseRewardApproximation

/-! # Strict unit-ceiling raw guards survive literal singleton perturbation -/

noncomputable section

namespace GameTheory

open QuittingLCPClassification

variable {n : ℕ}

private theorem singletonPerturb_own_insert
    (epsilon : ℝ)
    (reward : {S : Finset (Fin n) // S.Nonempty} → Payoff (Fin n))
    (recipient : Fin n) (subset : Finset (Fin n)) :
    weightOfReward (subtractOffOwnSingletonReward epsilon reward)
        (insert recipient subset) recipient =
      weightOfReward reward (insert recipient subset) recipient := by
  simp [weightOfReward, subtractOffOwnSingletonReward]

private theorem singletonPerturb_weight_le
    (epsilon : ℝ) (hepsilon : 0 ≤ epsilon)
    (reward : {S : Finset (Fin n) // S.Nonempty} → Payoff (Fin n))
    (recipient : Fin n) (subset : Finset (Fin n)) :
    weightOfReward (subtractOffOwnSingletonReward epsilon reward) subset recipient ≤
      weightOfReward reward subset recipient := by
  unfold weightOfReward
  split_ifs with hnonempty
  · dsimp [subtractOffOwnSingletonReward]
    split_ifs <;> linarith
  · exact le_rfl

/-- The lower ranking inequalities improve or remain strict for every positive
off-own singleton subtraction. -/
theorem quittingCrossed_strictLowerRanking_subtractOffOwnSingletonReward
    (epsilon : ℝ) (hepsilon : 0 ≤ epsilon)
    (reward : {S : Finset (Fin n) // S.Nonempty} → Payoff (Fin n))
    (recipient partner : Fin n)
    (hraw : QuittingCrossedStrictLowerRanking reward recipient partner) :
    QuittingCrossedStrictLowerRanking
      (subtractOffOwnSingletonReward epsilon reward) recipient partner := by
  intro own other hown hother hnonempty
  rw [singletonPerturb_own_insert]
  exact lt_of_le_of_lt (singletonPerturb_weight_le epsilon hepsilon reward recipient other)
    (hraw own other hown hother hnonempty)

private theorem singletonPerturb_partner_insert
    (epsilon : ℝ)
    (reward : {S : Finset (Fin n) // S.Nonempty} → Payoff (Fin n))
    (recipient partner : Fin n)
    (outsider : Finset (Fin n)) (hnonempty : outsider.Nonempty)
    (hsubset : outsider ⊆ quittingCrossedRawOutsiders recipient partner) :
    weightOfReward (subtractOffOwnSingletonReward epsilon reward)
        (insert partner outsider) recipient =
      weightOfReward reward (insert partner outsider) recipient := by
  obtain ⟨coordinate, hcoordinate⟩ := hnonempty
  have hne : partner ≠ coordinate := by
    have hmem := hsubset hcoordinate
    simp only [quittingCrossedRawOutsiders, Finset.mem_erase] at hmem
    exact hmem.1.symm
  have hcard : (insert partner outsider).card ≠ 1 := by
    have hlt : 1 < (insert partner outsider).card :=
      Finset.one_lt_card.mpr ⟨partner, Finset.mem_insert_self _ _,
        coordinate, Finset.mem_insert_of_mem hcoordinate, hne⟩
    omega
  simp [weightOfReward, subtractOffOwnSingletonReward, hcard]

/-- Only the empty-outsider joining gap shrinks, by exactly `epsilon`. -/
theorem quittingCrossed_strictUnitJoining_subtractOffOwnSingletonReward
    (epsilon : ℝ)
    (reward : {S : Finset (Fin n) // S.Nonempty} → Payoff (Fin n))
    (recipient partner : Fin n) (hdistinct : recipient ≠ partner)
    (hraw : QuittingCrossedStrictUnitJoining reward recipient partner)
    (hsmall : epsilon < weightOfReward reward {partner} recipient -
      weightOfReward reward (insert recipient {partner}) recipient) :
    QuittingCrossedStrictUnitJoining
      (subtractOffOwnSingletonReward epsilon reward) recipient partner := by
  intro outsider hsubset
  rw [singletonPerturb_own_insert]
  by_cases hempty : outsider = ∅
  · subst outsider
    change weightOfReward reward (insert recipient {partner}) recipient <
      weightOfReward (subtractOffOwnSingletonReward epsilon reward) {partner} recipient
    have hpartner : weightOfReward (subtractOffOwnSingletonReward epsilon reward)
        {partner} recipient = weightOfReward reward {partner} recipient - epsilon := by
      simp [weightOfReward, subtractOffOwnSingletonReward, hdistinct]
    rw [hpartner]
    linarith
  · rw [singletonPerturb_partner_insert epsilon reward recipient partner
      outsider (Finset.nonempty_iff_ne_empty.mpr hempty) hsubset]
    exact hraw outsider hsubset

end GameTheory
