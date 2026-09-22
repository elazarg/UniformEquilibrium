import UniformEquilibrium.Quitting.Classification.LCP.QuittingRewardAdapter
import UniformEquilibrium.Quitting.Classification.QuietExtension.CappedClockPositiveSingletonQuietExtension

/-! # Full-child joining obstruction and a collision-only reward modification

At the full-child coalition, the child terms in the raw joining row vanish.
Changing only the outsider's full-parent collision payoff can therefore defeat
every joining certificate without changing singleton or child reward data.
The modification is not asserted to be small in any norm.
-/

noncomputable section

namespace GameTheory

open scoped BigOperators

variable {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]

omit [Fintype ι] [DecidableEq ι] [Nonempty ι] in
theorem none_not_mem_cappedClockChildCoalition (A : Finset ι) :
    none ∉ cappedClockChildCoalition A := by
  intro h
  obtain ⟨i, _, hi⟩ := Finset.mem_map.mp h
  change some i = none at hi
  exact Option.some_ne_none i hi

omit [Nonempty ι] in
theorem cappedClockJoinedCoalition_univ :
    cappedClockJoinedCoalition (Finset.univ : Finset ι) = Finset.univ := by
  apply Finset.eq_univ_of_forall
  intro who
  cases who with
  | none => exact Finset.mem_insert_self _ _
  | some i =>
      apply Finset.mem_insert_of_mem
      exact Finset.mem_map.mpr ⟨i, Finset.mem_univ i, rfl⟩

/-- Only joining rows are used; the weights need not be nonnegative. -/
theorem fullChild_join_le_of_joinRows
    (reward : {A : Finset (Option ι) // A.Nonempty} → Option ι → ℝ)
    (weight : ι → ℝ)
    (hjoin : ∀ A (hA : A.Nonempty),
      reward ⟨cappedClockJoinedCoalition A,
            cappedClockJoinedCoalition_nonempty A⟩ none -
          reward ⟨cappedClockChildCoalition A,
            cappedClockChildCoalition_nonempty hA⟩ none ≤
        ∑ i, weight i *
          (reward ⟨cappedClockChildCoalition (insert i A),
              cappedClockChildCoalition_nonempty (Finset.insert_nonempty i A)⟩ (some i) -
            reward ⟨cappedClockChildCoalition A,
              cappedClockChildCoalition_nonempty hA⟩ (some i))) :
    reward ⟨cappedClockJoinedCoalition Finset.univ,
        cappedClockJoinedCoalition_nonempty Finset.univ⟩ none ≤
      reward ⟨cappedClockChildCoalition Finset.univ,
        cappedClockChildCoalition_nonempty Finset.univ_nonempty⟩ none := by
  have h := hjoin Finset.univ Finset.univ_nonempty
  have hinsert (i : ι) : insert i Finset.univ = (Finset.univ : Finset ι) :=
    Finset.insert_eq_of_mem (Finset.mem_univ i)
  simpa only [hinsert, sub_self, mul_zero, Finset.sum_const_zero, sub_nonpos] using h

theorem CappedClockParentRewardCertificate.fullChild_join_le
    {reward : {A : Finset (Option ι) // A.Nonempty} → Option ι → ℝ}
    (certificate : CappedClockParentRewardCertificate reward) :
    reward ⟨cappedClockJoinedCoalition Finset.univ,
        cappedClockJoinedCoalition_nonempty Finset.univ⟩ none ≤
      reward ⟨cappedClockChildCoalition Finset.univ,
        cappedClockChildCoalition_nonempty Finset.univ_nonempty⟩ none :=
  fullChild_join_le_of_joinRows reward certificate.weight certificate.join_row

theorem CappedClockParentFutureJoinCertificate.fullChild_join_le
    {reward : {A : Finset (Option ι) // A.Nonempty} → Option ι → ℝ}
    (certificate : CappedClockParentFutureJoinCertificate reward) :
    reward ⟨cappedClockJoinedCoalition Finset.univ,
        cappedClockJoinedCoalition_nonempty Finset.univ⟩ none ≤
      reward ⟨cappedClockChildCoalition Finset.univ,
        cappedClockChildCoalition_nonempty Finset.univ_nonempty⟩ none :=
  fullChild_join_le_of_joinRows reward certificate.weight certificate.join_row

/-- Replace only the outsider's payoff at the full-parent collision by its
full-child payoff plus the specified gap. -/
def cappedClockFullChildJoinModification
    (reward : {A : Finset (Option ι) // A.Nonempty} → Option ι → ℝ)
    (gap : ℝ) : {A : Finset (Option ι) // A.Nonempty} → Option ι → ℝ :=
  fun coalition who =>
    if coalition.1 = Finset.univ ∧ who = none then
      reward ⟨cappedClockChildCoalition Finset.univ,
        cappedClockChildCoalition_nonempty Finset.univ_nonempty⟩ none + gap
    else reward coalition who

/-- All child recipients' reward coordinates are unchanged, even at collisions. -/
theorem cappedClockFullChildJoinModification_some
    (reward : {A : Finset (Option ι) // A.Nonempty} → Option ι → ℝ)
    (gap : ℝ) (coalition : {A : Finset (Option ι) // A.Nonempty}) (i : ι) :
    cappedClockFullChildJoinModification reward gap coalition (some i) =
      reward coalition (some i) := by
  simp only [cappedClockFullChildJoinModification, Option.some_ne_none, and_false, ite_false]

/-- Coalitions not containing the outsider retain every reward coordinate. -/
theorem cappedClockFullChildJoinModification_of_none_not_mem
    (reward : {A : Finset (Option ι) // A.Nonempty} → Option ι → ℝ)
    (gap : ℝ) (coalition : {A : Finset (Option ι) // A.Nonempty})
    (hquiet : none ∉ coalition.1) (who : Option ι) :
    cappedClockFullChildJoinModification reward gap coalition who = reward coalition who := by
  have hne : coalition.1 ≠ Finset.univ := by
    intro heq
    apply hquiet
    rw [heq]
    exact Finset.mem_univ none
  simp only [cappedClockFullChildJoinModification, hne, false_and, ite_false]

/-- A nonempty child ensures that the full-parent collision is never a singleton. -/
theorem cappedClockFullChildJoinModification_singleton
    (reward : {A : Finset (Option ι) // A.Nonempty} → Option ι → ℝ)
    (gap : ℝ) (owner who : Option ι) :
    cappedClockFullChildJoinModification reward gap
        ⟨{owner}, Finset.singleton_nonempty owner⟩ who =
      reward ⟨{owner}, Finset.singleton_nonempty owner⟩ who := by
  have hne : ({owner} : Finset (Option ι)) ≠ Finset.univ := by
    intro heq
    have hn : none = owner := by
      apply Finset.mem_singleton.mp
      rw [heq]
      exact Finset.mem_univ none
    obtain ⟨i⟩ := ‹Nonempty ι›
    have hi : some i = owner := by
      apply Finset.mem_singleton.mp
      rw [heq]
      exact Finset.mem_univ (some i)
    exact Option.some_ne_none i (hi.trans hn.symm)
  simp only [cappedClockFullChildJoinModification, hne, false_and, ite_false]

theorem cappedClockFullChildJoinModification_singletonMatrix
    (reward : {A : Finset (Option ι) // A.Nonempty} → Option ι → ℝ) (gap : ℝ) :
    QuittingLCPClassification.quittingSingletonMatrix
        (cappedClockFullChildJoinModification reward gap) =
      QuittingLCPClassification.quittingSingletonMatrix reward := by
  funext who owner
  simp only [QuittingLCPClassification.quittingSingletonMatrix,
    cappedClockFullChildJoinModification_singleton]

theorem cappedClockFullChildJoinModification_deleteReward
    (reward : {A : Finset (Option ι) // A.Nonempty} → Option ι → ℝ) (gap : ℝ) :
    quittingDeleteReward (cappedClockFullChildJoinModification reward gap) (· = none) =
      quittingDeleteReward reward (· = none) := by
  funext coalition who
  change cappedClockFullChildJoinModification reward gap _ who.1 = _
  rcases who with ⟨who, hwho⟩
  cases who with
  | none => exact (hwho rfl).elim
  | some i => exact cappedClockFullChildJoinModification_some reward gap _ i

/-- The full-child joining gain is exactly the chosen gap. -/
theorem cappedClockFullChildJoinModification_join_gain
    (reward : {A : Finset (Option ι) // A.Nonempty} → Option ι → ℝ) (gap : ℝ) :
    cappedClockFullChildJoinModification reward gap
        ⟨cappedClockJoinedCoalition Finset.univ,
          cappedClockJoinedCoalition_nonempty Finset.univ⟩ none -
      cappedClockFullChildJoinModification reward gap
        ⟨cappedClockChildCoalition Finset.univ,
          cappedClockChildCoalition_nonempty Finset.univ_nonempty⟩ none = gap := by
  rw [cappedClockFullChildJoinModification_of_none_not_mem reward gap
    ⟨cappedClockChildCoalition Finset.univ,
      cappedClockChildCoalition_nonempty Finset.univ_nonempty⟩
    (none_not_mem_cappedClockChildCoalition Finset.univ)]
  unfold cappedClockFullChildJoinModification
  rw [ite_eq_left ⟨cappedClockJoinedCoalition_univ, rfl⟩]
  exact add_sub_cancel_left _ _

theorem cappedClockFullChildJoinModification_not_rewardCertificate
    (reward : {A : Finset (Option ι) // A.Nonempty} → Option ι → ℝ)
    (gap : ℝ) (hgap : 0 < gap) :
    ¬Nonempty (CappedClockParentRewardCertificate
      (cappedClockFullChildJoinModification reward gap)) := by
  rintro ⟨certificate⟩
  have h := certificate.fullChild_join_le
  have heq := cappedClockFullChildJoinModification_join_gain reward gap
  linarith

theorem cappedClockFullChildJoinModification_not_futureJoinCertificate
    (reward : {A : Finset (Option ι) // A.Nonempty} → Option ι → ℝ)
    (gap : ℝ) (hgap : 0 < gap) :
    ¬Nonempty (CappedClockParentFutureJoinCertificate
      (cappedClockFullChildJoinModification reward gap)) := by
  rintro ⟨certificate⟩
  have h := certificate.fullChild_join_le
  have heq := cappedClockFullChildJoinModification_join_gain reward gap
  linarith

end GameTheory
