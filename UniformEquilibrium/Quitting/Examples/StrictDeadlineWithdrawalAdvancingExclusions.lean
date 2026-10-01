import UniformEquilibrium.Quitting.Examples.StrictDeadlineWithdrawalNeighborhood
import UniformEquilibrium.Quitting.Classification.QuietExtension.CappedClockOriginalCoalitionRows

/-! # The fourteen split advancing-only deadline obstructions

Children missing player zero fail the genuine Never row and have no positive
child singleton. This does not assert their F/J-only infeasibility. The seven
proper children containing zero have explicit future or joining obstructions
which also exclude F/J-only certificates. These are compiler exclusions, not
nonexistence of uniform equilibrium.
-/

noncomputable section

namespace GameTheory.StrictDeadlineWithdrawal

open QuittingRawChildSource GuardedCrossedResponseExamples
open scoped BigOperators

private theorem pivot_singleton_pos_of_dist_lt
    (other : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (hclose : dist other reward < 1 / 512) :
    0 < other ⟨{0}, Finset.singleton_nonempty 0⟩ 0 := by
  have h := (abs_le.mp (coordinate_error_le_dist other
    ⟨{0}, Finset.singleton_nonempty 0⟩ 0)).1
  rw [singleton_payoffs] at h
  norm_num at h
  linarith

private theorem nonpivot_singleton_neg_of_dist_lt
    (other : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (hclose : dist other reward < 1 / 512) (who : Fin 4) (hne : who ≠ 0) :
    other ⟨{who}, Finset.singleton_nonempty who⟩ who < 0 := by
  have hcenter : reward ⟨{who}, Finset.singleton_nonempty who⟩ who = -1 / 16 := by
    rw [singleton_payoffs]
    fin_cases who
    · exact (hne rfl).elim
    all_goals norm_num
  have h := (abs_le.mp (coordinate_error_le_dist other
    ⟨{who}, Finset.singleton_nonempty who⟩ who)).2
  rw [hcenter] at h
  linarith

/-- The actual child has no positive singleton when it omits player zero. -/
theorem child_missing_zero_singletons_neg_of_dist_lt
    (other : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (hclose : dist other reward < 1 / 512) (players : Finset (Fin 4))
    (hzero : 0 ∉ players) (who : RawChild players) :
    rawChildReward other players ⟨0, hzero⟩
      ⟨{some who}, Finset.singleton_nonempty (some who)⟩ (some who) < 0 := by
  have hmem : who.1 ∈ players := not_not.mp who.2
  have hne : who.1 ≠ 0 := by
    intro heq
    exact hzero (heq ▸ hmem)
  have hsource := quittingChildWithOutsiderReward_singleton_original other
    (· ∉ players) ⟨0, hzero⟩ (some who) (some who)
  simp only [quittingChildWithOutsiderOriginalEmbedding_some] at hsource
  dsimp only [rawChildReward]
  rw [hsource]
  exact nonpivot_singleton_neg_of_dist_lt other hclose who.1 hne

/-- Genuine N infeasibility; no F/J-only conclusion is asserted here. -/
theorem child_missing_zero_no_full_certificate_of_dist_lt
    (other : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (hclose : dist other reward < 1 / 512) (players : Finset (Fin 4))
    (hzero : 0 ∉ players) :
    ¬Nonempty (CappedClockParentRewardCertificate
      (rawChildReward other players ⟨0, hzero⟩)) := by
  rintro ⟨source⟩
  have hsum : (∑ who, source.weight who * rawChildReward other players ⟨0, hzero⟩
      ⟨{some who}, Finset.singleton_nonempty (some who)⟩ (some who)) ≤ 0 := by
    apply Finset.sum_nonpos
    intro who _
    exact mul_nonpos_of_nonneg_of_nonpos (source.weight_nonneg who)
      (child_missing_zero_singletons_neg_of_dist_lt other hclose players hzero who).le
  have hsource := quittingChildWithOutsiderReward_singleton_original other
    (· ∉ players) ⟨0, hzero⟩ none none
  simp only [quittingChildWithOutsiderOriginalEmbedding_none] at hsource
  have hnever := source.never_row
  dsimp only [rawChildReward] at hnever hsum
  rw [hsource] at hnever
  have hpivot := pivot_singleton_pos_of_dist_lt other hclose
  linarith

def dualChild : Fin 7 → Finset (Fin 4) :=
  ![{0}, {0, 1}, {0, 2}, {0, 3}, {0, 1, 2}, {0, 1, 3}, {0, 2, 3}]

def dualOutside : Fin 7 → Fin 4 := ![2, 2, 1, 1, 3, 2, 1]
abbrev futureIndex (index : Fin 7) : Prop := index = 0 ∨ index = 1
def dualCoalition (index : Fin 7) : Finset (Fin 4) :=
  if futureIndex index then {0} else dualChild index

theorem dualOutside_notMem (index : Fin 7) : dualOutside index ∉ dualChild index := by
  fin_cases index <;> decide

theorem dualCoalition_subset (index : Fin 7) : dualCoalition index ⊆ dualChild index := by
  fin_cases index <;> decide

theorem dualCoalition_nonempty (index : Fin 7) :
    (rawChildCoalition (dualChild index) (dualCoalition index)).Nonempty := by
  exact (by decide : ∀ index,
    (rawChildCoalition (dualChild index) (dualCoalition index)).Nonempty) index

def dualRow (index : Fin 7) : CappedClockExactLPRow (RawChild (dualChild index)) :=
  if futureIndex index then
    .future ⟨rawChildCoalition (dualChild index) (dualCoalition index),
      dualCoalition_nonempty index⟩
  else
    .joining ⟨rawChildCoalition (dualChild index) (dualCoalition index),
      dualCoalition_nonempty index⟩

abbrev dualReward
    (table : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)) (index : Fin 7) :=
  rawChildReward table (dualChild index) ⟨dualOutside index, dualOutside_notMem index⟩

theorem dual_original_delta
    (table : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (index : Fin 7) (who : RawChild (dualChild index)) :
    cappedClockExactLPDelta (dualReward table index) (dualRow index) who =
      if futureIndex index then
        weightOfReward table {who.1} who.1 - weightOfReward table (dualCoalition index) who.1
      else
        weightOfReward table (insert who.1 (dualCoalition index)) who.1 -
          weightOfReward table (dualCoalition index) who.1 := by
  by_cases hfuture : futureIndex index
  · simpa only [dualRow, ite_eq_left hfuture] using
      rawChild_future_delta table _ _ _ (dualCoalition_subset index) _ who
  · simpa only [dualRow, ite_eq_right hfuture] using
      rawChild_joining_delta table _ _ _ (dualCoalition_subset index) _ who

theorem dual_original_base
    (table : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)) (index : Fin 7) :
    cappedClockExactLPBase (dualReward table index) (dualRow index) =
      if futureIndex index then
        weightOfReward table {dualOutside index} (dualOutside index) -
          weightOfReward table (dualCoalition index) (dualOutside index)
      else
        weightOfReward table (insert (dualOutside index) (dualCoalition index))
            (dualOutside index) - weightOfReward table (dualCoalition index) (dualOutside index)
          := by
  by_cases hfuture : futureIndex index
  · simpa only [dualRow, ite_eq_left hfuture] using
      rawChild_future_base table _ _ _ (dualCoalition_subset index) (dualCoalition_nonempty index)
  · simpa only [dualRow, ite_eq_right hfuture] using
      rawChild_joining_base table _ _ _ (dualCoalition_subset index) (dualCoalition_nonempty index)

def dualColumn (index : Fin 7) (who : Fin 4) : ℝ :=
  if index = 1 ∧ who = 1 then -3 else 0

theorem dual_column_eq (index : Fin 7) (who : RawChild (dualChild index)) :
    cappedClockExactLPDelta (dualReward reward index) (dualRow index) who =
      dualColumn index who.1 := by
  rw [dual_original_delta]
  fin_cases index
  all_goals rcases who with ⟨who, hwho⟩
  all_goals fin_cases who
  all_goals norm_num [dualChild] at hwho
  all_goals norm_num +decide [dualColumn, futureIndex, dualCoalition, dualChild,
    reward, integerReward, terminalShift, weightOfReward, coalitionCode]

theorem dual_objective_eq (index : Fin 7) :
    cappedClockExactLPBase (dualReward reward index) (dualRow index) = 1 := by
  rw [dual_original_base]
  fin_cases index
  all_goals norm_num +decide [futureIndex, dualCoalition, dualChild, dualOutside,
    reward, integerReward, terminalShift, weightOfReward, coalitionCode]

/-- Membership makes these zero columns identities for every actual reward completion. -/
theorem dual_delta_eq_zero_of_mem
    (table : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (index : Fin 7) (who : RawChild (dualChild index))
    (hmem : who.1 ∈ dualCoalition index) :
    cappedClockExactLPDelta (dualReward table index) (dualRow index) who = 0 := by
  rw [dual_original_delta]
  by_cases hfuture : futureIndex index
  · have hcoalition : dualCoalition index = {0} := by
      simp only [dualCoalition, ite_eq_left hfuture]
    have hwho : who.1 = 0 := by simpa only [hcoalition, Finset.mem_singleton] using hmem
    rw [ite_eq_left hfuture, hcoalition, hwho, sub_self]
  · rw [ite_eq_right hfuture, Finset.insert_eq_of_mem hmem, sub_self]

theorem dualColumn_eq_neg_three_of_not_mem
    (index : Fin 7) (who : RawChild (dualChild index))
    (hnot : who.1 ∉ dualCoalition index) : dualColumn index who.1 = -3 := by
  fin_cases index
  all_goals rcases who with ⟨who, hwho⟩
  all_goals fin_cases who
  all_goals norm_num [dualChild] at hwho
  all_goals norm_num [dualCoalition, futureIndex, dualChild] at hnot
  all_goals norm_num [dualColumn]

theorem dual_strict_of_dist_lt
    (other : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (hclose : dist other reward < 1 / 512) (index : Fin 7) :
    (∀ who, cappedClockExactLPDelta (dualReward other index) (dualRow index) who ≤ 0) ∧
      0 < cappedClockExactLPBase (dualReward other index) (dualRow index) := by
  have hrestricted := abs_quittingChildWithOutsiderReward_sub_le
    reward other (· ∉ dualChild index) ⟨dualOutside index, dualOutside_notMem index⟩
      (dist other reward) (coordinate_error_le_dist other)
  constructor
  · intro who
    by_cases hmem : who.1 ∈ dualCoalition index
    · exact (dual_delta_eq_zero_of_mem other index who hmem).le
    · have h := (abs_le.mp (abs_cappedClockExactLPDelta_sub_le
        (dualReward reward index) (dualReward other index) (dist other reward)
          hrestricted (dualRow index) who)).2
      rw [dual_column_eq, dualColumn_eq_neg_three_of_not_mem index who hmem] at h
      linarith
  · have h := (abs_le.mp (abs_cappedClockExactLPBase_sub_le
      (dualReward reward index) (dualReward other index) (dist other reward)
        hrestricted (dualRow index))).1
    rw [dual_objective_eq] at h
    linarith

theorem dual_no_certificates_of_dist_lt
    (other : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (hclose : dist other reward < 1 / 512) (index : Fin 7) :
    ¬Nonempty (CappedClockParentRewardCertificate (dualReward other index)) ∧
      ¬Nonempty (CappedClockParentFutureJoinCertificate (dualReward other index)) := by
  obtain ⟨hcolumns, hobjective⟩ := dual_strict_of_dist_lt other hclose index
  constructor
  · apply not_nonempty_cappedClockParentRewardCertificate_of_sampledDual
      (dualReward other index) (fun _ : Fin 1 => dualRow index) (fun _ => 1)
      (by intro row; norm_num)
    · intro who
      simpa using hcolumns who
    · simpa using hobjective
  · apply not_nonempty_cappedClockParentFutureJoinCertificate_of_sampledDual
      (dualReward other index) (fun _ : Fin 1 => dualRow index)
      (by intro row; dsimp only [dualRow]; split_ifs <;> simp)
      (fun _ => 1) (by intro row; norm_num)
    · intro who
      simpa using hcolumns who
    · simpa using hobjective

theorem exists_dualChild_index_of_zero_mem (players : Finset (Fin 4))
    (hzero : 0 ∈ players) (hproper : players ≠ Finset.univ) :
    ∃ index, players = dualChild index := by
  exact (by decide : ∀ players : Finset (Fin 4), 0 ∈ players →
    players ≠ Finset.univ → ∃ index, players = dualChild index) players hzero hproper

/-- Every proper child fails the full criterion; only children containing zero
are asserted to fail F/J-only, and other children have no positive singleton. -/
theorem every_proper_child_split_exclusions_of_dist_lt
    (other : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (hclose : dist other reward < 1 / 512) (players : Finset (Fin 4))
    (hproper : players ≠ Finset.univ) :
    ∃ outside : {who : Fin 4 // who ∉ players},
      ¬Nonempty (CappedClockParentRewardCertificate (rawChildReward other players outside)) ∧
      (0 ∈ players → ¬Nonempty
        (CappedClockParentFutureJoinCertificate (rawChildReward other players outside))) ∧
      (0 ∉ players → ∀ who : RawChild players, rawChildReward other players outside
        ⟨{some who}, Finset.singleton_nonempty (some who)⟩ (some who) < 0) := by
  by_cases hzero : 0 ∈ players
  · obtain ⟨index, rfl⟩ := exists_dualChild_index_of_zero_mem players hzero hproper
    obtain ⟨hfull, hrows⟩ := dual_no_certificates_of_dist_lt other hclose index
    exact ⟨⟨dualOutside index, dualOutside_notMem index⟩, hfull,
      fun _ => hrows, fun hnot => (hnot hzero).elim⟩
  · exact ⟨⟨0, hzero⟩,
      child_missing_zero_no_full_certificate_of_dist_lt other hclose players hzero,
      fun hmem => (hzero hmem).elim,
      fun _ who => child_missing_zero_singletons_neg_of_dist_lt other hclose players hzero who⟩

theorem every_proper_child_split_exclusions
    (players : Finset (Fin 4)) (hproper : players ≠ Finset.univ) :
    ∃ outside : {who : Fin 4 // who ∉ players},
      ¬Nonempty (CappedClockParentRewardCertificate (rawChildReward reward players outside)) ∧
      (0 ∈ players → ¬Nonempty
        (CappedClockParentFutureJoinCertificate (rawChildReward reward players outside))) ∧
      (0 ∉ players → ∀ who : RawChild players, rawChildReward reward players outside
        ⟨{some who}, Finset.singleton_nonempty (some who)⟩ (some who) < 0) :=
  every_proper_child_split_exclusions_of_dist_lt reward (by norm_num) players hproper

end GameTheory.StrictDeadlineWithdrawal
