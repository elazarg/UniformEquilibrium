import UniformEquilibrium.Quitting.Examples.StrictPatientWithdrawalTable
import UniformEquilibrium.Quitting.Classification.QuietExtension.CappedClockOriginalCoalitionRows

/-! # All fourteen advancing-only proper-child obstructions

Each obstruction is one actual joining row of the original game. The
conclusions exclude raw universal certificates, even after dropping Never;
they do not exclude extending a particular child equilibrium.
-/

noncomputable section

namespace GameTheory.StrictPatientWithdrawal

open QuittingRawChildSource GuardedCrossedResponseExamples
open scoped BigOperators

def dualChild : Fin 14 → Finset (Fin 4) :=
  ![{0}, {1}, {0, 1}, {2}, {0, 2}, {1, 2}, {0, 1, 2},
    {3}, {0, 3}, {1, 3}, {0, 1, 3}, {2, 3}, {0, 2, 3}, {1, 2, 3}]

def dualOutside : Fin 14 → Fin 4 := ![1, 2, 2, 0, 1, 0, 3, 0, 1, 0, 2, 0, 1, 0]

def dualCoalition : Fin 14 → Finset (Fin 4) :=
  ![{0}, {1}, {0, 1}, {2}, {0, 2}, {2}, {0, 1, 2},
    {3}, {0, 3}, {1, 3}, {0, 1}, {2, 3}, {0, 2, 3}, {1, 2, 3}]

theorem dualOutside_notMem (index : Fin 14) :
    dualOutside index ∉ dualChild index := by
  fin_cases index <;> decide

theorem dualCoalition_subset (index : Fin 14) :
    dualCoalition index ⊆ dualChild index := by
  fin_cases index <;> decide

theorem dualCoalition_nonempty (index : Fin 14) :
    (rawChildCoalition (dualChild index) (dualCoalition index)).Nonempty := by
  exact (by decide : ∀ index,
    (rawChildCoalition (dualChild index) (dualCoalition index)).Nonempty) index

def dualRow (index : Fin 14) : CappedClockExactLPRow (RawChild (dualChild index)) :=
  .joining ⟨rawChildCoalition (dualChild index) (dualCoalition index),
    dualCoalition_nonempty index⟩

abbrev dualReward
    (table : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)) (index : Fin 14) :=
  rawChildReward table (dualChild index) ⟨dualOutside index, dualOutside_notMem index⟩

def dualColumn (index : Fin 14) (who : Fin 4) : ℝ :=
  if (index = 5 ∧ who = 1) ∨ (index = 10 ∧ who = 3) then -1 else 0

def dualObjective : Fin 14 → ℝ := ![1, 2, 1, 2, 1, 2, 1 / 2, 2, 1, 1, 1, 1, 1, 1]

theorem dual_original_delta
    (table : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (index : Fin 14) (who : RawChild (dualChild index)) :
    cappedClockExactLPDelta (dualReward table index) (dualRow index) who =
      weightOfReward table (insert who.1 (dualCoalition index)) who.1 -
        weightOfReward table (dualCoalition index) who.1 :=
  rawChild_joining_delta table _ _ _ (dualCoalition_subset index) _ who

theorem dual_original_base
    (table : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)) (index : Fin 14) :
    cappedClockExactLPBase (dualReward table index) (dualRow index) =
      weightOfReward table (insert (dualOutside index) (dualCoalition index))
          (dualOutside index) -
        weightOfReward table (dualCoalition index) (dualOutside index) :=
  rawChild_joining_base table _ _ _ (dualCoalition_subset index) _

/-- The printed columns, in original player labels; nonchild entries are unused. -/
theorem dual_column_eq (index : Fin 14) (who : RawChild (dualChild index)) :
    cappedClockExactLPDelta (dualReward reward index) (dualRow index) who =
      dualColumn index who.1 := by
  rw [dual_original_delta]
  fin_cases index
  all_goals rcases who with ⟨who, hwho⟩
  all_goals fin_cases who
  all_goals norm_num [dualChild] at hwho
  all_goals norm_num +decide [dualColumn, dualCoalition, reward, weightOfReward, coalitionCode]

theorem dual_objective_eq (index : Fin 14) :
    cappedClockExactLPBase (dualReward reward index) (dualRow index) = dualObjective index := by
  rw [dual_original_base]
  fin_cases index <;>
    norm_num +decide [dualObjective, dualCoalition, dualOutside, reward,
      weightOfReward, coalitionCode]

theorem dualObjective_half_le (index : Fin 14) : 1 / 2 ≤ dualObjective index := by
  fin_cases index <;> norm_num [dualObjective]

/-- Every zero column is a membership identity, not an accidental numerical cancellation. -/
theorem dualColumn_eq_neg_one_of_not_mem
    (index : Fin 14) (who : RawChild (dualChild index))
    (hnot : who.1 ∉ dualCoalition index) : dualColumn index who.1 = -1 := by
  fin_cases index
  all_goals rcases who with ⟨who, hwho⟩
  all_goals fin_cases who
  all_goals norm_num [dualChild] at hwho
  all_goals norm_num [dualCoalition] at hnot
  all_goals norm_num [dualColumn]

/-- The columns stay nonpositive and the objective positive on the full raw ball. -/
theorem dual_strict_of_dist_lt
    (other : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (hclose : dist other reward < 1 / 100) (index : Fin 14) :
    (∀ who, cappedClockExactLPDelta (dualReward other index) (dualRow index) who ≤ 0) ∧
      0 < cappedClockExactLPBase (dualReward other index) (dualRow index) := by
  have hcoordinate : ∀ terminal who,
      |other terminal who - reward terminal who| ≤ dist other reward := by
    intro terminal who
    simpa only [Real.dist_eq] using
      (dist_le_pi_dist (other terminal) (reward terminal) who).trans
        (dist_le_pi_dist other reward terminal)
  have hrestricted := abs_quittingChildWithOutsiderReward_sub_le
    reward other (· ∉ dualChild index) ⟨dualOutside index, dualOutside_notMem index⟩
      (dist other reward) hcoordinate
  constructor
  · intro who
    by_cases hmem : who.1 ∈ dualCoalition index
    · rw [dual_original_delta, Finset.insert_eq_of_mem hmem, sub_self]
    · have h := (abs_le.mp (abs_cappedClockExactLPDelta_sub_le
        (dualReward reward index) (dualReward other index) (dist other reward)
          hrestricted (dualRow index) who)).2
      rw [dual_column_eq, dualColumn_eq_neg_one_of_not_mem index who hmem] at h
      linarith
  · have h := (abs_le.mp (abs_cappedClockExactLPBase_sub_le
      (dualReward reward index) (dualReward other index) (dist other reward)
        hrestricted (dualRow index))).1
    rw [dual_objective_eq] at h
    have hcenter := dualObjective_half_le index
    linarith

/-- The one-row dual excludes both full and Never-omitting advancing criteria. -/
theorem dual_no_certificates_of_dist_lt
    (other : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (hclose : dist other reward < 1 / 100) (index : Fin 14) :
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
      (by intro row; simp [dualRow]) (fun _ => 1) (by intro row; norm_num)
    · intro who
      simpa using hcolumns who
    · simpa using hobjective

theorem exists_dualChild_index (players : Finset (Fin 4))
    (hnonempty : players.Nonempty) (hproper : players ≠ Finset.univ) :
    ∃ index, players = dualChild index := by
  exact (by decide : ∀ players : Finset (Fin 4), players.Nonempty →
    players ≠ Finset.univ → ∃ index, players = dualChild index) players hnonempty hproper

/-- All fourteen proper nonempty children fail for an internally selected actual outsider. -/
theorem every_proper_child_no_certificates_of_dist_lt
    (other : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (hclose : dist other reward < 1 / 100) (players : Finset (Fin 4))
    (hnonempty : players.Nonempty) (hproper : players ≠ Finset.univ) :
    ∃ outside : {who : Fin 4 // who ∉ players},
      ¬Nonempty (CappedClockParentRewardCertificate (rawChildReward other players outside)) ∧
        ¬Nonempty (CappedClockParentFutureJoinCertificate
          (rawChildReward other players outside)) := by
  obtain ⟨index, rfl⟩ := exists_dualChild_index players hnonempty hproper
  exact ⟨⟨dualOutside index, dualOutside_notMem index⟩,
    dual_no_certificates_of_dist_lt other hclose index⟩

theorem every_proper_child_no_certificates
    (players : Finset (Fin 4)) (hnonempty : players.Nonempty)
    (hproper : players ≠ Finset.univ) :
    ∃ outside : {who : Fin 4 // who ∉ players},
      ¬Nonempty (CappedClockParentRewardCertificate (rawChildReward reward players outside)) ∧
        ¬Nonempty (CappedClockParentFutureJoinCertificate
          (rawChildReward reward players outside)) :=
  every_proper_child_no_certificates_of_dist_lt reward (by norm_num)
    players hnonempty hproper

end GameTheory.StrictPatientWithdrawal
