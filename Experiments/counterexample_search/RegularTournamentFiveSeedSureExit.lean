/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Experiments.counterexample_search.RegularTournamentFiveSeed
import UniformEquilibrium.Quitting.Paths.SureExitSet

/-!
# The regular five-player tournament seed is not a counterexample table

The seed module fixes one literal reward table: singleton rows realize the
regular five-cycle matrix `2 A - Aᵀ`, the pair `{0, 1}` pays its collider one,
and *every other coalition of two or more players pays zero to everybody*.
That zero completion is what this file reads.

Against such a table the grand coalition is a sure exit set in the sense of
`GameTheory.IsQuittingSureExitSet`: everybody quitting at once pays zero, and
a player who stays behind is still absorbed by the other four and still paid
zero.  The landed producer
`isUniformEquilibriumPayoff_setReward_of_isQuittingSureExitSet` then turns
that into a uniform-equilibrium payoff, so the seed's realized game has one
and is therefore not a counterexample to uniform-equilibrium existence.

The exact inventory is proved as well: a coalition passes the sure-exit test
for this table precisely when it has at least three members, or is one of the
four singletons other than `{0}` — twenty coalitions in all.  Only the empty
set, the singleton `{0}`, and the ten pairs fail.  The pairs fail because a
tournament always has a winner, and the winner of a pair prefers its own solo
row (worth three) to the pair row (worth at most one); `{0}` fails at the
marked collision, where player one prefers joining to being preempted.

## Scope

This is a statement about the *realized* table only.  The seed's geometry
theorems — the singleton matrix, the full normal core, the absent homogeneous
simplex branch, the strict directed preemption cycle, and the marked immediate
collision — read only singleton rows together with the single `{0, 1}` entry,
and none of them is affected.  The seed remains a checked calibration of what
the graph side of the search can realize; what dies here is the reading of its
zero-completed table as a counterexample candidate.  Any other completion of
the same singleton geometry is a different table and is not addressed.
-/

namespace GameTheory
namespace RegularTournamentFiveSeed

open Finset QuittingSureSetOwnerRepair Math.LinearProgramming

/-! ## Reading the literal table -/

/-- Every coalition of at least two players pays zero, except the marked pair
`{0, 1}`, which pays one to its collider. -/
theorem setReward_of_two_le_card {S : Finset Player} (hcard : 2 ≤ S.card)
    (who : Player) :
    quittingSetReward reward S who =
      if S = ({0, 1} : Finset Player) ∧ who = 1 then 1 else 0 := by
  have hS : S.Nonempty := Finset.card_pos.mp (by omega)
  have hone : ¬ S.card = 1 := by omega
  rw [quittingSetReward_of_nonempty reward hS]
  by_cases hpair : S = ({0, 1} : Finset Player)
  · subst hpair
    by_cases hwho : who = 1 <;> simp [reward, hwho]
  · simp [reward, hone, hpair]

/-- No coalition of at least two players pays anybody more than one. -/
theorem setReward_le_one_of_two_le_card {S : Finset Player} (hcard : 2 ≤ S.card)
    (who : Player) : quittingSetReward reward S who ≤ 1 := by
  rw [setReward_of_two_le_card hcard]
  split_ifs <;> norm_num

/-- Every coalition of at least three players pays zero: the marked pair is
the table's only nonzero multi-player row. -/
theorem setReward_eq_zero_of_three_le_card {S : Finset Player}
    (hcard : 3 ≤ S.card) (who : Player) : quittingSetReward reward S who = 0 := by
  rw [setReward_of_two_le_card (by omega), if_neg]
  rintro ⟨rfl, -⟩
  exact absurd hcard (by decide)

/-- A solo row of the literal table. -/
theorem setReward_singleton (owner who : Player) :
    quittingSetReward reward ({owner} : Finset Player) who =
      1 + singletonMatrix who owner := by
  rw [quittingSetReward_of_nonempty reward (Finset.singleton_nonempty owner)]
  simp [reward]

/-- Every solo row of the literal table is nonnegative: its entries are `0`,
`1`, and `3`. -/
theorem zero_le_setReward_singleton (owner who : Player) :
    0 ≤ quittingSetReward reward ({owner} : Finset Player) who := by
  rw [setReward_singleton]
  fin_cases owner <;> fin_cases who <;>
    norm_num [singletonMatrix, tournamentSkewMatrix, adjacency]

/-- The tournament has a winner in every pair, and the winner's matrix entry
against the loser is `2`. -/
theorem singletonMatrix_eq_two_or (first second : Player) :
    first = second ∨ singletonMatrix first second = 2 ∨
      singletonMatrix second first = 2 := by
  fin_cases first <;> fin_cases second <;>
    norm_num [singletonMatrix, tournamentSkewMatrix, adjacency]

/-! ## Which coalitions are sure exit sets -/

/-- **Three or more players exit surely.**  Both membership toggles land in
the zero part of the table. -/
theorem isQuittingSureExitSet_of_three_le_card {S : Finset Player}
    (hcard : 3 ≤ S.card) : IsQuittingSureExitSet reward S := by
  refine ⟨fun member hmem ↦ ?_, fun outsider hout ↦ ?_⟩
  · have herase : 2 ≤ (S.erase member).card := by
      rw [Finset.card_erase_of_mem hmem]
      omega
    have hno : ¬ (S.erase member = ({0, 1} : Finset Player) ∧ member = 1) := by
      rintro ⟨hpair, rfl⟩
      have hmemErase : (1 : Player) ∈ S.erase 1 := by
        rw [hpair]
        decide
      exact absurd hmemErase (Finset.notMem_erase 1 S)
    rw [setReward_eq_zero_of_three_le_card hcard,
      setReward_of_two_le_card herase, if_neg hno]
  · have hinsert : 3 ≤ (insert outsider S).card := by
      rw [Finset.card_insert_of_notMem hout]
      omega
    rw [setReward_eq_zero_of_three_le_card hcard,
      setReward_eq_zero_of_three_le_card hinsert]

/-- **The grand-coalition exit.**  All five players quitting at once is an
exact terminal Nash equilibrium of the seed's realized game. -/
theorem isQuittingSureExitSet_univ :
    IsQuittingSureExitSet reward (Finset.univ : Finset Player) :=
  isQuittingSureExitSet_of_three_le_card (by decide)

/-- **The surviving solo exits.**  Any single quitter other than player zero
exits surely: its own row pays one, and every opponent's alternative is a
zero pair row against a nonnegative solo row. -/
theorem isQuittingSureExitSet_singleton_of_ne_zero {owner : Player}
    (howner : owner ≠ 0) :
    IsQuittingSureExitSet reward ({owner} : Finset Player) := by
  refine ⟨fun member hmem ↦ ?_, fun outsider hout ↦ ?_⟩
  · obtain rfl : member = owner := Finset.mem_singleton.mp hmem
    rw [Finset.erase_singleton, quittingSetReward_empty]
    exact zero_le_setReward_singleton _ _
  · have hne : outsider ≠ owner := by simpa using hout
    have hcard : 2 ≤ (insert outsider ({owner} : Finset Player)).card := by
      rw [Finset.card_insert_of_notMem (by simpa using hne)]
      simp
    have hno : ¬ (insert outsider ({owner} : Finset Player) =
        ({0, 1} : Finset Player) ∧ outsider = 1) := by
      rintro ⟨hpair, rfl⟩
      have hmemPair : owner ∈ ({0, 1} : Finset Player) := by
        rw [← hpair]
        simp
      rcases Finset.mem_insert.mp hmemPair with hzero | hone
      · exact howner hzero
      · exact hne (Finset.mem_singleton.mp hone).symm
    rw [setReward_of_two_le_card hcard, if_neg hno]
    exact zero_le_setReward_singleton owner outsider

/-! ## Which coalitions are not sure exit sets -/

/-- Nobody exiting is unstable: a solo quit pays its owner one. -/
theorem not_isQuittingSureExitSet_empty :
    ¬ IsQuittingSureExitSet reward (∅ : Finset Player) := by
  rintro ⟨-, houtsider⟩
  have h := houtsider 0 (Finset.notMem_empty 0)
  rw [quittingSetReward_empty,
    show insert (0 : Player) (∅ : Finset Player) = {0} from by decide,
    setReward_singleton, singletonMatrix_diagonal] at h
  norm_num at h

/-- Player zero's solo exit is unstable: it is the owner of the marked
collision, and player one strictly prefers joining. -/
theorem not_isQuittingSureExitSet_singleton_zero :
    ¬ IsQuittingSureExitSet reward ({0} : Finset Player) := by
  rintro ⟨-, houtsider⟩
  have h := houtsider 1 (by decide)
  rw [show insert (1 : Player) ({0} : Finset Player) = ({0, 1} : Finset Player)
      from by decide,
    setReward_of_two_le_card (by decide), if_pos ⟨rfl, rfl⟩,
    setReward_singleton] at h
  norm_num [singletonMatrix, tournamentSkewMatrix, adjacency] at h

/-- A pair whose first member beats the second is unstable: the winner
prefers its own solo row, worth three, to the pair row, worth at most one. -/
theorem not_isQuittingSureExitSet_pair {first second : Player}
    (hne : first ≠ second) (hbeats : singletonMatrix first second = 2) :
    ¬ IsQuittingSureExitSet reward ({first, second} : Finset Player) := by
  rintro ⟨hmember, -⟩
  have hcard : 2 ≤ ({first, second} : Finset Player).card := by
    rw [Finset.card_insert_of_notMem (by simpa using hne)]
    simp
  have h := hmember first (by simp)
  rw [Finset.erase_insert (by simpa using hne), setReward_singleton, hbeats] at h
  have hle := setReward_le_one_of_two_le_card hcard first
  linarith

/-- No two-player coalition exits surely. -/
theorem not_isQuittingSureExitSet_of_card_eq_two {S : Finset Player}
    (hcard : S.card = 2) : ¬ IsQuittingSureExitSet reward S := by
  obtain ⟨first, second, hne, rfl⟩ := Finset.card_eq_two.mp hcard
  rcases singletonMatrix_eq_two_or first second with heq | hbeats | hbeats
  · exact absurd heq hne
  · exact not_isQuittingSureExitSet_pair hne hbeats
  · rw [Finset.pair_comm]
    exact not_isQuittingSureExitSet_pair hne.symm hbeats

/-! ## The inventory and the headline -/

/-- **The sure exit sets of the literal table, exactly.**  A coalition passes
the sure-exit test precisely when it has at least three members or is a
singleton other than `{0}`. -/
theorem isQuittingSureExitSet_iff (S : Finset Player) :
    IsQuittingSureExitSet reward S ↔
      3 ≤ S.card ∨ (S.card = 1 ∧ S ≠ ({0} : Finset Player)) := by
  constructor
  · intro hS
    have hcases : S.card = 0 ∨ S.card = 1 ∨ S.card = 2 ∨ 3 ≤ S.card := by omega
    rcases hcases with hzero | hone | htwo | hthree
    · rw [Finset.card_eq_zero.mp hzero] at hS
      exact absurd hS not_isQuittingSureExitSet_empty
    · refine Or.inr ⟨hone, ?_⟩
      rintro rfl
      exact not_isQuittingSureExitSet_singleton_zero hS
    · exact absurd hS (not_isQuittingSureExitSet_of_card_eq_two htwo)
    · exact Or.inl hthree
  · rintro (hthree | ⟨hone, hne⟩)
    · exact isQuittingSureExitSet_of_three_le_card hthree
    · obtain ⟨owner, rfl⟩ := Finset.card_eq_one.mp hone
      exact isQuittingSureExitSet_singleton_of_ne_zero (by simpa using hne)

/-- **Twenty sure exit sets.**  The ten triples, the five quadruples, the
grand coalition, and the four solo exits other than player zero's. -/
theorem exists_card_eq_twenty_isQuittingSureExitSet :
    ∃ family : Finset (Finset Player),
      (∀ S : Finset Player, S ∈ family ↔ IsQuittingSureExitSet reward S) ∧
        family.card = 20 := by
  refine ⟨Finset.univ.filter fun S ↦
    3 ≤ S.card ∨ (S.card = 1 ∧ S ≠ ({0} : Finset Player)), fun S ↦ ?_, by decide⟩
  simp [isQuittingSureExitSet_iff]

/-- The grand-coalition exit pays everybody zero. -/
theorem setReward_univ_eq_zero :
    quittingSetReward reward (Finset.univ : Finset Player) = 0 := by
  funext who
  exact setReward_eq_zero_of_three_le_card (by decide) who

/-- **The seed's realized table has a uniform-equilibrium payoff.**  All five
players quitting at date zero delivers the zero payoff vector and caps every
behavioral deviation, so zero is a uniform-equilibrium payoff. -/
theorem isUniformEquilibriumPayoff_zero :
    (quittingGame reward).IsUniformEquilibriumPayoff none (0 : Payoff Player) := by
  rw [← setReward_univ_eq_zero]
  exact isUniformEquilibriumPayoff_setReward_of_isQuittingSureExitSet reward
    isQuittingSureExitSet_univ

/-- **The literal seed table is not a counterexample table.**  Nonexistence of
a uniform-equilibrium payoff is the negation of this statement. -/
theorem exists_isUniformEquilibriumPayoff :
    ∃ value : Payoff Player,
      (quittingGame reward).IsUniformEquilibriumPayoff none value :=
  ⟨0, isUniformEquilibriumPayoff_zero⟩

end RegularTournamentFiveSeed
end GameTheory
