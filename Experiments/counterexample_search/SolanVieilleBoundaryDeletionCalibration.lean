/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Research.Quitting.BlockDeletionInequality
import UniformEquilibrium.Quitting.Examples.SolanVieilleBoundaryEquilibrium
import UniformEquilibrium.Quitting.Examples.SolanVieilleBoundarySoloPeriodicNoGo
import UniformEquilibrium.Quitting.Examples.SolanVieilleBoundaryTable

/-!
# The deletion constants of the Solan–Vieille boundary table

This file computes, for the literal four-player table of
`UniformEquilibrium/Quitting/Examples/SolanVieilleBoundaryTable.lean`, every
constant the block-deletion machinery of
`Research/Quitting/BlockPlayerDeletion.lean` and
`Research/Quitting/BlockDeletionInequality.lean` reads off a reward table: the
continue floor, the punishment value, the solo premium, the join cap, and the
resulting deletion excess bound.  It also identifies the sure exit set of each
three-player subgame.

Every constant lands on the table's own margin `1`.  At every player the
continue floor and the punishment value are `0`, the solo reward is `1`, and
the join cap is `1`, so the excess bound at absorption bound `A` is exactly
`A + 1` and, in the vanishing-absorption limit, exactly `1`.  Both clauses of
the block dispensability gate therefore fail, each by exactly `1`.  Each
three-player subgame has exactly one sure exit set, a cross pair, and the
omitted player's join gain against it is exactly `1`.

Because the reward entries are integers, the finite checks are routed through
the integer copy `boundaryValue`, where they are decidable.

## Scope

These are calibration facts about one table, not exclusions.  The table is
already resolved positively:
`boundaryReward_exists_uniformEquilibriumPayoff` supplies a
uniform-equilibrium payoff and
`boundaryReward_not_hasTerminalExploitabilityGap` rules out every positive
terminal exploitability gap, so the deletion necessary conditions are vacuous
here.  What the numbers show is that the deletion method is sharp rather than
merely inconclusive on this table: its hypotheses miss by zero, so no
weakening of the constants inside the method resolves the table, and the
equilibrium that does resolve it has all four players quitting and is not of
lift shape.

Uniqueness of the subgame sure exit set is uniqueness within the sure-exit
family only.  Nothing here rules out subgame approximate equilibria of other
shapes, in particular ones with small per-stage absorption.

The module is its own reproduction: building it kernel-checks every statement.
-/

namespace GameTheory

namespace SolanVieilleBoundary

open QuittingSureSetOwnerRepair

/-! ## An integer copy of the table -/

/-- Integer copy of `boundaryReward`, extended by `0` at the empty
coalition. -/
def boundaryValue (S : Finset Player) (who : Player) : ℤ :=
  match decide (0 ∈ S), decide (1 ∈ S), decide (2 ∈ S), decide (3 ∈ S) with
  | true, false, false, false => ![1, 4, 0, 0] who
  | false, true, false, false => ![4, 1, 0, 0] who
  | false, false, true, false => ![0, 0, 1, 4] who
  | false, false, false, true => ![0, 0, 4, 1] who
  | true, true, false, false => ![1, 1, 1, 1] who
  | true, false, true, false => ![1, 1, 1, 0] who
  | true, false, false, true => ![1, 0, 1, 1] who
  | false, true, true, false => ![0, 1, 1, 1] who
  | false, true, false, true => ![1, 1, 0, 1] who
  | false, false, true, true => ![1, 1, 1, 1] who
  | true, true, true, false => ![1, 0, 0, 0] who
  | true, true, false, true => ![0, 1, 0, 0] who
  | true, false, true, true => ![0, 0, 0, 1] who
  | false, true, true, true => ![0, 0, 1, 0] who
  | true, true, true, true => ![-1, -1, -1, -1] who
  | false, false, false, false => ![0, 0, 0, 0] who

/-- The extended set reward of the table is the integer copy. -/
theorem quittingSetReward_eq_boundaryValue (S : Finset Player) (who : Player) :
    quittingSetReward boundaryReward S who = (boundaryValue S who : ℝ) := by
  by_cases hS : S.Nonempty
  · rw [quittingSetReward_of_nonempty boundaryReward hS]
    rcases hb0 : decide ((0 : Player) ∈ S) with _ | _ <;>
      rcases hb1 : decide ((1 : Player) ∈ S) with _ | _ <;>
        rcases hb2 : decide ((2 : Player) ∈ S) with _ | _ <;>
          rcases hb3 : decide ((3 : Player) ∈ S) with _ | _ <;>
            simp only [boundaryReward, boundaryValue, hb0, hb1, hb2, hb3] <;>
              fin_cases who <;> norm_num
  · rw [Finset.not_nonempty_iff_eq_empty.mp hS]
    have hzero : ∀ w : Player, boundaryValue ∅ w = 0 := by decide
    simp [quittingSetReward, hzero]

theorem boundaryReward_eq_boundaryValue (S : Finset Player) (hS : S.Nonempty)
    (who : Player) :
    boundaryReward ⟨S, hS⟩ who = (boundaryValue S who : ℝ) := by
  rw [← quittingSetReward_of_nonempty boundaryReward hS,
    quittingSetReward_eq_boundaryValue]

/-! ## Two sign readings of the fifteen rows -/

theorem zero_le_boundaryValue_of_notMem :
    ∀ (S : Finset Player) (who : Player), who ∉ S → 0 ≤ boundaryValue S who := by
  decide

theorem boundaryValue_le_one_of_mem :
    ∀ (S : Finset Player) (who : Player), who ∈ S → boundaryValue S who ≤ 1 := by
  decide

/-- Every row pays each player outside the quitting coalition at least `0`. -/
theorem zero_le_boundaryReward_of_notMem (S : Finset Player) (hS : S.Nonempty)
    (who : Player) (hwho : who ∉ S) : 0 ≤ boundaryReward ⟨S, hS⟩ who := by
  rw [boundaryReward_eq_boundaryValue]
  exact_mod_cast zero_le_boundaryValue_of_notMem S who hwho

/-- Every row pays each member of the quitting coalition at most `1`. -/
theorem boundaryReward_le_one_of_mem (S : Finset Player) (hS : S.Nonempty)
    (who : Player) (hwho : who ∈ S) : boundaryReward ⟨S, hS⟩ who ≤ 1 := by
  rw [boundaryReward_eq_boundaryValue]
  exact_mod_cast boundaryValue_le_one_of_mem S who hwho

/-! ## The continue floor, the punishment value and the solo premium -/

/-- Every player's continue floor over the other three players is `0`. -/
theorem quittingContinueFloor_eq_zero (who : Player) :
    quittingContinueFloor boundaryReward who = 0 := by
  refine le_antisymm (quittingContinueFloor_nonpos boundaryReward who) ?_
  refine le_quittingBlockContinueFloor boundaryReward {who} who le_rfl ?_
  intro S hS hdisjoint
  exact zero_le_boundaryReward_of_notMem S hS who
    (Finset.disjoint_singleton_right.mp hdisjoint)

/-- Every player's punishment value is exactly `0`.  No player of this table
is join antitone, so the closed form is reached through the single pure exit
row of `quittingPunishmentValue_eq_continueFloor_of_pureRow`: the other three
players quitting at stage zero pays the deviator `0` for staying out and `-1`
for joining. -/
theorem quittingPunishmentValue_eq_zero (who : Player) :
    quittingPunishmentValue boundaryReward who = 0 := by
  have hcap := quittingPunishmentValue_le_pureRowCap boundaryReward who
    (Finset.univ.erase who)
  rw [Finset.insert_erase (Finset.mem_univ who), Finset.erase_idem,
    quittingSetReward_eq_boundaryValue,
    quittingSetReward_eq_boundaryValue] at hcap
  have hjoined : ∀ w : Player, boundaryValue Finset.univ w ≤ 0 := by decide
  have hstayed : ∀ w : Player,
      boundaryValue (Finset.univ.erase w) w ≤ 0 := by decide
  refine le_antisymm (hcap.trans (max_le ?_ ?_)) ?_
  · exact_mod_cast hjoined who
  · exact_mod_cast hstayed who
  · rw [← quittingContinueFloor_eq_zero who]
    exact quittingContinueFloor_le_quittingPunishmentValue boundaryReward who

/-- The solo premium of every player is exactly the table's margin `1`. -/
theorem soloPremium_eq_one (who : Player) :
    quittingSoloReward boundaryReward who who -
      quittingPunishmentValue boundaryReward who = 1 := by
  rw [quittingPunishmentValue_eq_zero, soloReward_self]
  norm_num

/-! ## The join cap -/

theorem crossPartner_ne (who : Player) : crossPartner who ≠ who := by
  revert who
  decide

/-- Every player's join cap over the other three players is exactly `1`. -/
theorem quittingBlockJoinCap_eq_one (who : Player) :
    quittingBlockJoinCap boundaryReward {who} who = 1 := by
  refine le_antisymm ?_ ?_
  · refine quittingBlockJoinCap_le boundaryReward {who} who zero_le_one ?_
    intro S hS hdisjoint
    have hnot : who ∉ S := Finset.disjoint_singleton_right.mp hdisjoint
    have hupper := boundaryReward_le_one_of_mem (insert who S)
      (Finset.insert_nonempty who S) who (Finset.mem_insert_self who S)
    have hlower := zero_le_boundaryReward_of_notMem S hS who hnot
    linarith
  · have hwitness := sub_le_quittingBlockJoinCap boundaryReward {who} who
      {crossPartner who} (Finset.singleton_nonempty _)
      (Finset.disjoint_singleton.mpr (crossPartner_ne who))
    have hgain : ∀ w : Player,
        boundaryValue (insert w {crossPartner w}) w -
          boundaryValue {crossPartner w} w = 1 := by decide
    rw [boundaryReward_eq_boundaryValue,
      boundaryReward_eq_boundaryValue] at hwitness
    have hcast : ((boundaryValue (insert who {crossPartner who}) who : ℝ) -
        (boundaryValue {crossPartner who} who : ℝ)) = 1 := by
      exact_mod_cast congrArg (fun n : ℤ => (n : ℝ)) (hgain who)
    linarith

/-! ## The deletion boundary -/

/-- The deletion excess bound of every player is exactly `absorptionBound + 1`;
in the vanishing-absorption limit it is exactly the margin `1`. -/
theorem quittingBlockDeletionExcessBound_eq (who : Player)
    (absorptionBound : ℝ) :
    quittingBlockDeletionExcessBound boundaryReward {who} who absorptionBound =
      absorptionBound + 1 := by
  unfold quittingBlockDeletionExcessBound
  rw [quittingBlockJoinCap_eq_one,
    show quittingBlockContinueFloor boundaryReward {who} who = 0 from
      quittingContinueFloor_eq_zero who,
    show boundaryReward (quittingSingletonTerminal who) who = 1 from
      soloReward_self who]
  norm_num

/-- The continue floor and the solo reward differ by exactly the margin `1`, so
the weak solo hypothesis shared by
`quittingGame_exists_uniformEquilibriumPayoff_of_le_continueFloor` and
`quittingGame_exists_uniformEquilibriumPayoff_of_vanishingAbsorption` fails by
exactly `1` at every player. -/
theorem continueFloor_add_one_eq_solo (who : Player) :
    quittingContinueFloor boundaryReward who + 1 =
      quittingSoloReward boundaryReward who who := by
  rw [quittingContinueFloor_eq_zero, soloReward_self]
  norm_num

/-- No player of this table is join antitone: the join cap is strictly
positive, so the join clause of the block dispensability gate fails at every
player. -/
theorem not_quittingBlockJoinAntitone (who : Player) :
    ¬ QuittingBlockJoinAntitone boundaryReward {who} who := by
  intro hjoin
  have hzero := quittingBlockJoinCap_eq_zero_of_blockJoinAntitone
    boundaryReward hjoin
  rw [quittingBlockJoinCap_eq_one] at hzero
  norm_num at hzero

/-- No player of this table is dispensable. -/
theorem not_quittingBlockDispensable (who : Player) :
    ¬ QuittingBlockDispensable boundaryReward {who} who := fun hgate =>
  not_quittingBlockJoinAntitone who hgate.1

/-! ## The three-player subgames -/

/-- The cross pair inside the subgame omitting a player. -/
def crossPair : Player → Finset Player := ![{1, 2}, {0, 3}, {1, 3}, {0, 2}]

/-- The cross pair read as a coalition of the survivor type. -/
def crossSurvivors (omitted : Player) :
    Finset (QuittingBlockSurvivor ({omitted} : Finset Player)) :=
  Finset.univ.filter (fun survivor => survivor.1 ∈ crossPair omitted)

theorem crossSurvivors_map (omitted : Player) :
    (crossSurvivors omitted).map
        (Function.Embedding.subtype
          (p := fun w : Player => w ∉ ({omitted} : Finset Player))) =
      crossPair omitted := by
  fin_cases omitted <;> decide

/-- The membership toggles of the original table at the survivors of
`omitted`, in the integer copy. -/
def IsBoundarySubgameSureExit (omitted : Player) (F : Finset Player) : Prop :=
  (∀ member ∈ F,
      boundaryValue (F.erase member) member ≤ boundaryValue F member) ∧
    ∀ outsider ∉ ({omitted} : Finset Player), outsider ∉ F →
      boundaryValue (insert outsider F) outsider ≤ boundaryValue F outsider

instance (omitted : Player) (F : Finset Player) :
    Decidable (IsBoundarySubgameSureExit omitted F) := by
  unfold IsBoundarySubgameSureExit
  infer_instance

theorem isQuittingSureExitSet_delete_iff_boundary (omitted : Player)
    (E : Finset (QuittingBlockSurvivor ({omitted} : Finset Player))) :
    IsQuittingSureExitSet (quittingDeleteBlockReward boundaryReward {omitted})
        E ↔
      IsBoundarySubgameSureExit omitted
        (E.map (Function.Embedding.subtype
          (p := fun w : Player => w ∉ ({omitted} : Finset Player)))) := by
  rw [isQuittingSureExitSet_deleteBlockReward_iff]
  unfold IsBoundarySubgameSureExit
  simp only [quittingSetReward_eq_boundaryValue, Int.cast_le]

/-- **Exactly one coalition of survivors exits surely, and it is the cross
pair.** -/
theorem isBoundarySubgameSureExit_iff_eq_crossPair :
    ∀ (omitted : Player) (F : Finset Player), omitted ∉ F →
      (IsBoundarySubgameSureExit omitted F ↔ F = crossPair omitted) := by
  decide

/-- **The unique sure exit set of each three-player subgame is a cross
pair.** -/
theorem isQuittingSureExitSet_deleteSingleton_iff (omitted : Player)
    (E : Finset (QuittingBlockSurvivor ({omitted} : Finset Player))) :
    IsQuittingSureExitSet (quittingDeleteBlockReward boundaryReward {omitted})
        E ↔
      E = crossSurvivors omitted := by
  have hnot : omitted ∉ E.map (Function.Embedding.subtype
      (p := fun w : Player => w ∉ ({omitted} : Finset Player))) := by
    intro hmem
    obtain ⟨survivor, -, hvalue⟩ := Finset.mem_map.mp hmem
    exact survivor.2 (by
      rw [show survivor.1 = omitted from hvalue]
      exact Finset.mem_singleton_self omitted)
  rw [isQuittingSureExitSet_delete_iff_boundary,
    isBoundarySubgameSureExit_iff_eq_crossPair omitted _ hnot]
  constructor
  · intro hmap
    exact Finset.map_injective _ (hmap.trans (crossSurvivors_map omitted).symm)
  · intro hE
    rw [hE]
    exact crossSurvivors_map omitted

/-- The omitted player's join gain against its subgame's sure exit is exactly
the margin `1`. -/
theorem omittedJoinGain_eq_one (omitted : Player) :
    quittingSetReward boundaryReward
        (insert omitted (crossPair omitted)) omitted -
      quittingSetReward boundaryReward (crossPair omitted) omitted = 1 := by
  rw [quittingSetReward_eq_boundaryValue, quittingSetReward_eq_boundaryValue]
  have hgain : ∀ w : Player,
      boundaryValue (insert w (crossPair w)) w -
        boundaryValue (crossPair w) w = 1 := by decide
  exact_mod_cast congrArg (fun n : ℤ => (n : ℝ)) (hgain omitted)

end SolanVieilleBoundary

end GameTheory
