/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Classification.Circulant.TerminalExploitabilityColliderCompletion
import UniformEquilibrium.Quitting.Classification.Circulant.ColliderCompletion

/-!
# A neighbour-pocket table that is not a collider completion

`Research/Quitting/CirculantTrichotomyClosure.lean` closes the neighbour
pocket of *any* five-player rotation-symmetric pair table whose join margins
are capped, and its collider specialization in
`Research/Quitting/CirculantColliderCompletion.lean` is only one instance of
that.  This file exercises the general theorem on a table outside the collider
family.

The table is *flat*: every joint exit pays its members the joint value `-1`
and its outsiders zero, with no collider exception.  Its solo self value is
`1`, its margin vector is

`(m 1, m 2, m 3, m 4) = (-1, 3, 2, -3)`,

and every join margin is `-2`.

Three facts place it exactly where the general theorem is needed.

* The margins are in the neighbour pocket — `m 1 < 0`, `m 4 < 0`, `0 ≤ m 2`,
  `0 ≤ m 3`, margin sum `1 > 0` — so no step fires in the sense of
  `GameTheory.CirculantTrichotomyClosure.IsFiringStep`, recorded below as
  `flat_not_exists_isFiringStep`.
* Only one of the pocket's two cap pairs holds.  The step-four caps read
  `-2 ≤ -1` at distances one and two and hold; the step-one caps would read
  `-2 ≤ -3` at distances three and four and fail.  So the step-four cycle of
  `exists_uniformEquilibriumPayoff_of_neighbourPocket` is the producer, and
  `exists_uniformEquilibriumPayoff_of_neighbourPocket_stepOne` is unavailable.
* The table is not the collider completion of its own margins: at the collider
  pair `{y - 1, y}` it pays `y` the joint value `-1`, where the collider
  completion pays the solo self value `1`.  That is
  `flatReward_ne_colliderReward`.

This is a checked statement about one table, not a general theorem.  The
general statement is
`GameTheory.CirculantTrichotomyClosure.exists_uniformEquilibriumPayoff_of_neighbourPocket`.
-/

noncomputable section

namespace GameTheory
namespace FlatNeighbourPocketEquilibrium

open CirculantConstantStepCycle CirculantTrichotomyClosure
open CirculantColliderCompletion

/-! ## The table -/

/-- The margin vector `(0, -1, 3, 2, -3)`. -/
def flatMargin : ZMod 5 → ℝ :=
  fun d =>
    if d = 1 then -1
    else if d = 2 then 3
    else if d = 3 then 2
    else if d = 4 then -3
    else 0

@[simp] theorem flatMargin_zero : flatMargin 0 = 0 := by
  rw [flatMargin, if_neg (by decide), if_neg (by decide), if_neg (by decide),
    if_neg (by decide)]

@[simp] theorem flatMargin_one : flatMargin 1 = -1 := by
  rw [flatMargin, if_pos rfl]

@[simp] theorem flatMargin_two : flatMargin 2 = 3 := by
  rw [flatMargin, if_neg (by decide), if_pos rfl]

@[simp] theorem flatMargin_three : flatMargin 3 = 2 := by
  rw [flatMargin, if_neg (by decide), if_neg (by decide), if_pos rfl]

@[simp] theorem flatMargin_four : flatMargin 4 = -3 := by
  rw [flatMargin, if_neg (by decide), if_neg (by decide), if_neg (by decide),
    if_pos rfl]

theorem sum_flatMargin : (∑ e : ZMod 5, flatMargin e) = 1 := by
  rw [show (∑ e : ZMod 5, flatMargin e) =
    flatMargin 0 + flatMargin 1 + flatMargin 2 + flatMargin 3 + flatMargin 4 from
      Fin.sum_univ_five (fun e : ZMod 5 => flatMargin e)]
  norm_num

/-- The flat completion: singleton rows are the circulant rows of
`flatMargin` around the solo self value `1`, every larger coalition pays its
members `-1`, and outsiders are paid zero. -/
def flatReward : {S : Finset (ZMod 5) // S.Nonempty} → Payoff (ZMod 5) :=
  fun S who =>
    if S.1.card = 1 then 1 + ∑ owner ∈ S.1, flatMargin (owner - who)
    else if who ∈ S.1 then -1 else 0

/-- Every join margin of the flat completion is `-2`. -/
def flatJoin : ZMod 5 → ℝ := fun _ => -2

@[simp] theorem flatReward_singleton (owner who : ZMod 5) :
    flatReward (quittingSingletonTerminal owner) who = 1 + flatMargin (owner - who) := by
  rw [flatReward, if_pos (by simp [quittingSingletonTerminal])]
  simp [quittingSingletonTerminal]

theorem flatReward_pair {owner who : ZMod 5} (hne : owner ≠ who) :
    flatReward ⟨{owner, who}, Finset.insert_nonempty owner {who}⟩ who =
      1 + flatJoin (owner - who) := by
  have hcard : ¬ (({owner, who} : Finset (ZMod 5)).card = 1) := by
    revert hne
    revert owner who
    decide
  rw [flatReward, if_neg hcard, if_pos (by simp), flatJoin]
  norm_num

theorem isCirculantPairTable_flatReward :
    IsCirculantPairTable flatReward 1 flatMargin flatJoin :=
  ⟨flatMargin_zero, flatReward_singleton, fun _ _ hne ↦ flatReward_pair hne⟩

/-! ## Where the table sits -/

/-- The margins are a complementary pocket on the neighbour distances. -/
theorem flat_isComplementaryPocketMargin : IsComplementaryPocketMargin flatMargin :=
  isComplementaryPocketMargin_one (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)

/-- No step fires, so the firing-step branch of the trichotomy is unavailable
and the pocket producer is the only one that reaches this table. -/
theorem flat_not_exists_isFiringStep : ¬ ∃ c : ZMod 5, IsFiringStep flatMargin c :=
  not_isFiringStep_of_isComplementaryPocketMargin flat_isComplementaryPocketMargin

/-- The second cap pair of the neighbour pocket fails: the join margin at
distance three exceeds `m 4`, so the step-one cycle is blocked. -/
theorem flat_not_stepOne_cap : ¬ flatJoin 3 ≤ flatMargin 4 := by
  rw [flatJoin, flatMargin_four]
  norm_num

/-- The table is not the collider completion of its own margins: the collider
completion pays a player its solo self value when it quits with exactly its
predecessor, and this table pays the joint value there. -/
theorem flatReward_ne_colliderReward :
    flatReward ≠ colliderReward 1 (-1) flatMargin := by
  intro hcontra
  have hcollider := colliderReward_collider 1 (-1) flatMargin 0
  rw [← hcontra] at hcollider
  have hflat : flatReward ⟨{(0 : ZMod 5) - 1, 0},
      Finset.insert_nonempty ((0 : ZMod 5) - 1) {0}⟩ 0 = -1 := by
    rw [flatReward, if_neg (by decide), if_pos (by decide)]
  rw [hflat] at hcollider
  norm_num at hcollider

/-! ## The equilibrium -/

/-- **The flat neighbour-pocket table has a uniform-equilibrium payoff.**  It
is produced by the step-four cycle of the general neighbour-pocket theorem,
consumed here on a table outside the collider family. -/
theorem flat_exists_uniformEquilibriumPayoff :
    ∃ payoff : Payoff (ZMod 5),
      (quittingGame flatReward).IsUniformEquilibriumPayoff none payoff :=
  exists_uniformEquilibriumPayoff_of_neighbourPocket isCirculantPairTable_flatReward
    zero_le_one (by norm_num) (by norm_num) (by norm_num)
    (by rw [sum_flatMargin]; norm_num)
    (by rw [flatJoin]; norm_num) (by rw [flatJoin]; norm_num)
    (by rw [flatJoin, flatMargin_one]; norm_num)
    (by rw [flatJoin, flatMargin_one]; norm_num)

/-- The table carries no terminal exploitability witness. -/
theorem flat_isEmpty_terminalExploitabilityWitness :
    IsEmpty (QuittingTerminalExploitabilityWitness flatReward) :=
  ⟨fun witness => witness.not_exists_uniformEquilibriumPayoff
    flat_exists_uniformEquilibriumPayoff⟩

end FlatNeighbourPocketEquilibrium
end GameTheory
