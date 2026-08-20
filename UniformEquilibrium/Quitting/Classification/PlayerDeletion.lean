/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Mathlib.Data.Fintype.Card

/-!
# Deleting one player from a finite player type

This module owns the complement subtype used when a quitting-game argument
deletes one distinguished player, together with its exact elementary
cardinality laws.  The construction is independent of a reward table,
counterexample regime, or deletion semantics.
-/

namespace GameTheory

/-- The subtype of players remaining after deleting `owner`. -/
abbrev QuittingDeletedPlayer {ι : Type} (owner : ι) := {who : ι // who ≠ owner}

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Deleting a player strictly decreases a nonempty finite player type. -/
theorem card_quittingDeletedPlayer_lt (owner : ι) :
    Fintype.card (QuittingDeletedPlayer owner) < Fintype.card ι := by
  exact Fintype.card_subtype_lt (p := fun who : ι => who ≠ owner)
    (x := owner) (by simp)

/-- Deleting one player from a four-player type leaves exactly three
players. -/
theorem card_quittingDeletedPlayer_eq_three_of_card_eq_four
    (owner : ι) (hcard : Fintype.card ι = 4) :
    Fintype.card (QuittingDeletedPlayer owner) = 3 := by
  rw [Fintype.card_subtype_compl (fun who : ι => who = owner)]
  simp [hcard]

end GameTheory
