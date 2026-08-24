/-
Copyright (c) 2026 UniformEquilibrium contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: UniformEquilibrium contributors
-/

import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.IntervalCases

/-!
# Finite support-status enumeration on a four-player persistent face

A binary mixed strategy has three support statuses: pure Continue, pure Quit,
or genuine mixing.  Hence a free face with at most three players has at most
`3^3 = 27` status cells.  This is only the finite enumeration statement; the
semantic compiler is kept in separate modules.
-/

namespace GameTheory

/-- The three support statuses of one binary mixed action: the values encode
pure Continue, pure Quit, and genuine mixing, respectively. -/
abbrev QuittingBinarySupportStatus := Fin 3

/-- All support-status cells on a finite free-player face. -/
def quittingBinarySupportStatusCells {ι : Type} [DecidableEq ι]
    (free : Finset ι) : Finset (free → QuittingBinarySupportStatus) :=
  Finset.univ

@[simp] theorem card_quittingBinarySupportStatusCells {ι : Type}
    [DecidableEq ι] (free : Finset ι) :
    (quittingBinarySupportStatusCells free).card = 3 ^ free.card := by
  simp [quittingBinarySupportStatusCells]

/-- A free face of cardinality at most three has at most twenty-seven exact
support-status cells. -/
theorem card_quittingBinarySupportStatusCells_le_twentySeven {ι : Type}
    [DecidableEq ι] (free : Finset ι) (hcard : free.card ≤ 3) :
    (quittingBinarySupportStatusCells free).card ≤ 27 := by
  rw [card_quittingBinarySupportStatusCells]
  interval_cases free.card <;> norm_num

/-- Every status assignment is one of the enumerated cells. -/
theorem mem_quittingBinarySupportStatusCells {ι : Type} [DecidableEq ι]
    (free : Finset ι) (status : free → QuittingBinarySupportStatus) :
    status ∈ quittingBinarySupportStatusCells free := by
  simp [quittingBinarySupportStatusCells]

end GameTheory
