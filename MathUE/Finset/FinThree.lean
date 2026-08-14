/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Mathlib.Data.Fintype.Powerset
import Mathlib.Tactic.FinCases

/-!
# Finsets on three elements

Small, reusable classification facts for subsets of `Fin 3`.
-/

namespace Math.Finset

/-- Every nonempty subset of `Fin 3` is one of its seven explicit subsets. -/
theorem nonempty_fin_three_cases (S : Finset (Fin 3)) (hS : S.Nonempty) :
    S = {0} ∨ S = {1} ∨ S = {2} ∨ S = {0, 1} ∨
      S = {0, 2} ∨ S = {1, 2} ∨ S = {0, 1, 2} := by
  fin_cases S <;> simp_all <;> decide

end Math.Finset
