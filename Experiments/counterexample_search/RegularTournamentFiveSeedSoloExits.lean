/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Experiments.counterexample_search.RegularTournamentFiveSeedSureExit

/-!
# The seed's nonzero uniform-equilibrium payoffs

`Experiments/counterexample_search/RegularTournamentFiveSeedSureExit.lean`
proves that the four solo exits `{i}`, `i ≠ 0`, are sure exit sets of the
literal seed table, and reads off the grand coalition's zero payoff as a
uniform-equilibrium payoff.  This module reads off the other four targets the
same producer
(`isUniformEquilibriumPayoff_setReward_of_isQuittingSureExitSet`) delivers.

The solo exit `{owner}` pays `1 + M who owner`, where `M` is the tournament
matrix `2 A - Aᵀ`, so the payoff vector is the matrix column shifted by one:

| exit  | payoff vector       |
| ----- | ------------------- |
| `{1}` | `(3, 1, 0, 0, 3)`   |
| `{2}` | `(3, 3, 1, 0, 0)`   |
| `{3}` | `(0, 3, 3, 1, 0)`   |
| `{4}` | `(0, 0, 3, 3, 1)`   |

These are nonzero targets, unlike the grand coalition's zero payoff.  The
realized game therefore sits well inside the equilibrium region rather than
at its boundary, which reinforces the reading of the seed as a calibration of
the singleton geometry and not as a counterexample candidate.

## A broken cyclic orbit

The four vectors are successive cyclic shifts of one another, as the five-fold
rotational symmetry of the regular tournament matrix predicts: shifting
`(3, 1, 0, 0, 3)` one coordinate to the right gives `(3, 3, 1, 0, 0)`, then
`(0, 3, 3, 1, 0)`, then `(0, 0, 3, 3, 1)`.  One more shift gives
`(1, 0, 0, 3, 3)`, which is player zero's singleton row and closes the orbit,
and that is exactly the vector this module does not list:
`isQuittingSureExitSet_singleton_of_ne_zero` excludes the owner `0`, because
the zero completion of the seed breaks the rotational symmetry at the
completion vertex.  Whether `(1, 0, 0, 3, 3)` is a uniform-equilibrium payoff
of the realized seed by some route other than a sure exit set is not settled
here; the anchored cyclic route is answered in
`Experiments/counterexample_search/RegularTournamentFiveSeedZeroOrbitGap.lean`.

## Inventory note

The checked inventory `isQuittingSureExitSet_iff` gives exactly twenty sure
exit sets: the ten triples, the five quadruples, the grand coalition, and
these four solo exits.

## Scope

Every statement here is about the one literal zero-completed table of
`RegularTournamentFiveSeed.lean`.  No claim is made about other completions
of the same singleton geometry, and none of the seed's geometry theorems is
affected.

## Reproduction

This module can be checked independently with Lean.
-/

namespace GameTheory
namespace RegularTournamentFiveSeed

open Finset QuittingSureSetOwnerRepair Math.LinearProgramming

/-! ## The four solo exit payoffs -/

/-- **A solo exit target.**  For any owner other than player zero, that
player's singleton row is a uniform-equilibrium payoff of the realized
game. -/
theorem isUniformEquilibriumPayoff_setReward_singleton {owner : Player}
    (howner : owner ≠ 0) :
    (quittingGame reward).IsUniformEquilibriumPayoff none
      (quittingSetReward reward ({owner} : Finset Player)) :=
  isUniformEquilibriumPayoff_setReward_of_isQuittingSureExitSet reward
    (isQuittingSureExitSet_singleton_of_ne_zero howner)

theorem setReward_singleton_one :
    quittingSetReward reward ({1} : Finset Player) = ![3, 1, 0, 0, 3] := by
  funext who
  rw [setReward_singleton, singletonMatrix_entries]
  fin_cases who <;>
    norm_num [Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
      Matrix.tail_cons, Matrix.head_cons]

theorem setReward_singleton_two :
    quittingSetReward reward ({2} : Finset Player) = ![3, 3, 1, 0, 0] := by
  funext who
  rw [setReward_singleton, singletonMatrix_entries]
  fin_cases who <;>
    norm_num [Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
      Matrix.tail_cons, Matrix.head_cons]

theorem setReward_singleton_three :
    quittingSetReward reward ({3} : Finset Player) = ![0, 3, 3, 1, 0] := by
  funext who
  rw [setReward_singleton, singletonMatrix_entries]
  fin_cases who <;>
    norm_num [Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
      Matrix.tail_cons, Matrix.head_cons]

theorem setReward_singleton_four :
    quittingSetReward reward ({4} : Finset Player) = ![0, 0, 3, 3, 1] := by
  funext who
  rw [setReward_singleton, singletonMatrix_entries]
  fin_cases who <;>
    norm_num [Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
      Matrix.tail_cons, Matrix.head_cons]

theorem isUniformEquilibriumPayoff_solo_one :
    (quittingGame reward).IsUniformEquilibriumPayoff none ![3, 1, 0, 0, 3] := by
  rw [← setReward_singleton_one]
  exact isUniformEquilibriumPayoff_setReward_singleton (by decide)

theorem isUniformEquilibriumPayoff_solo_two :
    (quittingGame reward).IsUniformEquilibriumPayoff none ![3, 3, 1, 0, 0] := by
  rw [← setReward_singleton_two]
  exact isUniformEquilibriumPayoff_setReward_singleton (by decide)

theorem isUniformEquilibriumPayoff_solo_three :
    (quittingGame reward).IsUniformEquilibriumPayoff none ![0, 3, 3, 1, 0] := by
  rw [← setReward_singleton_three]
  exact isUniformEquilibriumPayoff_setReward_singleton (by decide)

theorem isUniformEquilibriumPayoff_solo_four :
    (quittingGame reward).IsUniformEquilibriumPayoff none ![0, 0, 3, 3, 1] := by
  rw [← setReward_singleton_four]
  exact isUniformEquilibriumPayoff_setReward_singleton (by decide)

/-! ## The headline -/

/-- **A nonzero uniform-equilibrium payoff.**  Player one's solo exit pays
`(3, 1, 0, 0, 3)`, so the realized game's uniform-equilibrium payoff set is
not the single zero target of the grand-coalition exit. -/
theorem exists_ne_zero_isUniformEquilibriumPayoff :
    ∃ value : Payoff Player, value ≠ 0 ∧
      (quittingGame reward).IsUniformEquilibriumPayoff none value := by
  refine ⟨![3, 1, 0, 0, 3], fun hzero ↦ ?_, isUniformEquilibriumPayoff_solo_one⟩
  have hone := congrFun hzero 1
  norm_num at hone

end RegularTournamentFiveSeed
end GameTheory
