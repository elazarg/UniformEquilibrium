/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegime.Circulant.ColliderCompletion
import UniformEquilibrium.Quitting.Classification.Circulant.ColliderCompletion

/-!
# One three-negative collider completion and its constant-step equilibrium

This file fixes the five-player collider completion of
`Research/Quitting/CirculantColliderCompletion.lean` at solo self value `1`,
joint value `-2`, and margin vector

`(m 1, m 2, m 3, m 4) = (-1, -1, -1, 10)`.

Distance four is the only nonzero distance of nonnegative margin and the margin
sum is `7`, so the table sits outside both the neighbour pocket `m 1 < 0`,
`m 4 < 0`, `0 ≤ m 2`, `0 ≤ m 3` and the nonpositive-sum branch.  No step has
both a nonnegative complementary and a nonnegative doubled complementary
margin, recorded here as `threeNegative_not_exists_nonneg_complement_pair`, so
the sign condition that only that pair supports does not reach the table.  The
firing step is instead the complement `4 * 4 = 1` of the single nonnegative
distance, whose doubled margin `m 2` is negative.

The witness is therefore the period-five single-quitter profile of constant
step one, in which player `k` quits at phase `k` with the same probability
`1 - q` at every phase, `q` being a root in `(0, 1)` of the step-one anchor
cubic `-1 - q - q² + 10 q³`.  The statements below quantify existentially over
the realized payoff rather than displaying it, since it depends on `q`.

This is a checked statement about one table, not a general theorem about
collider completions.  The general statement is
`GameTheory.CirculantColliderCompletion.isEmpty_terminalExploitabilityWitness_colliderThreeNegative`.
-/

noncomputable section

namespace GameTheory
namespace ColliderThreeNegativeEquilibrium

open CirculantConstantStepCycle CirculantColliderCompletion
open CirculantTrichotomyClosure

/-! ## The table -/

/-- The margin vector `(0, -1, -1, -1, 10)`. -/
def threeNegativeMargin : ZMod 5 → ℝ :=
  fun d => if d = 0 then 0 else if d = 4 then 10 else -1

@[simp] theorem threeNegativeMargin_zero : threeNegativeMargin 0 = 0 := by
  rw [threeNegativeMargin, if_pos rfl]

@[simp] theorem threeNegativeMargin_one : threeNegativeMargin 1 = -1 := by
  rw [threeNegativeMargin, if_neg (by decide), if_neg (by decide)]

@[simp] theorem threeNegativeMargin_two : threeNegativeMargin 2 = -1 := by
  rw [threeNegativeMargin, if_neg (by decide), if_neg (by decide)]

@[simp] theorem threeNegativeMargin_three : threeNegativeMargin 3 = -1 := by
  rw [threeNegativeMargin, if_neg (by decide), if_neg (by decide)]

@[simp] theorem threeNegativeMargin_four : threeNegativeMargin 4 = 10 := by
  rw [threeNegativeMargin, if_neg (by decide), if_pos rfl]

/-- The collider completion at solo self value `1`, joint value `-2`, and the
margin vector `threeNegativeMargin`. -/
def threeNegativeReward : {S : Finset (ZMod 5) // S.Nonempty} → Payoff (ZMod 5) :=
  colliderReward 1 (-2) threeNegativeMargin

/-! ## The sign data -/

/-- The margin sum of the table is `7`. -/
theorem sum_threeNegativeMargin : (∑ e, threeNegativeMargin e) = 7 := by
  rw [show (∑ e : ZMod 5, threeNegativeMargin e) =
      threeNegativeMargin 0 + threeNegativeMargin 1 + threeNegativeMargin 2 +
        threeNegativeMargin 3 + threeNegativeMargin 4 from
    Fin.sum_univ_five (fun e : ZMod 5 => threeNegativeMargin e)]
  norm_num

/-- Distance four is the only nonzero distance of nonnegative margin. -/
theorem threeNegativeMargin_neg_of_ne (e : ZMod 5) (h0 : e ≠ 0) (h4 : e ≠ 4) :
    threeNegativeMargin e < 0 := by
  rcases zmod_five_cases e with h | h | h | h | h <;> subst h
  · exact absurd rfl h0
  · norm_num
  · norm_num
  · norm_num
  · exact absurd rfl h4

/-- **The step-one cycle fires.**  Step one is the complement `4 * 4` of the
single nonnegative distance: its own margin and its doubled margin `m 2` are
negative and its complementary margin is `m 4`. -/
theorem threeNegative_isFiringStep_one : IsFiringStep threeNegativeMargin 1 :=
  isFiringStep_one (by norm_num) (by norm_num) (Or.inr (by norm_num))

/-- **No step carries both nonnegative complementary margins.**  The sign
condition supported by the complementary and doubled complementary margins
alone does not reach this table. -/
theorem threeNegative_not_exists_nonneg_complement_pair :
    ¬ ∃ c : ZMod 5, c ≠ 0 ∧ threeNegativeMargin c < 0 ∧
      0 ≤ threeNegativeMargin (4 * c) ∧ 0 ≤ threeNegativeMargin (3 * c) :=
  not_exists_nonneg_complement_pair_of_unique_nonneg (g := 4)
    threeNegativeMargin_neg_of_ne

/-! ## The headline -/

/-- **The table has a uniform-equilibrium payoff.**  The witness is the
period-five single-quitter profile of constant step one at a uniform quit
probability; the deviation class is all behavior strategies, not stopping
times. -/
theorem threeNegative_exists_uniformEquilibriumPayoff :
    ∃ payoff : Payoff (ZMod 5),
      (quittingGame threeNegativeReward).IsUniformEquilibriumPayoff none payoff :=
  exists_uniformEquilibriumPayoff_of_unique_nonneg
    (isCirculantPairTable_colliderReward 1 (-2) threeNegativeMargin
      threeNegativeMargin_zero)
    (by norm_num) (by rw [sum_threeNegativeMargin]; norm_num) (g := 4)
    (by norm_num) threeNegativeMargin_neg_of_ne
    (fun d _ => colliderJoin_nonpos (by norm_num) d)

/-- **The table is in no terminal exploitability witness.**  A terminal exploitability
gap is incompatible with an existing uniform-equilibrium payoff. -/
theorem threeNegative_isEmpty_terminalExploitabilityWitness :
    IsEmpty (QuittingTerminalExploitabilityWitness threeNegativeReward) :=
  isEmpty_terminalExploitabilityWitness_colliderThreeNegative threeNegativeMargin_zero
    (by norm_num) (by norm_num)
    (by rw [sum_threeNegativeMargin]; norm_num) (g := 4) (by norm_num)
    threeNegativeMargin_neg_of_ne

end ColliderThreeNegativeEquilibrium
end GameTheory
