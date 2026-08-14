/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Basic
import MathUE.LinearProgramming.SingletonLCP

/-!
# Quitting-reward adapter for the normalized singleton LCP

This module instantiates the game-independent normalized singleton LCP with a
finite quitting reward. The comparison matrix

`B i j = reward {j} i - reward {i} i`

measures player `i`'s payoff from player `j` quitting alone relative to
player `i` quitting alone.
-/

noncomputable section

namespace GameTheory
namespace QuittingLCPClassification

open Math.LinearProgramming

variable {ι : Type} [Fintype ι]

/-- The singleton comparison matrix of a quitting reward: the `(i, j)` entry
is player `i`'s payoff when `j` solo-terminates minus player `i`'s payoff
when `i` itself solo-terminates. -/
def quittingSingletonMatrix
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (i j : ι) : ℝ :=
  reward ⟨{j}, Finset.singleton_nonempty j⟩ i -
    reward ⟨{i}, Finset.singleton_nonempty i⟩ i

/-- **The normalized singleton LCP of a quitting reward.** Feasibility of the
singleton LCP for the reward's comparison matrix `quittingSingletonMatrix`. -/
def quittingSingletonLCPFeasible
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) : Prop :=
  SingletonLCPFeasible (quittingSingletonMatrix reward)

/-- Unfolding lemma: the game-facing predicate is exactly the singleton LCP
of the comparison matrix, spelled out in full. -/
theorem quittingSingletonLCPFeasible_iff
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) :
    quittingSingletonLCPFeasible reward ↔
      ∃ lam : stdSimplex ℝ ι,
        (∀ i, 0 ≤ singletonLCPResidual (quittingSingletonMatrix reward) lam i) ∧
        ∀ i, lam.val i * singletonLCPResidual (quittingSingletonMatrix reward) lam i = 0 :=
  Iff.rfl

end QuittingLCPClassification
end GameTheory
