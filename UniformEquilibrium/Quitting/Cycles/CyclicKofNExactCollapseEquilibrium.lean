/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Cycles.CyclicKofNExactCollapseSchedule
import UniformEquilibrium.Quitting.Cycles.CyclicKofNBellmanBridge

/-!
# Uniform-equilibrium compiler for exact-collapse `K/N` clocks

The arithmetic construction realizes every admissible collapse factor
`d ∣ gcd(K,N)`.  The periodic Bellman bridge says that the remaining task is
finite and payoff-specific: provide one exact Nash--Bellman edge per distinct
translated block, with successor states closing around the orbit.

This file specializes that bridge to the explicit primitive-block/fiber
construction. The playerwise contraction required by the periodic compiler
is automatic from positive common hazard, including the sure-Quit boundary;
it is not an additional certificate premise.
-/

namespace GameTheory

namespace CyclicKofNExactCollapseEquilibrium

open StochasticGame Math.Probability Math.PMFProduct
open Math.CyclicKofNArithmetic CyclicKofNQuittingSchedule
  Math.CyclicKofNPrimitiveBlocks CyclicKofNExactCollapseSchedule
  CyclicKofNBellmanBridge
open scoped Pointwise

noncomputable section

/-- **Exact-collapse cyclic equilibrium compiler.**  For the explicit block
with `K = k*d`, `N = n*d`, and period `n`, a state-matched finite cycle of
exact Nash--Bellman edges yields a uniform-equilibrium payoff of the original
quitting game. -/
theorem isUniformEquilibriumPayoff_of_exactCollapseNashBellmanCycle
    {n k d : ℕ} [NeZero n] [NeZero d]
    (hkpos : 0 < k) (hkproper : k < n)
    (reward :
      {S : Finset (ZMod n × ZMod d) // S.Nonempty} →
        Payoff (ZMod n × ZMod d))
    (β : ℝ) (hβpos : 0 < β) (hβ1 : β ≤ 1)
    (point : Fin (Fintype.card
      (TranslationPhase (exactCollapseBlock n k d))) →
        QuittingNashBellmanPoint (ZMod n × ZMod d))
    (initial : Fin (Fintype.card
      (TranslationPhase (exactCollapseBlock n k d))))
    (hroot : ∀ phase, quittingRootOfSimplex (point phase).2 =
      cyclicPhaseRoots (exactCollapseBlock n k d)
        β hβpos.le hβ1 phase)
    (hedge : ∀ phase, IsQuittingNashBellmanEdge reward
      (point phase)
      (point (finRotate
        (Fintype.card (TranslationPhase (exactCollapseBlock n k d)))
        phase))) :
    (quittingGame reward).IsUniformEquilibriumPayoff none
      (point initial).1 := by
  have hA : (exactCollapseBlock n k d).Nonempty := by
    apply Finset.card_pos.mp
    rw [card_exactCollapseBlock hkproper.le]
    exact Nat.mul_pos hkpos (NeZero.pos d)
  have hnTwo : 1 < n := by omega
  have hpopulation : 1 < Fintype.card (ZMod n × ZMod d) := by
    rw [card_exactCollapsePopulation]
    exact hnTwo.trans_le (Nat.le_mul_of_pos_right n (NeZero.pos d))
  exact isUniformEquilibriumPayoff_of_cyclicNashBellmanCycle
    reward (exactCollapseBlock n k d) hA hpopulation
      β hβpos hβ1 point initial hroot hedge

/-- Its root word has exact stage support `k*d` and ambient population
`n*d`, making the `K/N` parameters explicit next to the equilibrium
compiler. -/
theorem exactCollapse_equilibriumCertificate_parameters
    {n k d : ℕ} [NeZero n] [NeZero d]
    (hkpos : 0 < k) (hkproper : k < n) :
    (exactCollapseBlock n k d).card = k * d ∧
    Fintype.card (ZMod n × ZMod d) = n * d ∧
    Fintype.card (TranslationPhase (exactCollapseBlock n k d)) = n ∧
    Fintype.card
      (AddAction.stabilizer (ZMod n × ZMod d)
        (exactCollapseBlock n k d)) = d := by
  exact ⟨card_exactCollapseBlock hkproper.le,
    card_exactCollapsePopulation n d,
    card_translationPhase_exactCollapseBlock hkpos hkproper,
    card_stabilizer_exactCollapseBlock hkpos hkproper⟩

end

end CyclicKofNExactCollapseEquilibrium

end GameTheory
