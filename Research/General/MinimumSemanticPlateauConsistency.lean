/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Root.TerminalSemanticPair

/-!
# Abstract consistency of the all-Continue semantic plateau

This probe isolates an important falsification boundary.  The finite-dimensional
equations of an all-Continue, positive-debt semantic fixed point impose no
restriction on a quitting reward table by themselves: every table admits such
an *abstract* pair.  The substantive hypothesis in the minimum-semantic-debt
argument is membership in the closure of executable terminal semantic pairs.

Consequently a counterexample search must test carrier realizability (or a
sound finite consequence of it).  Rejecting an abstract prescribed/envelope
pair merely because its debt is positive would be unsound.
-/

noncomputable section

namespace GameTheory

open Math.Probability

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- All-Continue is an exact root Nash action whenever the declared tail
dominates every owner's immediate singleton reward. -/
theorem isZeroQuittingRootNash_allContinue_of_singleton_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : Payoff ι)
    (hsingleton : ∀ who,
      reward (quittingSingletonTerminal who) who ≤ tail who) :
    IsεQuittingRootNash reward tail 0
      (quittingAllContinueRoot : ι → PMF Bool) := by
  rw [← isεQuittingRootEndpointNash_iff_isεQuittingRootNash]
  intro who
  constructor
  · rw [quittingRootEndpointDifference_allContinueRoot]
    have hcontinue :
        ((quittingAllContinueRoot who) false).toReal = 1 := by
      simp [quittingAllContinueRoot]
    rw [hcontinue, one_mul]
    exact sub_nonpos.mpr (hsingleton who)
  · simp [quittingAllContinueRoot]

/-- An all-Continue prefix fixes any abstract semantic pair whose envelope
coordinate dominates immediate singleton rewards.  The prescribed coordinate
is unchanged without an inequality. -/
theorem quittingTerminalSemanticPrefix_allContinue_eq_self
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (pair : QuittingTerminalSemanticPair ι)
    (henvelope : ∀ who,
      reward (quittingSingletonTerminal who) who ≤ pair.2 who) :
    quittingTerminalSemanticPrefix reward
        (quittingAllContinueRoot : ι → PMF Bool) pair = pair := by
  apply Prod.ext
  · funext who
    unfold quittingTerminalSemanticPrefix
    dsimp only
    rw [quittingRootSuccessorPayoff_eq_endpointMix]
    simp [quittingAllContinueRoot]
  · funext who
    simp [quittingTerminalSemanticPrefix, henvelope who]

/-- Every reward table has an abstract all-Continue semantic fixed point with
unit debt in every coordinate.  No carrier-membership claim is made. -/
theorem exists_abstract_allContinue_unitDebt_semanticPlateau
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) :
    ∃ pair : QuittingTerminalSemanticPair ι,
      IsεQuittingRootNash reward pair.1 0
        (quittingAllContinueRoot : ι → PMF Bool) ∧
      quittingTerminalSemanticPrefix reward
          (quittingAllContinueRoot : ι → PMF Bool) pair = pair ∧
      ∀ who, quittingTerminalSemanticDebt pair who = 1 := by
  let solo : Payoff ι :=
    fun who => reward (quittingSingletonTerminal who) who
  let pair : QuittingTerminalSemanticPair ι :=
    (solo, fun who => solo who + 1)
  refine ⟨pair,
    isZeroQuittingRootNash_allContinue_of_singleton_le reward solo
      (fun who => le_rfl), ?_, ?_⟩
  · apply quittingTerminalSemanticPrefix_allContinue_eq_self reward pair
    intro who
    dsimp [pair, solo]
    linarith
  · intro who
    simp [quittingTerminalSemanticDebt, pair]

end GameTheory
