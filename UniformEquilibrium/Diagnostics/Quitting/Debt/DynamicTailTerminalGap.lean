/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.Chronology.PositiveDebtDynamicTailWitness
import UniformEquilibrium.Quitting.Chronology.SummableExactTailTerminalGap

/-!
# Terminal gap of the canonical positive-debt dynamic tail

The optimized dynamic-debt tail extracted from a terminal-exploitability
witness is a literal instance of the general summable exact-value-tail
interface.  Consequently its late executable suffixes deliver zero while
their unrestricted behavioral best-response values converge to the positive
parts of the singleton self-payoffs.
-/

noncomputable section

namespace GameTheory

open Filter Math.Probability

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
variable {witness : QuittingTerminalExploitabilityWitness reward}

namespace QuittingPositiveDebtDynamicTailWitness

/-- Canonical adapter to the general summable exact-value-tail semantics. -/
def toSummableExactValueTail
    (seam : QuittingPositiveDebtDynamicTailWitness witness) :
    QuittingSummableExactValueTail reward where
  roots := quittingDynamicDebtTailRoots seam.tail
  value := fun time ↦ (seam.tail time).1.1
  boundary := seam.limit.value
  bellman := fun time ↦ (seam.tail_edge time).1.1
  value_tendsto := seam.value_tendsto
  absorption_summable := seam.jointAbsorption_summable

/-- The unrestricted behavioral best-response value against canonical late
suffixes converges coordinatewise to the positive singleton payoff. -/
theorem suffixBestResponseValue_tendsto_max_solo
    (seam : QuittingPositiveDebtDynamicTailWitness witness) (who : ι) :
    Tendsto (fun start ↦ quittingContinuationBestResponseValue reward
      (quittingRootSequenceProfile reward
        (quittingDynamicDebtTailRoots seam.tail) start) who) atTop
      (nhds (max 0 (reward (quittingSingletonTerminal who) who))) := by
  simpa [toSummableExactValueTail,
    QuittingSummableExactValueTail.suffixBestResponseValue,
    QuittingSummableExactValueTail.suffixProfile] using
    seam.toSummableExactValueTail.suffixBestResponseValue_tendsto_max_solo who

/-- The canonical late suffix's unrestricted positive unilateral gain has
the same exact singleton limit. -/
theorem suffixGain_tendsto_max_solo
    (seam : QuittingPositiveDebtDynamicTailWitness witness) (who : ι) :
    Tendsto (fun start ↦ max 0
      (quittingContinuationBestResponseValue reward
          (quittingRootSequenceProfile reward
            (quittingDynamicDebtTailRoots seam.tail) start) who -
        quittingTerminalPayoff reward
          (quittingRootSequenceProfile reward
            (quittingDynamicDebtTailRoots seam.tail) start) who)) atTop
      (nhds (max 0 (reward (quittingSingletonTerminal who) who))) := by
  simpa [toSummableExactValueTail,
    QuittingSummableExactValueTail.suffixGain,
    QuittingSummableExactValueTail.suffixBestResponseValue,
    QuittingSummableExactValueTail.suffixProfile] using
    seam.toSummableExactValueTail.suffixGain_tendsto_max_solo who

/-- On a no-uniform-payoff branch, some literal singleton self-payoff is
strictly positive and the corresponding canonical suffix exploitability
converges to that positive number. -/
theorem exists_positiveSolo_suffixGain_tendsto_of_no_uniformPayoff
    [Nonempty ι]
    (seam : QuittingPositiveDebtDynamicTailWitness witness)
    (hnoUE : ¬ ∃ payoff : Payoff ι,
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff) :
    ∃ who,
      0 < reward (quittingSingletonTerminal who) who ∧
      Tendsto (fun start ↦ max 0
        (quittingContinuationBestResponseValue reward
            (quittingRootSequenceProfile reward
              (quittingDynamicDebtTailRoots seam.tail) start) who -
          quittingTerminalPayoff reward
            (quittingRootSequenceProfile reward
              (quittingDynamicDebtTailRoots seam.tail) start) who)) atTop
        (nhds (reward (quittingSingletonTerminal who) who)) := by
  by_cases hpositive : ∃ who,
      0 < reward (quittingSingletonTerminal who) who
  · obtain ⟨who, hwho⟩ := hpositive
    refine ⟨who, hwho, ?_⟩
    simpa [max_eq_right hwho.le] using seam.suffixGain_tendsto_max_solo who
  · have hsolo : ∀ who,
        reward (quittingSingletonTerminal who) who ≤ 0 := by
      intro who
      exact le_of_not_gt fun hwho ↦ hpositive ⟨who, hwho⟩
    exact (hnoUE ⟨0,
      seam.toSummableExactValueTail.zero_isUniformEquilibriumPayoff_of_nonpositive_solo
        hsolo⟩).elim

end QuittingPositiveDebtDynamicTailWitness

end GameTheory
