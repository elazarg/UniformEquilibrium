/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.StoppingLaw.TerminalSemanticStoppingLawRetentionChain

/-!
# Macroscopic atom retention through a microscopic reset word

Fixed half-retention is too expensive along a long reset word: its lower
bound decays like `2^(-L)`.  Chattering uses a different calibration.  For a
word of length `L > 0`, require every micro-reset to retain the factor

```text
1 - 1 / (2L).
```

The factors still multiply exactly, but Bernoulli's inequality gives

```text
(1 - 1 / (2L))^L >= 1/2.
```

Consequently any selected chronological coalition atom whose edgewise
retention is supplied retains at least half of its initial mass through the
*whole* word, independently of its length.

The conclusion prevents quantitative atom decay across a length-calibrated
word. It does not identify reset vertices with successive Bellman states or
turn reset debt charge into game-time absorption.
-/

noncomputable section

namespace GameTheory

open StochasticGame Math.Probability Math.PMFProduct

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-! ## The length-calibrated microscopic factor -/

/-- Per-edge retention factor for a chattering word of the displayed
positive length. -/
def microChatteringRetentionFactor (length : ℕ) : ℝ :=
  1 - 1 / (2 * (length : ℝ))

/-- The microscopic retention factor is nonnegative at positive length. -/
theorem microChatteringRetentionFactor_nonneg
    (length : ℕ) (hlength : 0 < length) :
    0 ≤ microChatteringRetentionFactor length := by
  unfold microChatteringRetentionFactor
  have hlengthReal : 1 ≤ (length : ℝ) := by exact_mod_cast hlength
  have hdenom : 1 ≤ 2 * (length : ℝ) := by linarith
  have hdiv : 1 / (2 * (length : ℝ)) ≤ 1 := by
    exact (div_le_one (by positivity)).2 hdenom
  linarith

/-- Bernoulli's inequality: a word of `length` calibrated at loss
`1/(2*length)` retains at least one half of every multiplicatively retained
quantity. -/
theorem one_half_le_microChatteringRetentionFactor_pow
    (length : ℕ) (hlength : 0 < length) :
    (1 / 2 : ℝ) ≤ microChatteringRetentionFactor length ^ length := by
  have hlengthReal : 0 < (length : ℝ) := by exact_mod_cast hlength
  have hbern :
      1 + (length : ℝ) * (-1 / (2 * (length : ℝ))) ≤
        (1 + (-1 / (2 * (length : ℝ)))) ^ length :=
    one_add_mul_le_pow (by
      have : 1 / (2 * (length : ℝ)) ≤ 1 := by
        apply (div_le_one (by positivity)).2
        have : 1 ≤ (length : ℝ) := by exact_mod_cast hlength
        linarith
      have hneg : -(1 : ℝ) ≤ -(1 / (2 * (length : ℝ))) := neg_le_neg this
      have hsame : -(1 / (2 * (length : ℝ))) =
          -1 / (2 * (length : ℝ)) := by ring
      rw [hsame] at hneg
      linarith) length
  have hleft :
      1 + (length : ℝ) * (-1 / (2 * (length : ℝ))) = (1 / 2 : ℝ) := by
    field_simp
    ring
  have hright :
      1 + (-1 / (2 * (length : ℝ))) =
        microChatteringRetentionFactor length := by
    unfold microChatteringRetentionFactor
    ring
  simpa [hleft, hright] using hbern

/-! ## Whole-word retention -/

/-- **Macroscopic retention through an arbitrarily long microscopic word.**
If a word of positive length `L` retains `1 - 1/(2L)` at every edge, its
endpoint retains at least half of every source chronological atom. -/
theorem one_half_mul_stageCoalitionMass_le_of_microChatteringChain
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profiles : ℕ → (quittingGame reward).BehaviorProfile)
    (length : ℕ) (hlength : 0 < length)
    (start : ℕ)
    (terminal : {S : Finset ι // S.Nonempty}) (time : ℕ)
    (hstep : RetainsQuittingStageAtomOnInterval reward
      (microChatteringRetentionFactor length) profiles start length
        terminal time) :
    (1 / 2 : ℝ) *
        quittingStageCoalitionMass reward (profiles start) time terminal ≤
      quittingStageCoalitionMass reward (profiles (start + length)) time terminal := by
  have hmass : 0 ≤
      quittingStageCoalitionMass reward (profiles start) time terminal :=
    quittingStageCoalitionMass_nonneg reward (profiles start) time terminal
  have hpower := one_half_le_microChatteringRetentionFactor_pow length hlength
  have hchain := factorPow_mul_stageCoalitionMass_le_of_resetChain
    reward profiles (microChatteringRetentionFactor length)
      (microChatteringRetentionFactor_nonneg length hlength)
      start length terminal time hstep
  exact (mul_le_mul_of_nonneg_right hpower hmass).trans hchain

/-- Every initially positive atom remains quantitatively positive after the
complete microscopic word. -/
theorem stageCoalitionMass_pos_of_microChatteringChain
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profiles : ℕ → (quittingGame reward).BehaviorProfile)
    (length : ℕ) (hlength : 0 < length)
    (start : ℕ)
    (terminal : {S : Finset ι // S.Nonempty}) (time : ℕ)
    (hstep : RetainsQuittingStageAtomOnInterval reward
      (microChatteringRetentionFactor length) profiles start length
        terminal time)
    (hpositive : 0 <
      quittingStageCoalitionMass reward (profiles start) time terminal) :
    0 < quittingStageCoalitionMass reward
      (profiles (start + length)) time terminal := by
  have hretained :=
    one_half_mul_stageCoalitionMass_le_of_microChatteringChain
      reward profiles length hlength start terminal time hstep
  exact (mul_pos (by norm_num) hpositive).trans_le hretained

end GameTheory
