/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.StoppingLaw.FiniteClockMinimumPaidPort

/-!
# Fin4 finite-clock minimum paid-port reduction

This narrow specialization records the four-step bound for a supplied Fin4
finite-clock positive global minimum.
-/

noncomputable section

namespace GameTheory

open _root_.Math.Probability _root_.Math.Probability.DiscreteHazard
open _root_.Math.ProbabilityMassFunction

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Direct Fin4 specialization: the exact-cap chain has at most four steps and
all paid thresholds carried by the outcome structures are quarter-debt. -/
theorem finFourFiniteClockMinimum_exactCapPurification_or_pureTimeDescentPaidPort
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (profile : (quittingGame reward).BehaviorProfile)
    (hclock : IsQuittingFiniteClockProfile reward profile)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum
          (quittingTerminalSemanticPair reward profile) ≤
        quittingTerminalSemanticDebtSum candidate)
    (hpositive : 0 < quittingTerminalSemanticDebtSum
      (quittingTerminalSemanticPair reward profile)) :
    ∃ clockBound,
      HasQuittingFiniteClockBound reward profile clockBound ∧
      QuittingDeadlineBounded reward
        (quittingStoppingLawCanonicalizeOn reward profile Finset.univ)
        clockBound ∧
      quittingTerminalSemanticPair reward
          (quittingStoppingLawCanonicalizeOn reward profile Finset.univ) =
        quittingTerminalSemanticPair reward profile ∧
      QuittingFiniteClockMinimumPaidPortReduction reward
        (quittingStoppingLawCanonicalizeOn reward profile Finset.univ)
        (quittingTerminalSemanticDebtSum
          (quittingTerminalSemanticPair reward profile)) 4 := by
  simpa using
    finiteClockMinimum_exactCapPurification_or_pureTimeDescentPaidPort
      reward profile hclock hminimum hpositive

end GameTheory
