/-
Copyright (c) 2026 UniformEquilibrium contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: UniformEquilibrium contributors
-/

import Research.Quitting.NearMinimumRetainedTailTimingNashIdentity
import UniformEquilibrium.Diagnostics.Quitting.RetainedTailFiniteTimingRealization

/-!
# Near-minimum retained-tail timing rigidity

This Research module applies the production retained-tail timing realization
compiler to the current positive-minimum root-rigidity theorem.
-/

noncomputable section

namespace GameTheory

open Math.Probability Math.ProbabilityMassFunction Math.PMFProduct

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Near a positive global debt minimum, the retained-tail timing normal form
has only the literal pure-`Never` Nash law among laws giving every player
positive `Never` probability.  This is an actual normal-form Nash compiler,
not a supplied root-stack verifier. -/
theorem nearMinimum_retainedTailFiniteTimingNash_eq_pureNever
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : (quittingGame reward).BehaviorProfile)
    (deadline : ℕ)
    (mixed : ι → PMF (QuittingFiniteDeadlineTimingAction deadline))
    {M kappa excess : ℝ}
    (hM : 0 < M) (hkappa : 0 < kappa)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hminimum : 0 < quittingTerminalDebtSumInf reward)
    (htail : quittingTerminalDebtSum reward tail ≤
      quittingTerminalDebtSumInf reward + excess)
    (hsingleton : ∀ who,
      reward (quittingSingletonTerminal who) who + kappa ≤
        quittingTerminalPayoff reward tail who)
    (hnear : excess <
      kappa * quittingTerminalDebtSumInf reward / (2 * M))
    (hnash : (quittingRetainedTailFiniteTimingGame reward
      deadline tail).mixedExtension.IsNash mixed)
    (hnever : ∀ who, 0 < (mixed who none).toReal) :
    ∀ who, mixed who = PMF.pure none := by
  apply retainedTailFiniteTimingNash_eq_pureNever_of_root_rigidity
    reward tail
  · intro root hnashRoot
    exact nearMinimum_rootNashAgainstPayoff_eq_allContinue
      reward tail root hM hkappa hreward hminimum htail hsingleton
        hnashRoot hnear
  · exact hnash
  · exact hnever

/-- Profile-level form of the retained-tail mixed-Nash rigidity compiler. -/
theorem nearMinimum_retainedTailFiniteTimingNash_eq_pureNeverProfile
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : (quittingGame reward).BehaviorProfile)
    (deadline : ℕ)
    (mixed : ι → PMF (QuittingFiniteDeadlineTimingAction deadline))
    {M kappa excess : ℝ}
    (hM : 0 < M) (hkappa : 0 < kappa)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hminimum : 0 < quittingTerminalDebtSumInf reward)
    (htail : quittingTerminalDebtSum reward tail ≤
      quittingTerminalDebtSumInf reward + excess)
    (hsingleton : ∀ who,
      reward (quittingSingletonTerminal who) who + kappa ≤
        quittingTerminalPayoff reward tail who)
    (hnear : excess <
      kappa * quittingTerminalDebtSumInf reward / (2 * M))
    (hnash : (quittingRetainedTailFiniteTimingGame reward
      deadline tail).mixedExtension.IsNash mixed)
    (hnever : ∀ who, 0 < (mixed who none).toReal) :
    mixed = fun _ => PMF.pure none := by
  funext who
  exact nearMinimum_retainedTailFiniteTimingNash_eq_pureNever
    reward tail deadline mixed hM hkappa hreward hminimum htail
      hsingleton hnear hnash hnever who

end GameTheory
