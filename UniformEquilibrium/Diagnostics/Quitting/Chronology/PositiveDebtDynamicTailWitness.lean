/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.Debt.PositiveDebtSelfLoopLimit
import UniformEquilibrium.Diagnostics.Quitting.Collision.SingletonPacket.Surplus
import UniformEquilibrium.Quitting.Classification.TerminalExploitabilityToggles
import UniformEquilibrium.Quitting.Cycles.BehaviorPureTimeExtremality
import UniformEquilibrium.Quitting.Cycles.PeriodicCompiler
import UniformEquilibrium.Quitting.Cycles.PeriodicWindowEvaluation

/-!
# Positive debt dynamic-tail witness of a quitting counterexample

This module records the optimized dynamic-tail consequence of terminal
exploitability, together with the strategic evaluation of periodic restarts.

Every terminal exploitability witness supplies:

* a projective optimized exact-D tail converging to a positive-debt
  all-Continue exact dynamic-debt self-loop; and
* for every finite window of that tail, a periodically restarted behavior
  profile whose complete behavioral best-response value is a finite maximum
  of first-pass stop values and refusal/`Never`, and exceeds its realized
  payoff by the witness's terminal gap for some player.

-/

noncomputable section

namespace GameTheory

open Filter Math.Probability

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}

/-- The optimized exact dynamic-debt tail consequence of terminal
exploitability. -/
structure QuittingPositiveDebtDynamicTailWitness
    (witness : QuittingTerminalExploitabilityWitness reward) where
  tail : ℕ → QuittingDebtPoint ι
  subseq : ℕ → ℕ
  limit : QuittingPositiveDebtSelfLoopLimit reward
  subseq_strict : StrictMono subseq
  projective_limit :
    letI : Nonempty ι := witness.nonempty_players
    Tendsto
      ((fun cutoff ↦ quittingFiniteMinMaxDynamicDebtTail reward cutoff) ∘
        subseq) atTop (nhds tail)
  tail_mem : ∀ time, tail time ∈ quittingDebtBox reward
  tail_edge : ∀ time,
    IsQuittingDynamicDebtEdge reward (tail time) (tail (time + 1))
  terminalGap_le_initialDebt : witness.terminalGap ≤ (tail 0).2 limit.owner
  terminalGap_le_limitDebt : witness.terminalGap ≤ limit.debt limit.owner
  value_tendsto : ∀ who,
    Tendsto (fun time ↦ (tail time).1.1 who) atTop
      (nhds (limit.value who))
  debt_tendsto : ∀ who,
    Tendsto (fun time ↦ (tail time).2 who) atTop
      (nhds (limit.debt who))
  quitProbability_tendsto_zero : ∀ who,
    Tendsto (fun time ↦
      (quittingDynamicDebtTailRoots tail time who true).toReal)
      atTop (nhds 0)
  continueProbability_tendsto_one : ∀ who,
    Tendsto (fun time ↦
      (quittingDynamicDebtTailRoots tail time who false).toReal)
      atTop (nhds 1)
  ownerOpponentClock_summable :
    Summable (quittingOpponentClockCharge
      (quittingDynamicDebtTailRoots tail) limit.owner)
  jointAbsorption_summable :
    Summable (quittingDynamicDebtTailAbsorptionCharge tail)

namespace QuittingTerminalExploitabilityWitness

/-- Against every behavior profile, the exact best-response supremum can be
restricted to deterministic quit times and `Never` while retaining the full
counterexample gap. -/
theorem exists_pureTimeCap_gap
    (witness : QuittingTerminalExploitabilityWitness reward)
    (profile : (quittingGame reward).BehaviorProfile) :
    ∃ who,
      quittingTerminalPayoff reward profile who + witness.terminalGap ≤
        sSup (Set.range fun quitTime : Option ℕ ↦
          quittingTerminalPayoff reward
            (Function.update profile who
              (quittingPureTimeBehaviorStrategy reward who quitTime)) who) := by
  obtain ⟨who, deviation, hgap⟩ := witness.terminalExploitability profile
  refine ⟨who, hgap.trans ?_⟩
  exact quittingTerminalPayoff_update_le_sSup_pureTimeBehaviorStrategy
    reward profile who deviation

/-- Every finite window of any dynamic-debt tail, restarted periodically, is
exposed by the exact pure-time/`Never` cap at the witness's full terminal gap.
No Bellman property of the supplied tail is needed for this strategic
statement. -/
theorem exists_cyclicWindow_pureTimeCap_gap
    (witness : QuittingTerminalExploitabilityWitness reward)
    (tail : ℕ → QuittingDebtPoint ι) (start length : ℕ)
    (phase : Fin (length + 1)) :
    ∃ who,
      quittingCyclicTerminalValue reward
          (quittingDynamicDebtTailWindowCycle tail start length) phase who +
          witness.terminalGap ≤
        sSup (Set.range fun quitTime : Option ℕ ↦
          quittingTerminalPayoff reward
            (Function.update
              (quittingCyclicBehaviorProfile reward
                (quittingDynamicDebtTailWindowCycle tail start length) phase)
              who (quittingPureTimeBehaviorStrategy reward who quitTime)) who) := by
  simpa only [quittingTerminalPayoff_cyclicBehaviorProfile] using
    witness.exists_pureTimeCap_gap
      (quittingCyclicBehaviorProfile reward
        (quittingDynamicDebtTailWindowCycle tail start length) phase)

/-- Every restarted tail window exposes the full counterexample gap through
the exact finite periodic evaluator: refusal/`Never` or one stop in the first
pass.  This is the finite, search-facing form of
`exists_cyclicWindow_pureTimeCap_gap`. -/
theorem exists_cyclicWindow_finiteEvaluation_gap
    (witness : QuittingTerminalExploitabilityWitness reward)
    (tail : ℕ → QuittingDebtPoint ι) (start length : ℕ)
    (phase : Fin (length + 1)) :
    ∃ who,
      quittingCyclicTerminalValue reward
          (quittingDynamicDebtTailWindowCycle tail start length) phase who +
          witness.terminalGap ≤
        quittingPeriodicWindowBestResponseValue reward
          (quittingCyclicRootSequence
            (quittingDynamicDebtTailWindowCycle tail start length) phase)
          who (length + 1) := by
  letI : NeZero (length + 1) := ⟨Nat.succ_ne_zero length⟩
  let cycle := quittingDynamicDebtTailWindowCycle tail start length
  let profile := quittingCyclicBehaviorProfile reward cycle phase
  obtain ⟨who, deviation, hgap⟩ := witness.terminalExploitability profile
  refine ⟨who, ?_⟩
  have hperiodic : ∀ time,
      quittingProfileLiveRoot reward profile (time + (length + 1)) =
        quittingProfileLiveRoot reward profile time := by
    intro time
    simp [profile, cycle]
  have hbdd := bddAbove_range_quittingTerminalPayoff_update
    reward profile who
  have heval := sSup_range_quittingTerminalPayoff_update_eq_periodicWindow
    reward profile who (length + 1) hperiodic
  calc
    quittingCyclicTerminalValue reward cycle phase who +
        witness.terminalGap =
      quittingTerminalPayoff reward profile who + witness.terminalGap := by
        simp [profile]
    _ ≤ quittingTerminalPayoff reward
        (Function.update profile who deviation) who := hgap
    _ ≤ sSup (Set.range fun candidate :
        (quittingGame reward).BehaviorStrategy who ↦
          quittingTerminalPayoff reward
            (Function.update profile who candidate) who) :=
      le_csSup hbdd ⟨deviation, rfl⟩
    _ = quittingPeriodicWindowBestResponseValue reward
        (quittingCyclicRootSequence cycle phase) who (length + 1) := by
      simpa [profile] using heval

/-- Every terminal exploitability witness has an independently extracted positive-debt
all-Continue dynamic tail limit, with its provenance and convergence data. -/
theorem nonempty_positiveDebtDynamicTailWitness
    (witness : QuittingTerminalExploitabilityWitness reward) :
    Nonempty (QuittingPositiveDebtDynamicTailWitness witness) := by
  letI : Nonempty ι := witness.nonempty_players
  obtain ⟨tail, subseq, limit, hsubseq, hprojective, hbox, hedge,
      hinitialDebt, hlimitDebt, hvalue, hdebt, hquit, hcontinue,
      hownerClock, habsorption⟩ :=
    witness.exists_terminalGapDynamicDebtTail_selfLoopLimit
  exact ⟨{
    tail := tail
    subseq := subseq
    limit := limit
    subseq_strict := hsubseq
    projective_limit := hprojective
    tail_mem := hbox
    tail_edge := hedge
    terminalGap_le_initialDebt := hinitialDebt
    terminalGap_le_limitDebt := hlimitDebt
    value_tendsto := hvalue
    debt_tendsto := hdebt
    quitProbability_tendsto_zero := hquit
    continueProbability_tendsto_one := hcontinue
    ownerOpponentClock_summable := hownerClock
    jointAbsorption_summable := habsorption }⟩

end QuittingTerminalExploitabilityWitness

end GameTheory
