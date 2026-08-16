/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Terminal.TailCompression.ElementaryTailSemanticReduction
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticPlateauIncidence

/-!
# Chronological elementary-tail compression

The foundational elementary-tail compiler approximates continuation payoff,
best-response envelope, and semantic debt after any retained finite prefix.
This diagnostic bridge additionally preserves a literal terminal-coalition
atom at a marked chronological date.  Its stage-mass conclusion depends on
the diagnostic live-mass factorization, so it is intentionally kept above the
foundational tail-compression layer.
-/

noncomputable section

namespace GameTheory

open StochasticGame Math.Probability Math.PMFProduct

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Equality of a root word through a displayed date preserves the literal
unconditional terminal-coalition atom at that date. -/
theorem quittingStageCoalitionMass_rootSequence_eq_of_prefix
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (first second : ℕ → ι → PMF Bool) (time : ℕ)
    (terminal : {S : Finset ι // S.Nonempty})
    (hprefix : ∀ date ≤ time, first date = second date) :
    quittingStageCoalitionMass reward
        (quittingRootSequenceProfile reward first 0) time terminal =
      quittingStageCoalitionMass reward
        (quittingRootSequenceProfile reward second 0) time terminal := by
  rw [quittingStageCoalitionMass_eq_liveMass_mul_rootCoalitionMass,
    quittingStageCoalitionMass_eq_liveMass_mul_rootCoalitionMass,
    ← quittingJointSurvivalWeight_eq_liveMass_rootSequence reward first time,
    ← quittingJointSurvivalWeight_eq_liveMass_rootSequence reward second time,
    quittingProfileLiveRoot_quittingRootSequenceProfile_zero,
    quittingProfileLiveRoot_quittingRootSequenceProfile_zero,
    hprefix time le_rfl]
  congr 1
  exact quittingJointSurvivalWeight_congr first second 0 time
    (fun offset hoffset => by
      simpa using hprefix offset (Nat.le_of_lt hoffset))

/-- After any marked date, retain an arbitrarily long literal root block and
attach an elementary boundary while preserving the marked terminal atom and
approximating the marked continuation's payoff, envelope, and semantic debt.
The compressed continuation is also identified with its exact finite
backward semantic evaluation. -/
theorem exists_markedDate_elementaryCompression_continuationSemantics_close
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (mark retainedAfterMark : ℕ)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ cap : QuittingElementaryTailCap ι, ∃ tailCutoff,
      retainedAfterMark + 1 ≤ tailCutoff ∧
      QuittingElementaryCapMatchesSurvivalStratum
        (fun time => roots (mark + time)) cap ∧
      (∀ time < mark + tailCutoff,
        quittingElementaryTailRoots roots (mark + tailCutoff) cap time =
          roots time) ∧
      (∀ terminal,
        quittingStageCoalitionMass reward
            (quittingRootSequenceProfile reward roots 0) mark terminal =
          quittingStageCoalitionMass reward
            (quittingRootSequenceProfile reward
              (quittingElementaryTailRoots
                roots (mark + tailCutoff) cap) 0) mark terminal) ∧
      (∀ observer,
        |(quittingRootSequenceContinuationSemanticPair
              reward roots mark).1 observer -
            (quittingRootSequenceContinuationSemanticPair reward
              (quittingElementaryTailRoots roots (mark + tailCutoff) cap)
              mark).1 observer| < δ ∧
        |(quittingRootSequenceContinuationSemanticPair
              reward roots mark).2 observer -
            (quittingRootSequenceContinuationSemanticPair reward
              (quittingElementaryTailRoots roots (mark + tailCutoff) cap)
              mark).2 observer| < δ ∧
        |quittingTerminalSemanticDebt
              (quittingRootSequenceContinuationSemanticPair
                reward roots mark) observer -
            quittingTerminalSemanticDebt
              (quittingRootSequenceContinuationSemanticPair reward
                (quittingElementaryTailRoots roots (mark + tailCutoff) cap)
                mark) observer| < δ) ∧
      quittingRootSequenceContinuationSemanticPair reward
          (quittingElementaryTailRoots roots (mark + tailCutoff) cap) mark =
        quittingFinitePrefixSemanticEval reward
          (fun time => roots (mark + time)) tailCutoff
          (quittingElementaryBoundarySemanticPair reward cap) := by
  let shifted := fun time => roots (mark + time)
  let η := δ / 2
  have hη : 0 < η := div_pos hδ (by norm_num)
  obtain ⟨cap, tailCutoff, hlate, hmatch, hpayoff, henvelope⟩ :=
    exists_stratifiedElementaryTailCap_terminalPair_close_after
      reward shifted (retainedAfterMark + 1) hη
  let capped :=
    quittingElementaryTailRoots roots (mark + tailCutoff) cap
  have hcappedShift :
      (fun time => capped (mark + time)) =
        quittingElementaryTailRoots shifted tailCutoff cap := by
    exact quittingElementaryTailRoots_add_shift
      roots mark tailCutoff cap
  refine ⟨cap, tailCutoff, hlate, hmatch, ?_, ?_, ?_, ?_⟩
  · intro time htime
    exact quittingElementaryTailRoots_of_lt roots cap htime
  · intro terminal
    apply quittingStageCoalitionMass_rootSequence_eq_of_prefix
    intro date hdate
    exact (quittingElementaryTailRoots_of_lt roots cap (by
      have htailPositive : 0 < tailCutoff := by omega
      omega)).symm
  · intro observer
    have hp := hpayoff observer
    have hb := henvelope observer
    have hp' :
        |(quittingRootSequenceContinuationSemanticPair
              reward roots mark).1 observer -
            (quittingRootSequenceContinuationSemanticPair
              reward capped mark).1 observer| < η := by
      rw [quittingRootSequenceContinuationSemanticPair_payoff,
        quittingRootSequenceContinuationSemanticPair_payoff]
      have hsource :
          quittingRootSequenceTerminalValue reward roots observer mark =
            quittingRootSequenceTerminalValue reward shifted observer 0 := by
        simpa [shifted] using
          (quittingRootSequenceTerminalValue_eq_shift
            reward roots observer mark)
      have htarget :
          quittingRootSequenceTerminalValue reward capped observer mark =
            quittingRootSequenceTerminalValue reward
              (quittingElementaryTailRoots shifted tailCutoff cap)
              observer 0 := by
        calc
          quittingRootSequenceTerminalValue reward capped observer mark =
              quittingRootSequenceTerminalValue reward
                (fun time => capped (mark + time)) observer 0 :=
            quittingRootSequenceTerminalValue_eq_shift
              reward capped observer mark
          _ = quittingRootSequenceTerminalValue reward
                (quittingElementaryTailRoots shifted tailCutoff cap)
                observer 0 := by rw [hcappedShift]
      rw [hsource, htarget]
      exact hp
    have hb' :
        |(quittingRootSequenceContinuationSemanticPair
              reward roots mark).2 observer -
            (quittingRootSequenceContinuationSemanticPair
              reward capped mark).2 observer| < η := by
      rw [quittingRootSequenceContinuationSemanticPair_envelope,
        quittingRootSequenceContinuationSemanticPair_envelope,
        hcappedShift]
      exact hb
    constructor
    · exact hp'.trans_le (by dsimp [η]; linarith)
    · constructor
      · exact hb'.trans_le (by dsimp [η]; linarith)
      · unfold quittingTerminalSemanticDebt
        calc
          |((quittingRootSequenceContinuationSemanticPair
                  reward roots mark).2 observer -
                (quittingRootSequenceContinuationSemanticPair
                  reward roots mark).1 observer) -
              ((quittingRootSequenceContinuationSemanticPair
                  reward capped mark).2 observer -
                (quittingRootSequenceContinuationSemanticPair
                  reward capped mark).1 observer)| =
              |((quittingRootSequenceContinuationSemanticPair
                    reward roots mark).2 observer -
                  (quittingRootSequenceContinuationSemanticPair
                    reward capped mark).2 observer) +
                ((quittingRootSequenceContinuationSemanticPair
                    reward capped mark).1 observer -
                  (quittingRootSequenceContinuationSemanticPair
                    reward roots mark).1 observer)| := by ring_nf
          _ ≤ |(quittingRootSequenceContinuationSemanticPair
                    reward roots mark).2 observer -
                  (quittingRootSequenceContinuationSemanticPair
                    reward capped mark).2 observer| +
                |(quittingRootSequenceContinuationSemanticPair
                    reward capped mark).1 observer -
                  (quittingRootSequenceContinuationSemanticPair
                    reward roots mark).1 observer| := abs_add_le _ _
          _ < η + η := add_lt_add hb'
            (by simpa [abs_sub_comm] using hp')
          _ = δ := by dsimp [η]; ring
  · unfold quittingRootSequenceContinuationSemanticPair
    rw [quittingRootSequenceProfile_eq_shift, hcappedShift]
    exact quittingTerminalSemanticPair_elementaryTail_eq_finiteEval
      reward shifted tailCutoff cap

end GameTheory
