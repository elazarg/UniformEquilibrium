/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Classification.SimonFiniteOrbit.SurvivalCrossingRepair
import UniformEquilibrium.Quitting.Cycles.CyclicPeriodicExtension
import UniformEquilibrium.Quitting.Projective.Lasso
import UniformEquilibrium.Quitting.Root.EndpointOpponentStability

/-!
# Finite-prefix compatibility for reached support purification

Purifying several reached rows independently against their original tails
does not by itself make a root sequence: changing a later row changes every
earlier continuation.  This module performs the missing finite operation.
It installs the original continuation at a finite cutoff and evaluates all
purified rows backwards.  The resulting prefix is exactly Bellman-compatible.

If every purified marginal moves by at most `d`, then a uniform payoff bound
`M` charges at most `2 * M * card * d` per changed row.  Consequently the
recomputed continuation at an offset is within the sum of the remaining row
charges of the original continuation.  Support optimality transfers to the
recomputed tail with exactly that accumulated error.

This is a finite, source-matched compatibility theorem.  It neither chooses
one prefix length working at every scale nor constructs a compatible infinite
sequence of purified rows.
-/

noncomputable section

namespace GameTheory

open Math.Probability Math.PMFProduct

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Purify every row against its actual continuation in the source root
sequence.  A finite backward evaluation below reads only a displayed finite
window of this sequence. -/
def quittingReachedSupportPurifiedRoots
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (β : ℝ) : ℕ → ι → PMF Bool :=
  fun time => quittingSupportPurifiedRoot reward
    (quittingRootSequenceTailVector reward roots (time + 1)) β (roots time)

/-- Value entering `start + offset` after playing the remaining purified
prefix and then installing the source sequence's actual tail at the cutoff.
Only offsets at most `fuel` have the intended prefix interpretation. -/
def quittingReachedSupportPurifiedPrefixValue
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (β : ℝ)
    (start fuel offset : ℕ) : Payoff ι :=
  quittingRootSequenceBackwardPayoff reward
    (quittingReachedSupportPurifiedRoots reward roots β)
    (quittingRootSequenceTailVector reward roots (start + fuel))
    (start + offset) (fuel - offset)

/-- The recomputed prefix has the source sequence's actual continuation as
its terminal boundary. -/
theorem quittingReachedSupportPurifiedPrefixValue_at_cutoff
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (β : ℝ) (start fuel : ℕ) :
    quittingReachedSupportPurifiedPrefixValue reward roots β start fuel fuel =
      quittingRootSequenceTailVector reward roots (start + fuel) := by
  simp [quittingReachedSupportPurifiedPrefixValue]

/-- Every pre-cutoff row of the recomputed prefix satisfies its exact Bellman
equation against the next recomputed value. -/
theorem quittingReachedSupportPurifiedPrefixValue_eq_successor
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (β : ℝ)
    (start fuel offset : ℕ) (hoffset : offset < fuel) :
    quittingReachedSupportPurifiedPrefixValue reward roots β start fuel offset =
      quittingRootSuccessorPayoff reward
        (quittingReachedSupportPurifiedPrefixValue reward roots β start fuel
          (offset + 1))
        (quittingReachedSupportPurifiedRoots reward roots β (start + offset)) := by
  unfold quittingReachedSupportPurifiedPrefixValue
  rw [show fuel - offset = (fuel - (offset + 1)) + 1 by omega,
    quittingRootSequenceBackwardPayoff_succ]
  congr 2


/-- A finite sequence of root perturbations accumulates additively under
backward Bellman evaluation.  The terminal boundary is the source sequence's
actual tail at the end of the window. -/
theorem abs_quittingRootSequenceBackwardPayoff_sub_tailVector_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots candidate : ℕ → ι → PMF Bool)
    (start steps : ℕ) {M d : ℝ} (hd : 0 ≤ d)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hclose : ∀ offset, offset < steps → ∀ player,
      |(candidate (start + offset) player true).toReal -
          (roots (start + offset) player true).toReal| ≤ d) :
    ∀ who,
      |quittingRootSequenceBackwardPayoff reward candidate
          (quittingRootSequenceTailVector reward roots (start + steps))
          start steps who -
        quittingRootSequenceTailVector reward roots start who| ≤
      (2 * M) * ((Fintype.card ι : ℝ) * d) * steps := by
  induction steps generalizing start with
  | zero =>
      intro who
      simp [quittingRootSequenceTailVector]
  | succ steps ih =>
      intro who
      let charge := (2 * M) * ((Fintype.card ι : ℝ) * d)
      let candidateTail := quittingRootSequenceBackwardPayoff reward candidate
        (quittingRootSequenceTailVector reward roots (start + (steps + 1)))
        (start + 1) steps
      let sourceTail := quittingRootSequenceTailVector reward roots (start + 1)
      have hshiftClose : ∀ offset, offset < steps → ∀ player,
        |(candidate (start + 1 + offset) player true).toReal -
              (roots (start + 1 + offset) player true).toReal| ≤ d := by
        intro offset hoffset player
        have h := hclose (offset + 1) (Nat.succ_lt_succ hoffset) player
        rw [show start + (offset + 1) = start + 1 + offset by omega] at h
        exact h
      have htailClose : ∀ player,
          |candidateTail player - sourceTail player| ≤ charge * steps := by
        intro player
        simpa [candidateTail, sourceTail, charge, Nat.add_assoc,
          Nat.add_left_comm, Nat.add_comm] using
          ih (start + 1) hshiftClose player
      have hcharge : 0 ≤ charge := by
        dsimp only [charge]
        by_cases hcard : Fintype.card ι = 0
        · simp [hcard]
        · letI : Nonempty ι :=
            Fintype.card_pos_iff.mp (Nat.pos_of_ne_zero hcard)
          let player : ι := Classical.choice inferInstance
          have hM : 0 ≤ M :=
            (abs_nonneg
              (reward (quittingSingletonTerminal player) player)).trans
              (hreward (quittingSingletonTerminal player) player)
          positivity
      have htailStep :
          |quittingRootSuccessorPayoff reward candidateTail (candidate start) who -
              quittingRootSuccessorPayoff reward sourceTail (candidate start) who| ≤
            charge * steps := by
        exact abs_quittingRootExpectedPayoff_sub_of_tail_close reward
          candidateTail sourceTail (candidate start) who
          (mul_nonneg hcharge (Nat.cast_nonneg steps)) (htailClose who)
      have hsourceBound : ∀ player, |sourceTail player| ≤ M := by
        intro player
        have hM : 0 ≤ M :=
          (abs_nonneg
            (reward (quittingSingletonTerminal player) player)).trans
            (hreward (quittingSingletonTerminal player) player)
        exact abs_quittingRootSequenceTerminalValue_le reward roots player
          (start + 1) hM hreward
      have hrootStep :
          |quittingRootSuccessorPayoff reward sourceTail (candidate start) who -
              quittingRootSuccessorPayoff reward sourceTail (roots start) who| ≤
            charge := by
        apply abs_quittingRootSuccessorPayoff_sub_of_quitProbability_close
          reward sourceTail (candidate start) (roots start) who hreward
          hsourceBound
        simpa using hclose 0 (by omega)
      rw [quittingRootSequenceBackwardPayoff_succ]
      change
        |quittingRootSuccessorPayoff reward candidateTail (candidate start) who -
            quittingRootSequenceTailVector reward roots start who| ≤ _
      rw [show quittingRootSequenceTailVector reward roots start who =
        quittingRootSuccessorPayoff reward sourceTail (roots start) who by
          exact quittingRootSequenceTerminalValue_eq_successorPayoff_tailVector
            reward roots who start]
      calc
        |quittingRootSuccessorPayoff reward candidateTail (candidate start) who -
            quittingRootSuccessorPayoff reward sourceTail (roots start) who| ≤
            |quittingRootSuccessorPayoff reward candidateTail
                (candidate start) who -
              quittingRootSuccessorPayoff reward sourceTail
                (candidate start) who| +
              |quittingRootSuccessorPayoff reward sourceTail
                  (candidate start) who -
                quittingRootSuccessorPayoff reward sourceTail
                  (roots start) who| := abs_sub_le _ _ _
        _ ≤ charge * steps + charge := add_le_add htailStep hrootStep
        _ = (2 * M) * ((Fintype.card ι : ℝ) * d) *
            ((steps + 1 : ℕ) : ℝ) := by
          simp only [charge]
          push_cast
          ring

/-- Private extraction of the coordinate displacement hidden inside the
reached-row support-purification theorem. -/
private theorem supportPurifiedRoot_coordinate_close_of_reachedNash
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (stage : ℕ)
    {α u β d : ℝ}
    (hα : 0 < α) (hu : 0 < u) (hβ : 0 < β) (hd : 0 < d)
    (hnash : IsεQuittingRootSequenceNash reward α roots)
    (hreached : u ≤ quittingJointSurvivalWeight roots 0 stage)
    (hscale : α < u * β * d) :
    ∀ who,
      |(quittingReachedSupportPurifiedRoots reward roots β stage who true).toReal -
          (roots stage who true).toReal| < d := by
  let survival := quittingJointSurvivalWeight roots 0 stage
  have hsurvival : 0 < survival := hu.trans_le hreached
  have hendpoint : IsεQuittingRootEndpointNash reward
      (quittingRootSequenceTailVector reward roots (stage + 1))
      (α / survival) (roots stage) :=
    isεQuittingRootEndpointNash_tailVector_of_isεQuittingRootSequenceNash
      reward roots hnash stage hsurvival
  have hpure :=
    (isεQuittingRootEndpointNash_iff_purePayoff_le reward
      (quittingRootSequenceTailVector reward roots (stage + 1))
      (α / survival) (roots stage)).mp hendpoint
  have hlocalError : 0 < α / survival := div_pos hα hsurvival
  have hratio : α / survival ≤ α / u := by
    exact (div_le_div_iff₀ hsurvival hu).2
      (mul_le_mul_of_nonneg_left hreached hα.le)
  apply supportPurifiedRoot_coordinate_close_of_mul_bound reward
    (quittingRootSequenceTailVector reward roots (stage + 1)) (roots stage)
    hu hβ hd hscale
  · intro who hbad
    exact (badQuit_quitProbability_mul_lt_of_endpointCaps reward
      (quittingRootSequenceTailVector reward roots (stage + 1))
      (quittingRootSequenceTailVector reward roots (stage + 1))
      (roots stage) hlocalError (fun _ => le_rfl)
      (fun player => (hpure player).2) who hbad).trans_le hratio
  · intro who hbad
    exact (badContinue_continueProbability_mul_lt_of_endpointCaps reward
      (quittingRootSequenceTailVector reward roots (stage + 1))
      (quittingRootSequenceTailVector reward roots (stage + 1))
      (roots stage) hlocalError (fun _ => le_rfl)
      (fun player => (hpure player).1) who hbad).trans_le hratio

/-- **Reached finite-prefix compatibility.**  Simultaneously purify every
row of a uniformly reached finite window.  Against each original tail the
row is support-local `η`-optimal.  Backward evaluation from the original
cutoff tail makes all rows exactly Bellman-compatible, moves the continuation
at offset `k` by at most
`2 * M * card * d * (fuel - k)`, and preserves support optimality against the
recomputed tail after adding the remaining-tail error.

This theorem consumes concrete roots, a finite window, and an explicit reach
bound.  It does not assume or return a global compatible-prefix producer. -/
theorem reached_supportPurifiedPrefix_compatible
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (start fuel : ℕ)
    {α u β d M η : ℝ}
    (hα : 0 < α) (hu : 0 < u) (hβ : 0 < β) (hd : 0 < d)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hnash : IsεQuittingRootSequenceNash reward α roots)
    (hreached : ∀ offset, offset < fuel →
      u ≤ quittingJointSurvivalWeight roots 0 (start + offset))
    (hscale : α < u * β * d)
    (herror : β + 4 * M * (Fintype.card ι : ℝ) * d ≤ η) :
    (∀ offset, offset < fuel →
      IsQuittingRootSupportApproxNash reward
        (quittingRootSequenceTailVector reward roots (start + offset + 1)) η
        (quittingReachedSupportPurifiedRoots reward roots β (start + offset))) ∧
    (∀ offset, offset < fuel →
      quittingReachedSupportPurifiedPrefixValue reward roots β start fuel offset =
        quittingRootSuccessorPayoff reward
          (quittingReachedSupportPurifiedPrefixValue reward roots β start fuel
            (offset + 1))
          (quittingReachedSupportPurifiedRoots reward roots β
            (start + offset))) ∧
    quittingReachedSupportPurifiedPrefixValue reward roots β start fuel fuel =
      quittingRootSequenceTailVector reward roots (start + fuel) ∧
    (∀ offset, offset ≤ fuel → ∀ who,
      |quittingReachedSupportPurifiedPrefixValue reward roots β start fuel offset
          who -
        quittingRootSequenceTailVector reward roots (start + offset) who| ≤
        (2 * M) * ((Fintype.card ι : ℝ) * d) *
          ((fuel - offset : ℕ) : ℝ)) ∧
    (∀ offset, offset < fuel → ∀ who,
      |quittingRootSequenceTailVector reward roots (start + offset) who -
        quittingRootSuccessorPayoff reward
          (quittingReachedSupportPurifiedPrefixValue reward roots β start fuel
            (offset + 1))
          (quittingReachedSupportPurifiedRoots reward roots β
            (start + offset)) who| ≤
        (2 * M) * ((Fintype.card ι : ℝ) * d) *
          ((fuel - offset : ℕ) : ℝ)) ∧
    (∀ offset, offset < fuel →
      IsQuittingRootSupportApproxNash reward
        (quittingReachedSupportPurifiedPrefixValue reward roots β start fuel
          (offset + 1))
        (η + (2 * M) * ((Fintype.card ι : ℝ) * d) *
          ((fuel - (offset + 1) : ℕ) : ℝ))
        (quittingReachedSupportPurifiedRoots reward roots β (start + offset))) := by
  have hrowClose : ∀ offset, offset < fuel → ∀ who,
      |(quittingReachedSupportPurifiedRoots reward roots β
            (start + offset) who true).toReal -
          (roots (start + offset) who true).toReal| ≤ d := by
    intro offset hoffset who
    exact (supportPurifiedRoot_coordinate_close_of_reachedNash reward roots
      (start + offset) hα hu hβ hd hnash (hreached offset hoffset) hscale who).le
  have horiginalSupport : ∀ offset, offset < fuel →
      IsQuittingRootSupportApproxNash reward
        (quittingRootSequenceTailVector reward roots (start + offset + 1)) η
        (quittingReachedSupportPurifiedRoots reward roots β
          (start + offset)) := by
    intro offset hoffset
    exact isQuittingRootSupportApproxNash_supportPurifiedRoot_of_reachedNash
      reward roots (start + offset) hα hu hβ hd hreward hnash
      (hreached offset hoffset) hscale herror
  have htailClose : ∀ offset, offset ≤ fuel → ∀ who,
      |quittingReachedSupportPurifiedPrefixValue reward roots β start fuel offset
          who -
        quittingRootSequenceTailVector reward roots (start + offset) who| ≤
        (2 * M) * ((Fintype.card ι : ℝ) * d) *
          ((fuel - offset : ℕ) : ℝ) := by
    intro offset hoffset who
    unfold quittingReachedSupportPurifiedPrefixValue
    have hbackward := abs_quittingRootSequenceBackwardPayoff_sub_tailVector_le
      reward roots (quittingReachedSupportPurifiedRoots reward roots β)
      (start + offset) (fuel - offset) hd.le hreward
    have hwindowClose : ∀ later, later < fuel - offset → ∀ player,
        |(quittingReachedSupportPurifiedRoots reward roots β
              (start + offset + later) player true).toReal -
            (roots (start + offset + later) player true).toReal| ≤ d := by
      intro later hlater player
      have hsum : offset + later < fuel := by omega
      simpa [Nat.add_assoc] using hrowClose (offset + later) hsum player
    have := hbackward hwindowClose who
    have hfinish : start + offset + (fuel - offset) = start + fuel := by omega
    rw [hfinish] at this
    exact this
  refine ⟨horiginalSupport, ?_,
    quittingReachedSupportPurifiedPrefixValue_at_cutoff
      reward roots β start fuel, htailClose, ?_, ?_⟩
  · intro offset hoffset
    exact quittingReachedSupportPurifiedPrefixValue_eq_successor
      reward roots β start fuel offset hoffset
  · intro offset hoffset who
    rw [← quittingReachedSupportPurifiedPrefixValue_eq_successor
      reward roots β start fuel offset hoffset, abs_sub_comm]
    exact htailClose offset hoffset.le who
  · intro offset hoffset
    apply isQuittingRootSupportApproxNash_of_tail_close reward
      (quittingReachedSupportPurifiedRoots reward roots β (start + offset))
      (quittingRootSequenceTailVector reward roots (start + offset + 1))
      (quittingReachedSupportPurifiedPrefixValue reward roots β start fuel
        (offset + 1))
      (horiginalSupport offset hoffset)
    intro who
    simpa [abs_sub_comm, Nat.add_assoc] using
      htailClose (offset + 1) (by omega) who

end GameTheory
