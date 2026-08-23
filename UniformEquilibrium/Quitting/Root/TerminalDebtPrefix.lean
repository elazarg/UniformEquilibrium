/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Root.FirstBranch
import UniformEquilibrium.Quitting.Root.NashDefect
import UniformEquilibrium.Quitting.Root.SuccessorCertificate
import UniformEquilibrium.Quitting.Stationary.LiveMass

/-!
# Terminal deviation debt under an exact root prefix

For a literal continuation profile, a player's **best-response debt** is the
all-behavior best-response supremum minus the prescribed terminal payoff.  It
is equivalently the player's unilateral regret or exploitability gap against
the fixed opponents.  It is not online-learning regret: there is no cumulative
comparison with a fixed action in hindsight.  The word `debt` records the
dynamic accounting proved here—survival transports it, a positive exercise
premium consumes it, and opponent absorption kills it.
Prepending a finite root action admits an exact Bellman formula for this debt.
If the root is an exact Nash action against the continuation's literal payoff,
the formula implies coordinatewise debt monotonicity.

Every statement uses the actual continuation profile on both the prescribed
and deviation sides.  No stored boundary value, conditioned payoff, path
return, or state-matching premise is identified with that literal payoff.
-/

noncomputable section

namespace GameTheory

open Math.Probability Math.PMFProduct

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Playerwise literal best-response debt of a behavior profile: the
unilateral behavioral exploitability gap, not cumulative online-learning
regret. -/
def quittingTerminalDeviationDebt
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (who : ι) : ℝ :=
  quittingContinuationBestResponseValue reward profile who -
    quittingTerminalPayoff reward profile who

/-- Pure Quit does not read the all-Continue continuation coordinate. -/
theorem quittingRootQuitPayoff_continuation_invariant
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (first second : Payoff ι) (root : ι → PMF Bool) (who : ι) :
    quittingRootQuitPayoff reward first root who =
      quittingRootQuitPayoff reward second root who := by
  unfold quittingRootQuitPayoff
  apply quittingRootExpectedPayoff_eq_of_hasSureQuitter
  exact ⟨who, Function.update_self who (PMF.pure true) root⟩

/-- Pure Continue is affine in the player's continuation coordinate, with
linear coefficient equal to opponent Continue mass. -/
theorem quittingRootContinuePayoff_update_add
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : Payoff ι) (root : ι → PMF Bool) (who : ι) (increment : ℝ) :
    quittingRootContinuePayoff reward
        (Function.update tail who (tail who + increment)) root who =
      quittingRootContinuePayoff reward tail root who +
        quittingRootOpponentContinueMass root who * increment := by
  unfold quittingRootContinuePayoff quittingRootOpponentContinueMass
  rw [quittingRootExpectedPayoff_eq_absorbingContribution_add,
    quittingRootExpectedPayoff_eq_absorbingContribution_add]
  simp
  ring

/-- Exact root Nash turns the prescribed root mixture into the maximum of
its pure Quit and pure Continue endpoints. -/
theorem quittingRootSuccessorPayoff_eq_max_of_isZeroNash
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : Payoff ι) (root : ι → PMF Bool) (who : ι)
    (hnash : IsεQuittingRootNash reward tail 0 root) :
    quittingRootSuccessorPayoff reward tail root who =
      max (quittingRootQuitPayoff reward tail root who)
        (quittingRootContinuePayoff reward tail root who) := by
  have hquit := quittingRootQuitPayoff_le_successor_of_isZeroNash
    reward tail root who hnash
  have hcontinue := quittingRootContinuePayoff_le_successor_of_isZeroNash
    reward tail root who hnash
  apply le_antisymm
  · rw [quittingRootSuccessorPayoff_eq_endpointMix]
    have hsum := quittingRoot_continueProbability_add_quitProbability root who
    calc
      (root who true).toReal * quittingRootQuitPayoff reward tail root who +
          (root who false).toReal *
            quittingRootContinuePayoff reward tail root who ≤
        (root who true).toReal *
            max (quittingRootQuitPayoff reward tail root who)
              (quittingRootContinuePayoff reward tail root who) +
          (root who false).toReal *
            max (quittingRootQuitPayoff reward tail root who)
              (quittingRootContinuePayoff reward tail root who) := by
        exact add_le_add
          (mul_le_mul_of_nonneg_left (le_max_left _ _) ENNReal.toReal_nonneg)
          (mul_le_mul_of_nonneg_left (le_max_right _ _) ENNReal.toReal_nonneg)
      _ = max (quittingRootQuitPayoff reward tail root who)
            (quittingRootContinuePayoff reward tail root who) := by
        rw [← add_mul]
        have hsum' : (root who true).toReal +
            (root who false).toReal = 1 := by linarith
        rw [hsum', one_mul]
  · exact max_le hquit hcontinue

/-- The all-behavior best response against a root/continuation splice is the
maximum of pure Quit and pure Continue, where Continue carries the literal
continuation best-response value. -/
theorem quittingContinuationBestResponseValue_rootThenContinuation_eq_max
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool)
    (continuation : (quittingGame reward).BehaviorProfile)
    (who : ι) :
    quittingContinuationBestResponseValue reward
        (quittingRootThenContinuationProfile reward root continuation) who =
      max
        (quittingRootQuitPayoff reward
          (fun player => quittingTerminalPayoff reward continuation player)
          root who)
        (quittingRootContinuePayoff reward
          (Function.update
            (fun player => quittingTerminalPayoff reward continuation player)
            who (quittingContinuationBestResponseValue reward continuation who))
          root who) := by
  let base : Payoff ι :=
    fun player => quittingTerminalPayoff reward continuation player
  let best : ℝ := quittingContinuationBestResponseValue reward continuation who
  let spliced : (quittingGame reward).BehaviorProfile :=
    quittingRootThenContinuationProfile reward root continuation
  let values : Set ℝ := Set.range (fun deviation :
      (quittingGame reward).BehaviorStrategy who =>
    quittingTerminalPayoff reward (Function.update spliced who deviation) who)
  have hvalues : values.Nonempty := by
    exact ⟨quittingTerminalPayoff reward
      (Function.update spliced who (spliced who)) who, ⟨spliced who, rfl⟩⟩
  have hbounded : BddAbove values := by
    dsimp only [values]
    exact bddAbove_range_quittingTerminalPayoff_update reward spliced who
  change sSup values = _
  apply le_antisymm
  · apply csSup_le hvalues
    rintro payoff ⟨deviation, rfl⟩
    have hdeviation := quittingTerminalPayoff_update_rootThenContinuation_le
      reward root continuation who best
      (fun candidate =>
        quittingTerminalPayoff_update_le_continuationBestResponseValue
          reward continuation who candidate)
      deviation
    let marginal := deviation 0 ((quittingGame reward).emptyHist none)
    have hmix := quittingRootExpectedPayoff_update_eq_endpointMix
      reward (Function.update base who best) root who marginal
    have hquitInvariant := quittingRootQuitPayoff_continuation_invariant
      reward (Function.update base who best) base root who
    rw [hmix, hquitInvariant] at hdeviation
    exact hdeviation.trans <| by
      have hsum := quittingRoot_continueProbability_add_quitProbability
        (Function.update root who marginal) who
      simp only [Function.update_self] at hsum ⊢
      calc
        (marginal true).toReal * quittingRootQuitPayoff reward base root who +
            (marginal false).toReal *
              quittingRootContinuePayoff reward
                (Function.update base who best) root who ≤
          (marginal true).toReal *
              max (quittingRootQuitPayoff reward base root who)
                (quittingRootContinuePayoff reward
                  (Function.update base who best) root who) +
            (marginal false).toReal *
              max (quittingRootQuitPayoff reward base root who)
                (quittingRootContinuePayoff reward
                  (Function.update base who best) root who) := by
            exact add_le_add
              (mul_le_mul_of_nonneg_left
                (le_max_left _ _) ENNReal.toReal_nonneg)
              (mul_le_mul_of_nonneg_left
                (le_max_right _ _) ENNReal.toReal_nonneg)
        _ = max (quittingRootQuitPayoff reward base root who)
              (quittingRootContinuePayoff reward
                (Function.update base who best) root who) := by
          rw [← add_mul]
          have hsum' : (marginal true).toReal +
              (marginal false).toReal = 1 :=
            (add_comm _ _).trans hsum
          rw [hsum', one_mul]
  · apply max_le
    · apply le_csSup hbounded
      let assembled := quittingRootAndContinuationDeviation reward
        (PMF.pure true) (continuation who)
      refine ⟨assembled, ?_⟩
      change quittingTerminalPayoff reward
        (Function.update
          (quittingRootThenContinuationProfile reward root continuation)
          who assembled) who = _
      rw [quittingTerminalPayoff_update_rootAndContinuationDeviation_eq]
      rw [Function.update_eq_self]
      change quittingRootExpectedPayoff reward
        (Function.update base who (base who))
        (Function.update root who (PMF.pure true)) who = _
      rw [Function.update_eq_self]
      rfl
    · refine le_of_forall_pos_le_add fun ε hε => ?_
      obtain ⟨candidate, hcandidate⟩ :=
        exists_quittingContinuation_deviation_ge_sub
          reward continuation who hε
      let candidatePayoff := quittingTerminalPayoff reward
        (Function.update continuation who candidate) who
      let assembled := quittingRootAndContinuationDeviation reward
        (PMF.pure false) candidate
      have hassembled : quittingTerminalPayoff reward
          (Function.update spliced who assembled) who ≤ sSup values := by
        apply le_csSup hbounded
        exact ⟨assembled, rfl⟩
      have hbest : best ≤ candidatePayoff + ε := by
        dsimp [best, candidatePayoff]
        linarith
      have hroot := quittingRootExpectedPayoff_continuation_le_add
        reward (Function.update base who best)
        (Function.update base who candidatePayoff)
        (Function.update root who (PMF.pure false)) who hε.le (by simpa)
      change quittingTerminalPayoff reward
          (Function.update
            (quittingRootThenContinuationProfile reward root continuation)
            who assembled) who ≤ sSup values at hassembled
      rw [quittingTerminalPayoff_update_rootAndContinuationDeviation_eq]
        at hassembled
      dsimp [assembled, candidatePayoff, base] at hassembled hroot
      exact hroot.trans (by linarith)

/-- Literal terminal deviation debt is nonnegative. -/
theorem quittingTerminalDeviationDebt_nonneg
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (who : ι) :
    0 ≤ quittingTerminalDeviationDebt reward profile who := by
  have hbounded : BddAbove (Set.range fun deviation :
      (quittingGame reward).BehaviorStrategy who =>
    quittingTerminalPayoff reward
      (Function.update profile who deviation) who) := by
    exact bddAbove_range_quittingTerminalPayoff_update reward profile who
  have hprescribed : quittingTerminalPayoff reward profile who ≤
      quittingContinuationBestResponseValue reward profile who := by
    unfold quittingContinuationBestResponseValue
    apply le_csSup hbounded
    refine ⟨profile who, ?_⟩
    change quittingTerminalPayoff reward
      (Function.update profile who (profile who)) who =
        quittingTerminalPayoff reward profile who
    rw [Function.update_eq_self]
  unfold quittingTerminalDeviationDebt
  linarith

/-- Exact coordinatewise debt recursion for an exact Nash root against the
literal continuation payoff. -/
theorem quittingTerminalDeviationDebt_rootThenContinuation_eq
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool)
    (continuation : (quittingGame reward).BehaviorProfile)
    (who : ι)
    (hnash : IsεQuittingRootNash reward
      (fun player => quittingTerminalPayoff reward continuation player) 0 root) :
    quittingTerminalDeviationDebt reward
        (quittingRootThenContinuationProfile reward root continuation) who =
      max
          (quittingRootQuitPayoff reward
            (fun player => quittingTerminalPayoff reward continuation player)
            root who)
          (quittingRootContinuePayoff reward
              (fun player => quittingTerminalPayoff reward continuation player)
              root who +
            quittingRootOpponentContinueMass root who *
              quittingTerminalDeviationDebt reward continuation who) -
        max
          (quittingRootQuitPayoff reward
            (fun player => quittingTerminalPayoff reward continuation player)
            root who)
          (quittingRootContinuePayoff reward
            (fun player => quittingTerminalPayoff reward continuation player)
            root who) := by
  let base : Payoff ι :=
    fun player => quittingTerminalPayoff reward continuation player
  let debt := quittingTerminalDeviationDebt reward continuation who
  rw [quittingTerminalDeviationDebt,
    quittingContinuationBestResponseValue_rootThenContinuation_eq_max
      reward root continuation who,
    quittingTerminalPayoff_rootThenContinuation_eq]
  change max
      (quittingRootQuitPayoff reward base root who)
      (quittingRootContinuePayoff reward
        (Function.update base who
          (quittingContinuationBestResponseValue reward continuation who))
        root who) -
      quittingRootSuccessorPayoff reward base root who = _
  rw [quittingRootSuccessorPayoff_eq_max_of_isZeroNash
    reward base root who hnash]
  have hbest : quittingContinuationBestResponseValue reward continuation who =
      base who + debt := by
    dsimp [base, debt, quittingTerminalDeviationDebt]
    ring
  rw [hbest, show Function.update base who (base who + debt) =
      Function.update base who (base who + debt) by rfl,
    quittingRootContinuePayoff_update_add]

/-- Exact-root prefixing cannot increase any player's literal terminal debt. -/
theorem quittingTerminalDeviationDebt_rootThenContinuation_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool)
    (continuation : (quittingGame reward).BehaviorProfile)
    (who : ι)
    (hnash : IsεQuittingRootNash reward
      (fun player => quittingTerminalPayoff reward continuation player) 0 root) :
    quittingTerminalDeviationDebt reward
        (quittingRootThenContinuationProfile reward root continuation) who ≤
      quittingRootOpponentContinueMass root who *
        quittingTerminalDeviationDebt reward continuation who := by
  rw [quittingTerminalDeviationDebt_rootThenContinuation_eq
    reward root continuation who hnash]
  let base : Payoff ι :=
    fun player => quittingTerminalPayoff reward continuation player
  let debt := quittingTerminalDeviationDebt reward continuation who
  let mass := quittingRootOpponentContinueMass root who
  have hdebt : 0 ≤ debt :=
    quittingTerminalDeviationDebt_nonneg reward continuation who
  have hmass : 0 ≤ mass := quittingRootOpponentContinueMass_nonneg root who
  have hmax := max_sub_max_le_max
    (quittingRootQuitPayoff reward base root who)
    (quittingRootContinuePayoff reward base root who + mass * debt)
    (quittingRootQuitPayoff reward base root who)
    (quittingRootContinuePayoff reward base root who)
  change max (quittingRootQuitPayoff reward base root who)
      (quittingRootContinuePayoff reward base root who + mass * debt) -
      max (quittingRootQuitPayoff reward base root who)
        (quittingRootContinuePayoff reward base root who) ≤ mass * debt
  calc
    _ ≤ max
        (quittingRootQuitPayoff reward base root who -
          quittingRootQuitPayoff reward base root who)
        ((quittingRootContinuePayoff reward base root who + mass * debt) -
          quittingRootContinuePayoff reward base root who) := hmax
    _ = mass * debt := by
      rw [sub_self]
      have hsub : quittingRootContinuePayoff reward base root who +
          mass * debt - quittingRootContinuePayoff reward base root who =
            mass * debt := by ring
      rw [hsub, max_eq_right (mul_nonneg hmass hdebt)]

/-- Prefixing an arbitrary root charges its actual one-coordinate Nash defect
and transports the continuation debt with the probability that all opponents
Continue.  Both the defect and the continuation payoff are computed from the
literal continuation profile. -/
theorem quittingTerminalDeviationDebt_rootThenContinuation_le_coordinateDefect_add
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool)
    (continuation : (quittingGame reward).BehaviorProfile)
    (who : ι) :
    quittingTerminalDeviationDebt reward
        (quittingRootThenContinuationProfile reward root continuation) who ≤
      quittingRootCoordinateNashDefect reward
          (fun player ↦ quittingTerminalPayoff reward continuation player)
          root who +
        quittingRootOpponentContinueMass root who *
          quittingTerminalDeviationDebt reward continuation who := by
  let tail : Payoff ι :=
    fun player ↦ quittingTerminalPayoff reward continuation player
  let debt := quittingTerminalDeviationDebt reward continuation who
  let mass := quittingRootOpponentContinueMass root who
  have hdebt : 0 ≤ debt :=
    quittingTerminalDeviationDebt_nonneg reward continuation who
  have hmass : 0 ≤ mass := quittingRootOpponentContinueMass_nonneg root who
  rw [quittingTerminalDeviationDebt,
    quittingContinuationBestResponseValue_rootThenContinuation_eq_max,
    quittingTerminalPayoff_rootThenContinuation_eq]
  have hbest : quittingContinuationBestResponseValue reward continuation who =
      tail who + debt := by
    dsimp [tail, debt, quittingTerminalDeviationDebt]
    ring
  change max
      (quittingRootQuitPayoff reward tail root who)
      (quittingRootContinuePayoff reward
        (Function.update tail who
          (quittingContinuationBestResponseValue reward continuation who))
        root who) -
      quittingRootSuccessorPayoff reward tail root who ≤ _
  rw [hbest, quittingRootContinuePayoff_update_add]
  unfold quittingRootCoordinateNashDefect
  have hmax := max_sub_max_le_max
    (quittingRootQuitPayoff reward tail root who)
    (quittingRootContinuePayoff reward tail root who + mass * debt)
    (quittingRootQuitPayoff reward tail root who)
    (quittingRootContinuePayoff reward tail root who)
  have htransport :
      max
          (quittingRootQuitPayoff reward tail root who)
          (quittingRootContinuePayoff reward tail root who + mass * debt) -
        max
          (quittingRootQuitPayoff reward tail root who)
          (quittingRootContinuePayoff reward tail root who) ≤
      mass * debt := by
    calc
      _ ≤ max
          (quittingRootQuitPayoff reward tail root who -
            quittingRootQuitPayoff reward tail root who)
          ((quittingRootContinuePayoff reward tail root who + mass * debt) -
            quittingRootContinuePayoff reward tail root who) := hmax
      _ = mass * debt := by
        rw [sub_self]
        have hsub : quittingRootContinuePayoff reward tail root who + mass * debt -
            quittingRootContinuePayoff reward tail root who = mass * debt := by
          ring
        rw [hsub, max_eq_right (mul_nonneg hmass hdebt)]
  linarith

end GameTheory
