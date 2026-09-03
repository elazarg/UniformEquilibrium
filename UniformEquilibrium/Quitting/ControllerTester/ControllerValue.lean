/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.ControllerTester.FiniteHorizonExploitability
import UniformEquilibrium.Quitting.ControllerTester.TesterFlowDuality
import UniformEquilibrium.Quitting.Root.NeverGeneratedSemanticCarrier
import UniformEquilibrium.Quitting.Classification.Existence.UniformPayoffTerminalSemanticCarrier
import UniformEquilibrium.Quitting.Classification.Existence.StationarilyGeneratedSemanticCarrier

/-!
# Compact controller value for finite quitting games

This module identifies the finite forward controller ledger with the literal
terminal semantic pair, packages fixed-length compact controller problems, and
passes their decreasing minima to the compact semantic carrier.  The resulting
targeted and target-free values retain the unrestricted behavioral tester.
-/

noncomputable section

namespace GameTheory

open Filter Math.Probability QuittingBoundaryHolonomy
open scoped Topology

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-! ## Literal finite-dimensional and semantic surfaces -/

/-- The advertised real-coordinate count of the forward ledger. -/
def quittingControllerTesterLedgerDimension (ι : Type) [Fintype ι] : ℕ :=
  4 * Fintype.card ι + 1

/-- For four players, the forward ledger has literally seventeen real coordinates. -/
theorem quittingControllerTesterLedgerDimension_fin4 :
    quittingControllerTesterLedgerDimension (Fin 4) = 17 := by
  norm_num [quittingControllerTesterLedgerDimension]

/-- The exact semantic prefix update is continuous jointly in the product root
and the supplied continuation pair. -/
theorem continuous_quittingControllerTesterSemanticPrefix
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) :
    Continuous (quittingTerminalSemanticPrefixSimplex reward) :=
  continuous_quittingTerminalSemanticPrefixSimplex reward

/-- The finite-word reachable closure is the compact literal semantic carrier. -/
theorem quittingControllerTester_reachableClosure_eq_carrier
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) :
    closure (quittingNeverGeneratedSemanticReachable reward) =
      quittingTerminalSemanticCarrier reward := by
  exact (terminalSemanticCarrier_eq_closure_neverGeneratedSemanticReachable
    reward).symm

/-- The closure of the finite-word reachable semantic set is compact. -/
theorem quittingControllerTester_reachableClosure_isCompact
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) :
    IsCompact (closure (quittingNeverGeneratedSemanticReachable reward)) := by
  rw [quittingControllerTester_reachableClosure_eq_carrier]
  exact quittingTerminalSemanticCarrier_isCompact reward

/-! ## The exact ledger/semantics bridge -/

theorem quittingControllerTesterLedgerRun_prescribedAccumulator_eq_terminal
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (cutoff : ℕ) (who : ι) :
    (quittingControllerTesterLedgerRun reward roots cutoff).prescribedAccumulator who =
      quittingRootSequenceTerminalValue reward
        (quittingTruncatedRoots roots cutoff) who 0 := by
  rw [quittingRootSequenceTerminalValue_quittingTruncatedRoots_eq_sum,
    quittingControllerTesterLedgerRun_prescribedAccumulator]
  apply Finset.sum_congr rfl
  intro time htime
  congr 1
  · rw [quittingJointSurvivalWeight_eq_prod]
    apply Finset.prod_congr rfl
    intro earlier _
    simp [quittingControllerContinueMass]

theorem quittingControllerTesterLedgerRun_opponentSurvival_eq
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (cutoff : ℕ) (who : ι) :
    (quittingControllerTesterLedgerRun reward roots cutoff).opponentSurvival who =
      quittingOpponentSurvivalWeight roots who 0 cutoff := by
  rw [quittingControllerTesterLedgerRun_opponentSurvival]
  unfold quittingOpponentSurvivalWeight
  apply Finset.prod_congr rfl
  intro time _
  simp [quittingTesterOpponentContinueMass,
    quittingFixedOpponentsContinueMass, quittingRootOpponentContinueMass]

theorem quittingControllerTesterLedgerRun_deviationAccumulator_eq
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (cutoff : ℕ) (who : ι) :
    (quittingControllerTesterLedgerRun reward roots cutoff).deviationAccumulator who =
      quittingLiveLedgerAccum reward roots who 0 cutoff := by
  rw [quittingControllerTesterLedgerRun_deviationAccumulator]
  unfold quittingLiveLedgerAccum
  apply Finset.sum_congr rfl
  intro time _
  congr 1
  · unfold quittingOpponentSurvivalWeight
    apply Finset.prod_congr rfl
    intro earlier _
    simp [quittingTesterOpponentContinueMass,
      quittingFixedOpponentsContinueMass, quittingRootOpponentContinueMass]
  · unfold quittingTesterContinueContribution
    rw [quittingRootContinuePayoff_eq_fixedOpponents]
    simp

theorem quittingTesterQuitValue_eq_fixedOpponentsQuitValue
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (time : ℕ) (who : ι) :
    quittingTesterQuitValue reward (roots time) who =
      quittingFixedOpponentsQuitValue reward roots who time := by
  unfold quittingTesterQuitValue
  rw [quittingRootQuitPayoff_eq_fixedOpponentsQuitValue]

/-- Every finite pure stopping payoff is exactly the corresponding ledger candidate. -/
theorem quittingRootSequencePureTimeTerminalValue_some_eq_ledgerCandidate
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι) (time : ℕ) :
    quittingRootSequencePureTimeTerminalValue reward roots who (some time) 0 =
      (quittingControllerTesterLedgerRun reward roots time).deviationAccumulator who +
        (quittingControllerTesterLedgerRun reward roots time).opponentSurvival who *
          quittingTesterQuitValue reward (roots time) who := by
  rw [quittingRootSequencePureTimeTerminalValue_some_eq,
    quittingControllerTesterLedgerRun_deviationAccumulator_eq,
    quittingControllerTesterLedgerRun_opponentSurvival_eq,
    quittingTesterQuitValue_eq_fixedOpponentsQuitValue]

private theorem quittingLiveLedgerAccum_truncated_eq_of_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι) {fuel cutoff : ℕ}
    (hfuel : fuel ≤ cutoff) :
    quittingLiveLedgerAccum reward (quittingTruncatedRoots roots cutoff)
        who 0 fuel =
      quittingLiveLedgerAccum reward roots who 0 fuel := by
  unfold quittingLiveLedgerAccum
  apply Finset.sum_congr rfl
  intro time htime
  simp only [zero_add]
  have ht : time < cutoff := (Finset.mem_range.mp htime).trans_le hfuel
  have hreward :
      quittingFixedOpponentsContinueReward reward
          (quittingTruncatedRoots roots cutoff) who time =
        quittingFixedOpponentsContinueReward reward roots who time := by
    unfold quittingFixedOpponentsContinueReward
    rw [quittingTruncatedRoots_of_lt roots ht]
  have hsurvival :
      quittingOpponentSurvivalWeight (quittingTruncatedRoots roots cutoff)
          who 0 time =
        quittingOpponentSurvivalWeight roots who 0 time := by
    unfold quittingOpponentSurvivalWeight
    apply Finset.prod_congr rfl
    intro earlier hearlier
    simp only [zero_add]
    have he : earlier < cutoff :=
      (Finset.mem_range.mp hearlier).trans ht
    unfold quittingFixedOpponentsContinueMass
    rw [quittingTruncatedRoots_of_lt roots he]
  rw [hreward, hsurvival]

private theorem quittingOpponentSurvivalWeight_truncated_eq_of_le
    (roots : ℕ → ι → PMF Bool) (who : ι) {fuel cutoff : ℕ}
    (hfuel : fuel ≤ cutoff) :
    quittingOpponentSurvivalWeight (quittingTruncatedRoots roots cutoff)
        who 0 fuel =
      quittingOpponentSurvivalWeight roots who 0 fuel := by
  unfold quittingOpponentSurvivalWeight
  apply Finset.prod_congr rfl
  intro time htime
  simp only [zero_add]
  have ht : time < cutoff := (Finset.mem_range.mp htime).trans_le hfuel
  unfold quittingFixedOpponentsContinueMass
  rw [quittingTruncatedRoots_of_lt roots ht]

private theorem quittingFixedOpponentsContinueReward_truncated_eq_zero_of_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι) {cutoff time : ℕ}
    (htime : cutoff ≤ time) :
    quittingFixedOpponentsContinueReward reward
        (quittingTruncatedRoots roots cutoff) who time = 0 := by
  simpa [quittingTruncatedRoots_of_le roots htime] using
    (quittingRootContinuePayoff_eq_fixedOpponents reward
      (quittingTruncatedRoots roots cutoff) who (0 : Payoff ι) time).symm

private theorem quittingFixedOpponentsContinueMass_truncated_eq_one_of_le
    (roots : ℕ → ι → PMF Bool) (who : ι) {cutoff time : ℕ}
    (htime : cutoff ≤ time) :
    quittingFixedOpponentsContinueMass
        (quittingTruncatedRoots roots cutoff) who time = 1 := by
  unfold quittingFixedOpponentsContinueMass
  rw [quittingTruncatedRoots_of_le roots htime]
  have hupdate : Function.update
      (quittingAllContinueRoot : ι → PMF Bool) who (PMF.pure false) =
        quittingAllContinueRoot := by
    funext other
    by_cases hother : other = who
    · subst other
      simp [quittingAllContinueRoot]
    · simp [hother, quittingAllContinueRoot]
  rw [hupdate, quittingStationaryContinueMass_allContinueRoot]

private theorem quittingFixedOpponentsQuitValue_truncated_eq_singleton_of_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι) {cutoff time : ℕ}
    (htime : cutoff ≤ time) :
    quittingFixedOpponentsQuitValue reward
        (quittingTruncatedRoots roots cutoff) who time =
      reward (quittingSingletonTerminal who) who := by
  rw [← quittingRootQuitPayoff_eq_fixedOpponentsQuitValue reward
    (quittingTruncatedRoots roots cutoff) who (0 : Payoff ι) time]
  simp [quittingTruncatedRoots_of_le roots htime]

private theorem quittingLiveLedgerAccum_truncated_add
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι) (cutoff later : ℕ) :
    quittingLiveLedgerAccum reward (quittingTruncatedRoots roots cutoff)
        who 0 (cutoff + later) =
      quittingLiveLedgerAccum reward roots who 0 cutoff := by
  induction later with
  | zero =>
      simpa using quittingLiveLedgerAccum_truncated_eq_of_le
        reward roots who (le_refl cutoff)
  | succ later ih =>
      rw [show cutoff + (later + 1) = cutoff + later + 1 by omega,
        quittingLiveLedgerAccum_zero_succ, ih,
        quittingFixedOpponentsContinueReward_truncated_eq_zero_of_le
          reward roots who (Nat.le_add_right cutoff later), mul_zero, add_zero]

private theorem quittingOpponentSurvivalWeight_truncated_add
    (roots : ℕ → ι → PMF Bool) (who : ι) (cutoff later : ℕ) :
    quittingOpponentSurvivalWeight (quittingTruncatedRoots roots cutoff)
        who 0 (cutoff + later) =
      quittingOpponentSurvivalWeight roots who 0 cutoff := by
  induction later with
  | zero =>
      simpa using quittingOpponentSurvivalWeight_truncated_eq_of_le
        roots who (le_refl cutoff)
  | succ later ih =>
      rw [show cutoff + (later + 1) = cutoff + later + 1 by omega,
        quittingOpponentSurvivalWeight_zero_succ, ih,
        quittingFixedOpponentsContinueMass_truncated_eq_one_of_le
          roots who (Nat.le_add_right cutoff later), mul_one]

private theorem quittingRootSequencePureTimeTerminalValue_truncated_some_add
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι) (cutoff later : ℕ) :
    quittingRootSequencePureTimeTerminalValue reward
        (quittingTruncatedRoots roots cutoff) who (some (cutoff + later)) 0 =
      (quittingControllerTesterLedgerRun reward roots cutoff).deviationAccumulator who +
        (quittingControllerTesterLedgerRun reward roots cutoff).opponentSurvival who *
          reward (quittingSingletonTerminal who) who := by
  rw [quittingRootSequencePureTimeTerminalValue_some_eq,
    quittingLiveLedgerAccum_truncated_add,
    quittingOpponentSurvivalWeight_truncated_add,
    quittingFixedOpponentsQuitValue_truncated_eq_singleton_of_le
      reward roots who (Nat.le_add_right cutoff later),
    quittingControllerTesterLedgerRun_deviationAccumulator_eq,
    quittingControllerTesterLedgerRun_opponentSurvival_eq]

/-- The Never response to a finite word followed by all Continue is exactly
the deviation-accumulator coordinate at the word endpoint. -/
theorem quittingRootSequencePureTimeTerminalValue_truncated_none
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι) (cutoff : ℕ) :
    quittingRootSequencePureTimeTerminalValue reward
        (quittingTruncatedRoots roots cutoff) who none 0 =
      (quittingControllerTesterLedgerRun reward roots cutoff).deviationAccumulator who := by
  have heventually : ∀ᶠ fuel : ℕ in atTop,
      quittingLiveLedgerAccum reward (quittingTruncatedRoots roots cutoff)
          who 0 fuel =
        (quittingControllerTesterLedgerRun reward roots cutoff).deviationAccumulator who := by
    apply eventually_atTop.mpr
    refine ⟨cutoff, fun fuel hfuel => ?_⟩
    obtain ⟨later, rfl⟩ := Nat.exists_eq_add_of_le hfuel
    rw [quittingLiveLedgerAccum_truncated_add,
      quittingControllerTesterLedgerRun_deviationAccumulator_eq]
  have hconstant : Tendsto
      (fun fuel => quittingLiveLedgerAccum reward
        (quittingTruncatedRoots roots cutoff) who 0 fuel)
      atTop (nhds
        ((quittingControllerTesterLedgerRun reward roots cutoff).deviationAccumulator who)) :=
    Filter.Tendsto.congr' (Filter.EventuallyEq.symm heventually)
      tendsto_const_nhds
  exact tendsto_nhds_unique
    (tendsto_quittingLiveLedgerAccum reward
      (quittingTruncatedRoots roots cutoff) who) hconstant

private theorem quittingRootSequencePureTimeTerminalValue_truncated_some_of_lt
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι) {cutoff time : ℕ}
    (htime : time < cutoff) :
    quittingRootSequencePureTimeTerminalValue reward
        (quittingTruncatedRoots roots cutoff) who (some time) 0 =
      (quittingControllerTesterLedgerRun reward roots time).deviationAccumulator who +
        (quittingControllerTesterLedgerRun reward roots time).opponentSurvival who *
          quittingTesterQuitValue reward (roots time) who := by
  have hquit : quittingFixedOpponentsQuitValue reward
      (quittingTruncatedRoots roots cutoff) who time =
        quittingFixedOpponentsQuitValue reward roots who time := by
    unfold quittingFixedOpponentsQuitValue
    rw [quittingTruncatedRoots_of_lt roots htime]
  rw [quittingRootSequencePureTimeTerminalValue_some_eq,
    quittingLiveLedgerAccum_truncated_eq_of_le reward roots who htime.le,
    quittingOpponentSurvivalWeight_truncated_eq_of_le roots who htime.le,
    hquit,
    quittingControllerTesterLedgerRun_deviationAccumulator_eq,
    quittingControllerTesterLedgerRun_opponentSurvival_eq,
    quittingTesterQuitValue_eq_fixedOpponentsQuitValue]

/-- The unrestricted behavioral best-response cap of a finite word followed
by all Continue is exactly the cap coordinate read from the forward ledger.
The second branch includes both later solo Quit and Never. -/
theorem quittingContinuationBestResponseValue_truncated_eq_ledger
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (cutoff : ℕ) (who : ι) :
    quittingContinuationBestResponseValue reward
        (quittingRootSequenceProfile reward
          (quittingTruncatedRoots roots cutoff) 0) who =
      ((quittingControllerTesterLedgerRun reward roots cutoff).neverTailSemanticPair
        reward).2 who := by
  rw [show quittingContinuationBestResponseValue reward
      (quittingRootSequenceProfile reward
        (quittingTruncatedRoots roots cutoff) 0) who =
      quittingTesterTailBestResponseValue reward
        (quittingTruncatedRoots roots cutoff) who 0 by rfl,
    quittingTesterTailBestResponseValue_zero_eq_sSup_pureTime]
  let values : Set ℝ := Set.range fun quitTime : Option ℕ =>
    quittingRootSequencePureTimeTerminalValue reward
      (quittingTruncatedRoots roots cutoff) who quitTime 0
  have hbounded : BddAbove values := by
    refine ⟨quittingRewardBound reward, ?_⟩
    rintro value ⟨quitTime, rfl⟩
    let profile := quittingRootSequenceProfile reward
      (quittingTruncatedRoots roots cutoff) 0
    have hpayoff := abs_quittingTerminalPayoff_le reward
      (Function.update profile who
        (quittingPureTimeBehaviorStrategy reward who quitTime)) who
      (abs_reward_le_quittingRewardBound reward)
    rw [quittingTerminalPayoff_update_pureTimeBehaviorStrategy,
      quittingProfileLiveRoot_quittingRootSequenceProfile_zero] at hpayoff
    exact (le_abs_self _).trans hpayoff
  have hledger := quittingControllerTesterLedgerRun_isBounded reward roots cutoff
  apply le_antisymm
  · apply csSup_le (Set.range_nonempty _)
    rintro value ⟨quitTime, rfl⟩
    cases quitTime with
    | none =>
        change quittingRootSequencePureTimeTerminalValue reward
          (quittingTruncatedRoots roots cutoff) who none 0 ≤ _
        rw [quittingRootSequencePureTimeTerminalValue_truncated_none]
        unfold QuittingControllerTesterLedger.neverTailSemanticPair
        exact le_max_of_le_right <| le_add_of_nonneg_right <|
          mul_nonneg (hledger.opponentSurvival_nonneg who) (le_max_right _ _)
    | some time =>
        change quittingRootSequencePureTimeTerminalValue reward
          (quittingTruncatedRoots roots cutoff) who (some time) 0 ≤ _
        by_cases htime : time < cutoff
        · rw [quittingRootSequencePureTimeTerminalValue_truncated_some_of_lt
            reward roots who htime]
          unfold QuittingControllerTesterLedger.neverTailSemanticPair
          exact (quittingControllerTesterLedgerRun_candidate_le_finiteQuitCap
            reward roots cutoff who htime).trans (le_max_left _ _)
        · obtain ⟨later, rfl⟩ := Nat.exists_eq_add_of_le (Nat.not_lt.mp htime)
          rw [quittingRootSequencePureTimeTerminalValue_truncated_some_add]
          unfold QuittingControllerTesterLedger.neverTailSemanticPair
          apply le_max_of_le_right
          simpa only [add_comm] using add_le_add_left
            (mul_le_mul_of_nonneg_left
              (le_max_left (reward (quittingSingletonTerminal who) who) (0 : ℝ))
              (hledger.opponentSurvival_nonneg who))
            ((quittingControllerTesterLedgerRun reward roots cutoff).deviationAccumulator who)
  · unfold QuittingControllerTesterLedger.neverTailSemanticPair
    apply max_le
    · apply quittingControllerTesterLedgerRun_finiteQuitCap_le
      · have hnever : -quittingRewardBound reward ≤
            quittingRootSequencePureTimeTerminalValue reward
              (quittingTruncatedRoots roots cutoff) who none 0 := by
          rw [quittingRootSequencePureTimeTerminalValue_truncated_none]
          have hp := hledger.deviationAccumulator_le who
          have hL := hledger.opponentSurvival_nonneg who
          have hLone := hledger.opponentSurvival_le_one who
          have hR := quittingRewardBound_nonneg reward
          nlinarith [neg_le_of_abs_le hp, mul_nonneg hR hL]
        exact hnever.trans (le_csSup hbounded ⟨none, rfl⟩)
      · intro time htime
        rw [← quittingRootSequencePureTimeTerminalValue_truncated_some_of_lt
          reward roots who htime]
        exact le_csSup hbounded ⟨some time, rfl⟩
    · have hnever := le_csSup hbounded ⟨none, rfl⟩
      have hquit := le_csSup hbounded ⟨some cutoff, rfl⟩
      change quittingRootSequencePureTimeTerminalValue reward
        (quittingTruncatedRoots roots cutoff) who none 0 ≤ _ at hnever
      change quittingRootSequencePureTimeTerminalValue reward
        (quittingTruncatedRoots roots cutoff) who (some cutoff) 0 ≤ _ at hquit
      rw [quittingRootSequencePureTimeTerminalValue_truncated_none] at hnever
      have hquitFormula :=
        quittingRootSequencePureTimeTerminalValue_truncated_some_add
          reward roots who cutoff 0
      simp only [Nat.add_zero] at hquitFormula
      rw [hquitFormula] at hquit
      rw [mul_max_of_nonneg _ _ (hledger.opponentSurvival_nonneg who), add_max]
      simpa using max_le hquit hnever

/-- The literal semantic pair of a finite root word followed by all Continue
is exactly the finite forward-ledger semantic readout. -/
theorem quittingTerminalSemanticPair_truncated_eq_ledger
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (cutoff : ℕ) :
    quittingTerminalSemanticPair reward
        (quittingRootSequenceProfile reward
          (quittingTruncatedRoots roots cutoff) 0) =
      (quittingControllerTesterLedgerRun reward roots cutoff).neverTailSemanticPair
        reward := by
  apply Prod.ext
  · funext who
    exact quittingControllerTesterLedgerRun_prescribedAccumulator_eq_terminal
      reward roots cutoff who |>.symm
  · funext who
    exact quittingContinuationBestResponseValue_truncated_eq_ledger
      reward roots cutoff who

/-! ## Compact semantic minima -/

/-- Raw maximum cap debt of a semantic pair. Unlike
`quittingTerminalSemanticExploitability`, this definition does not insert a
positive part and is therefore the literal target-free obstacle on the full
reward box. -/
def quittingControllerRawMaximumDebt [Nonempty ι]
    (pair : QuittingTerminalSemanticPair ι) : ℝ :=
  QuittingBoundaryHolonomy.finitePlayerMax fun who =>
    pair.2 who - pair.1 who

omit [DecidableEq ι] in
/-- Raw maximum cap debt is continuous on the ambient semantic-pair space. -/
theorem continuous_quittingControllerRawMaximumDebt [Nonempty ι] :
    Continuous (quittingControllerRawMaximumDebt :
      QuittingTerminalSemanticPair ι → ℝ) := by
  unfold quittingControllerRawMaximumDebt
    QuittingBoundaryHolonomy.finitePlayerMax
  apply Continuous.finset_sup'_apply Finset.univ_nonempty
  intro who _
  exact continuous_quittingTerminalSemanticDebt who

/-- On genuine terminal-semantic pairs every cap debt is nonnegative, so the
raw maximum debt and positive-part exploitability coincide exactly. -/
theorem quittingControllerRawMaximumDebt_eq_semanticExploitability_of_mem_carrier
    [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    {pair : QuittingTerminalSemanticPair ι}
    (hpair : pair ∈ quittingTerminalSemanticCarrier reward) :
    quittingControllerRawMaximumDebt pair =
      quittingTerminalSemanticExploitability pair := by
  unfold quittingControllerRawMaximumDebt
    quittingTerminalSemanticExploitability quittingTerminalSemanticDebt
  congr 1
  funext who
  rw [max_eq_right]
  exact quittingTerminalSemanticDebt_nonneg_of_mem_carrier reward hpair who

omit [DecidableEq ι] in
/-- On a symmetric semantic reward box, raw maximum debt is bounded by twice
the displayed coordinate bound. -/
theorem abs_quittingControllerRawMaximumDebt_le_of_mem_box [Nonempty ι]
    {pair : QuittingTerminalSemanticPair ι} {bound : ℝ}
    (_hbound : 0 ≤ bound)
    (hpair : pair ∈ quittingTerminalSemanticBox ι bound) :
    |quittingControllerRawMaximumDebt pair| ≤ 2 * bound := by
  apply abs_le.mpr
  constructor
  · let who : ι := Classical.choice inferInstance
    exact (by
      have hcoordinate := QuittingBoundaryHolonomy.le_finitePlayerMax
        (fun player : ι => pair.2 player - pair.1 player) who
      have hu := hpair.1.2 who
      have hb := hpair.2.1 who
      unfold quittingControllerRawMaximumDebt
      linarith)
  · apply QuittingBoundaryHolonomy.finitePlayerMax_le
    intro who
    have hu := hpair.1.1 who
    have hb := hpair.2.2 who
    linarith

/-- Fixed-target loss of one semantic pair. The second term is the maximum
unrestricted behavioral cap debt. -/
def quittingControllerTargetLoss [Nonempty ι]
    (target : Payoff ι) (pair : QuittingTerminalSemanticPair ι) : ℝ :=
  max ‖pair.1 - target‖ (quittingControllerRawMaximumDebt pair)

omit [DecidableEq ι] in
theorem continuous_quittingControllerTargetLoss [Nonempty ι]
    (target : Payoff ι) :
    Continuous (quittingControllerTargetLoss target :
      QuittingTerminalSemanticPair ι → ℝ) := by
  unfold quittingControllerTargetLoss
  apply Continuous.max
  · fun_prop
  · exact continuous_quittingControllerRawMaximumDebt

/-- A fixed-target controller loss attains its minimum on the compact
terminal-semantic carrier. -/
theorem exists_minimum_quittingControllerTargetLoss [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (target : Payoff ι) :
    ∃ pair ∈ quittingTerminalSemanticCarrier reward,
      ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
        quittingControllerTargetLoss target pair ≤
          quittingControllerTargetLoss target candidate := by
  obtain ⟨pair, hpair, hminimum⟩ :=
    (quittingTerminalSemanticCarrier_isCompact reward).exists_isMinOn
      (quittingTerminalSemanticCarrier_nonempty reward)
      (continuous_quittingControllerTargetLoss target).continuousOn
  exact ⟨pair, hpair, fun candidate hcandidate => hminimum hcandidate⟩

/-- Canonical choice of a carrier minimizer for the fixed-target value. -/
def quittingControllerTargetMinimizer [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (target : Payoff ι) : QuittingTerminalSemanticPair ι :=
  Classical.choose (exists_minimum_quittingControllerTargetLoss reward target)

theorem quittingControllerTargetMinimizer_mem [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (target : Payoff ι) :
    quittingControllerTargetMinimizer reward target ∈
      quittingTerminalSemanticCarrier reward :=
  (Classical.choose_spec
    (exists_minimum_quittingControllerTargetLoss reward target)).1

theorem quittingControllerTargetMinimizer_isMinimum [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (target : Payoff ι) {candidate : QuittingTerminalSemanticPair ι}
    (hcandidate : candidate ∈ quittingTerminalSemanticCarrier reward) :
    quittingControllerTargetLoss target
        (quittingControllerTargetMinimizer reward target) ≤
      quittingControllerTargetLoss target candidate :=
  (Classical.choose_spec
    (exists_minimum_quittingControllerTargetLoss reward target)).2
      candidate hcandidate

/-- The compact fixed-target controller--tester value `W_r(v)`. -/
def quittingControllerTargetValue [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (target : Payoff ι) : ℝ :=
  quittingControllerTargetLoss target
    (quittingControllerTargetMinimizer reward target)

theorem quittingControllerTargetValue_eq_minimum [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (target : Payoff ι) :
    quittingControllerTargetMinimizer reward target ∈
        quittingTerminalSemanticCarrier reward ∧
      quittingControllerTargetValue reward target =
        quittingControllerTargetLoss target
          (quittingControllerTargetMinimizer reward target) ∧
      ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
        quittingControllerTargetValue reward target ≤
          quittingControllerTargetLoss target candidate := by
  exact ⟨quittingControllerTargetMinimizer_mem reward target, rfl,
    fun candidate hcandidate =>
      quittingControllerTargetMinimizer_isMinimum reward target hcandidate⟩

/-- Canonical choice of a carrier minimizer of maximum unrestricted
behavioral cap debt. -/
def quittingControllerTesterMinimizer [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) :
    QuittingTerminalSemanticPair ι :=
  Classical.choose <|
    (quittingTerminalSemanticCarrier_isCompact reward).exists_isMinOn
      (quittingTerminalSemanticCarrier_nonempty reward)
      continuous_quittingTerminalSemanticExploitability.continuousOn

theorem quittingControllerTesterMinimizer_mem [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) :
    quittingControllerTesterMinimizer reward ∈
      quittingTerminalSemanticCarrier reward := by
  unfold quittingControllerTesterMinimizer
  exact (Classical.choose_spec
    ((quittingTerminalSemanticCarrier_isCompact reward).exists_isMinOn
      (quittingTerminalSemanticCarrier_nonempty reward)
      continuous_quittingTerminalSemanticExploitability.continuousOn)).1

theorem quittingControllerTesterMinimizer_isMinimum [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    {candidate : QuittingTerminalSemanticPair ι}
    (hcandidate : candidate ∈ quittingTerminalSemanticCarrier reward) :
    quittingTerminalSemanticExploitability
        (quittingControllerTesterMinimizer reward) ≤
      quittingTerminalSemanticExploitability candidate := by
  unfold quittingControllerTesterMinimizer
  exact (Classical.choose_spec
    ((quittingTerminalSemanticCarrier_isCompact reward).exists_isMinOn
      (quittingTerminalSemanticCarrier_nonempty reward)
      continuous_quittingTerminalSemanticExploitability.continuousOn)).2
        hcandidate

/-- The target-free compact controller--tester value `eta(r)`. -/
def quittingControllerTesterValue [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) : ℝ :=
  quittingTerminalSemanticExploitability
    (quittingControllerTesterMinimizer reward)

omit [DecidableEq ι] in
theorem quittingControllerSemanticExploitability_nonneg [Nonempty ι]
    (pair : QuittingTerminalSemanticPair ι) :
    0 ≤ quittingTerminalSemanticExploitability pair := by
  let who : ι := Classical.choice inferInstance
  exact (le_max_left 0 (quittingTerminalSemanticDebt pair who)).trans
    (QuittingBoundaryHolonomy.le_finitePlayerMax
      (fun player => max 0 (quittingTerminalSemanticDebt pair player)) who)

theorem quittingControllerTesterValue_eq_minimum [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) :
    quittingControllerTesterMinimizer reward ∈
        quittingTerminalSemanticCarrier reward ∧
      quittingControllerTesterValue reward =
        quittingTerminalSemanticExploitability
          (quittingControllerTesterMinimizer reward) ∧
      ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
        quittingControllerTesterValue reward ≤
          quittingTerminalSemanticExploitability candidate := by
  exact ⟨quittingControllerTesterMinimizer_mem reward, rfl,
    fun candidate hcandidate =>
      quittingControllerTesterMinimizer_isMinimum reward hcandidate⟩

theorem quittingControllerTesterValue_nonneg [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) :
    0 ≤ quittingControllerTesterValue reward := by
  exact quittingControllerSemanticExploitability_nonneg _

/-- On the semantic carrier, the positive parts in the target-free objective
are redundant: every cap debt is nonnegative. -/
theorem quittingControllerTesterValue_eq_max_debt [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) :
    quittingControllerTesterValue reward =
      QuittingBoundaryHolonomy.finitePlayerMax fun who =>
        (quittingControllerTesterMinimizer reward).2 who -
          (quittingControllerTesterMinimizer reward).1 who := by
  exact (quittingControllerRawMaximumDebt_eq_semanticExploitability_of_mem_carrier
    reward (quittingControllerTesterMinimizer_mem reward)).symm

/-- The literal raw maximum debt reaches its minimum on the semantic carrier at
the controller--tester minimizer, and that minimum is exactly `eta(r)`. -/
theorem quittingControllerTesterValue_eq_minimum_rawMaximumDebt [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) :
    quittingControllerTesterMinimizer reward ∈
        quittingTerminalSemanticCarrier reward ∧
      quittingControllerTesterValue reward =
        quittingControllerRawMaximumDebt
          (quittingControllerTesterMinimizer reward) ∧
      ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
        quittingControllerTesterValue reward ≤
          quittingControllerRawMaximumDebt candidate := by
  refine ⟨quittingControllerTesterMinimizer_mem reward,
    quittingControllerTesterValue_eq_max_debt reward, ?_⟩
  intro candidate hcandidate
  rw [quittingControllerRawMaximumDebt_eq_semanticExploitability_of_mem_carrier
    reward hcandidate]
  exact quittingControllerTesterMinimizer_isMinimum reward hcandidate

/-- The target-free value is zero exactly when the game has a
uniform-equilibrium payoff. -/
theorem quittingControllerTesterValue_eq_zero_iff_exists_uniformEquilibriumPayoff
    [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) :
    quittingControllerTesterValue reward = 0 ↔
      ∃ target : Payoff ι,
        (quittingGame reward).IsUniformEquilibriumPayoff none target := by
  constructor
  · intro hzero
    let pair := quittingControllerTesterMinimizer reward
    have hpair : pair ∈ quittingTerminalSemanticCarrier reward :=
      quittingControllerTesterMinimizer_mem reward
    have hdebtZero : ∀ who, quittingTerminalSemanticDebt pair who = 0 := by
      intro who
      have hnonneg := quittingTerminalSemanticDebt_nonneg_of_mem_carrier
        reward hpair who
      have hle : max 0 (quittingTerminalSemanticDebt pair who) ≤
          quittingControllerTesterValue reward := by
        unfold quittingControllerTesterValue pair
        change max 0 (quittingTerminalSemanticDebt
          (quittingControllerTesterMinimizer reward) who) ≤
            QuittingBoundaryHolonomy.finitePlayerMax fun player =>
              max 0 (quittingTerminalSemanticDebt
                (quittingControllerTesterMinimizer reward) player)
        exact QuittingBoundaryHolonomy.le_finitePlayerMax
          (fun player : ι => max 0 (quittingTerminalSemanticDebt
            (quittingControllerTesterMinimizer reward) player)) who
      rw [hzero] at hle
      exact le_antisymm ((le_max_right 0 _).trans hle) hnonneg
    have hpairEq : pair = (pair.1, pair.1) := by
      apply Prod.ext
      · rfl
      · funext who
        have := hdebtZero who
        unfold quittingTerminalSemanticDebt at this
        linarith
    have hdiagonal : (pair.1, pair.1) ∈
        quittingTerminalSemanticCarrier reward := by
      rwa [← hpairEq]
    exact ⟨pair.1,
      (isUniformEquilibriumPayoff_iff_diagonal_mem_terminalSemanticCarrier
        reward pair.1).2 hdiagonal⟩
  · rintro ⟨target, huniform⟩
    have hdiagonal : (target, target) ∈ quittingTerminalSemanticCarrier reward :=
      (isUniformEquilibriumPayoff_iff_diagonal_mem_terminalSemanticCarrier
        reward target).1 huniform
    apply le_antisymm
    · have hminimum := quittingControllerTesterMinimizer_isMinimum
        reward hdiagonal
      have hdiagonalZero :
          quittingTerminalSemanticExploitability (target, target) = 0 := by
        simp [quittingTerminalSemanticExploitability,
          quittingTerminalSemanticDebt,
          QuittingBoundaryHolonomy.finitePlayerMax]
      exact hminimum.trans_eq hdiagonalZero
    · exact quittingControllerTesterValue_nonneg reward

/-- Choosing the payoff coordinate of a target-free minimizer eliminates the
delivery loss exactly. Thus optimization over targets contributes no extra
compactness assumption. -/
theorem quittingControllerTargetValue_at_minimizer_eq_targetFree [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) :
    quittingControllerTargetValue reward
        (quittingControllerTesterMinimizer reward).1 =
      quittingControllerTesterValue reward := by
  apply le_antisymm
  · calc
      quittingControllerTargetValue reward
          (quittingControllerTesterMinimizer reward).1 ≤
        quittingControllerTargetLoss
          (quittingControllerTesterMinimizer reward).1
          (quittingControllerTesterMinimizer reward) :=
        quittingControllerTargetMinimizer_isMinimum reward _
          (quittingControllerTesterMinimizer_mem reward)
      _ = quittingControllerTesterValue reward := by
        rw [quittingControllerTargetLoss, sub_self, norm_zero,
          max_eq_right]
        · exact (quittingControllerTesterValue_eq_max_debt reward).symm
        · rw [quittingControllerRawMaximumDebt_eq_semanticExploitability_of_mem_carrier
            reward (quittingControllerTesterMinimizer_mem reward)]
          exact quittingControllerSemanticExploitability_nonneg _
  · unfold quittingControllerTargetValue quittingControllerTargetLoss
    exact le_max_of_le_right <|
      (quittingControllerTesterValue_eq_minimum_rawMaximumDebt reward).2.2 _
        (quittingControllerTargetMinimizer_mem reward _)

/-- The target-free value lower-bounds every fixed-target value. -/
theorem quittingControllerTesterValue_le_targetValue [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (target : Payoff ι) :
    quittingControllerTesterValue reward ≤
      quittingControllerTargetValue reward target := by
  unfold quittingControllerTargetValue quittingControllerTargetLoss
  exact ((quittingControllerTesterValue_eq_minimum_rawMaximumDebt reward).2.2 _
    (quittingControllerTargetMinimizer_mem reward target)).trans
      (le_max_right _ _)

end GameTheory
