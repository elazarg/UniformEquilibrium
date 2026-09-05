import UniformEquilibrium.Quitting.Cycles.ConditionedPeriodicRenewal
import UniformEquilibrium.Quitting.Stationary.MinMax

/-! # Signed finite-response bounds under actual prefix repetition -/

noncomputable section

namespace GameTheory

open Filter Math.Probability

variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem quittingLiveLedgerAccum_congr
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (first second : ℕ → ι → PMF Bool) (who : ι) (start fuel : ℕ)
    (hagree : ∀ offset < fuel, first (start + offset) = second (start + offset)) :
    quittingLiveLedgerAccum reward first who start fuel =
      quittingLiveLedgerAccum reward second who start fuel := by
  unfold quittingLiveLedgerAccum
  apply Finset.sum_congr rfl
  intro offset hoffset
  have hlt := Finset.mem_range.mp hoffset
  rw [quittingOpponentSurvivalWeight_congr first second who start offset
    (fun earlier hearlier ↦ hagree earlier (hearlier.trans hlt))]
  unfold quittingFixedOpponentsContinueReward
  rw [hagree offset hlt]

/-- A finite deterministic response sees only roots through its own date. -/
theorem quittingRootSequencePureTimeTerminalValue_some_congr
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (first second : ℕ → ι → PMF Bool) (who : ι) (time : ℕ)
    (hagree : ∀ date ≤ time, first date = second date) :
    quittingRootSequencePureTimeTerminalValue reward first who (some time) 0 =
      quittingRootSequencePureTimeTerminalValue reward second who (some time) 0 := by
  rw [quittingRootSequencePureTimeTerminalValue_some_eq,
    quittingRootSequencePureTimeTerminalValue_some_eq,
    quittingLiveLedgerAccum_congr reward first second who 0 time
      (fun offset hoffset ↦ by simpa using hagree offset hoffset.le),
    quittingOpponentSurvivalWeight_congr first second who 0 time
      (fun offset hoffset ↦ by simpa using hagree offset hoffset.le)]
  unfold quittingFixedOpponentsQuitValue
  rw [hagree time le_rfl]

theorem quittingTruncatedNeverValue_eq_liveLedgerAccum
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι) (cutoff : ℕ) :
    quittingRootSequenceHazardTerminalValue reward (quittingTruncatedRoots roots cutoff)
      who (quittingPureTimeHazard none) 0 =
      quittingLiveLedgerAccum reward roots who 0 cutoff := by
  have hhazard : quittingTruncatedHazard (quittingPureTimeHazard none) cutoff =
      quittingPureTimeHazard none := by
    funext time
    simp [quittingTruncatedHazard, quittingPureTimeHazard]
  unfold quittingRootSequenceHazardTerminalValue
  rw [← hhazard, quittingRootSequenceUpdate_quittingTruncatedRoots,
    quittingRootSequenceTerminalValue_quittingTruncatedRoots_eq_sum]
  unfold quittingLiveLedgerAccum
  apply Finset.sum_congr rfl
  intro offset _
  rw [quittingJointSurvivalWeight_update_none_eq_opponentSurvivalWeight]
  simp only [Nat.zero_add]
  rfl

theorem quittingOpponentSurvivalWeight_periodizedPrefix
    (roots : ℕ → ι → PMF Bool) (who : ι) (window : ℕ) :
    quittingOpponentSurvivalWeight (quittingPeriodizedTailWindowRoots roots 0 window)
      who 0 (window + 1) = quittingOpponentSurvivalWeight roots who 0 (window + 1) := by
  apply quittingOpponentSurvivalWeight_congr
  intro offset hoffset
  simpa only [Nat.zero_add] using
    quittingPeriodizedTailWindowRoots_of_lt roots 0 window offset hoffset

theorem quittingLiveLedgerAccum_periodizedPrefix
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι) (window : ℕ) :
    quittingLiveLedgerAccum reward (quittingPeriodizedTailWindowRoots roots 0 window)
      who 0 (window + 1) = quittingLiveLedgerAccum reward roots who 0 (window + 1) := by
  apply quittingLiveLedgerAccum_congr
  intro offset hoffset
  simpa only [Nat.zero_add] using
    quittingPeriodizedTailWindowRoots_of_lt roots 0 window offset hoffset

theorem quittingPeriodicWindowRefusalValue_periodizedPrefix_eq_div
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι) (window : ℕ)
    (hcontracts : quittingOpponentSurvivalWeight roots who 0 (window + 1) < 1) :
    quittingPeriodicWindowRefusalValue reward
      (quittingPeriodizedTailWindowRoots roots 0 window) who =
      quittingLiveLedgerAccum reward roots who 0 (window + 1) /
        (1 - quittingOpponentSurvivalWeight roots who 0 (window + 1)) := by
  have heq := quittingPeriodicWindowRefusalValue_eq_prefix_add_survival_mul reward
    (quittingPeriodizedTailWindowRoots roots 0 window) who (window + 1)
    (quittingPeriodizedTailWindowRoots_add_period roots 0 window)
  rw [quittingTruncatedNeverValue_eq_liveLedgerAccum,
    quittingLiveLedgerAccum_periodizedPrefix,
    quittingOpponentSurvivalWeight_periodizedPrefix] at heq
  apply (eq_div_iff (show 1 - quittingOpponentSurvivalWeight roots who 0 (window + 1) ≠ 0
    by linarith)).mpr
  nlinarith

theorem quittingPureTimeValue_periodizedPrefix_firstPass
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι) (window : ℕ)
    (phase : Fin (window + 1)) :
    quittingRootSequencePureTimeTerminalValue reward
      (quittingPeriodizedTailWindowRoots roots 0 window) who (some phase.val) 0 =
      quittingRootSequencePureTimeTerminalValue reward roots who (some phase.val) 0 := by
  apply quittingRootSequencePureTimeTerminalValue_some_congr
  intro date hdate
  simpa only [Nat.zero_add] using
    quittingPeriodizedTailWindowRoots_of_lt roots 0 window date (hdate.trans_lt phase.isLt)

/-- Exact signed interpolation for a response in any later block. -/
theorem quittingPureTimeValue_periodizedPrefix_block_interpolation
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι) (window : ℕ)
    (hcontracts : quittingOpponentSurvivalWeight roots who 0 (window + 1) < 1)
    (block : ℕ) (phase : Fin (window + 1)) :
    quittingRootSequencePureTimeTerminalValue reward
      (quittingPeriodizedTailWindowRoots roots 0 window) who
      (some (block * (window + 1) + phase.val)) 0 =
      (1 - quittingOpponentSurvivalWeight roots who 0 (window + 1) ^ block) *
        (quittingLiveLedgerAccum reward roots who 0 (window + 1) /
          (1 - quittingOpponentSurvivalWeight roots who 0 (window + 1))) +
      quittingOpponentSurvivalWeight roots who 0 (window + 1) ^ block *
        quittingRootSequencePureTimeTerminalValue reward roots who (some phase.val) 0 := by
  induction block with
  | zero =>
      simpa only [Nat.zero_mul, Nat.zero_add, pow_zero, sub_self, zero_mul, one_mul,
        zero_add] using
        quittingPureTimeValue_periodizedPrefix_firstPass reward roots who window phase
  | succ block ih =>
      rw [show (block + 1) * (window + 1) + phase.val =
        (window + 1) + (block * (window + 1) + phase.val) by ring]
      rw [quittingPeriodicPureTimeTerminalValue_add_period_eq_interpolation reward _ who
        (window + 1) _ (quittingPeriodizedTailWindowRoots_add_period roots 0 window),
        quittingPeriodicWindowRefusalValue_periodizedPrefix_eq_div
          reward roots who window hcontracts,
        quittingOpponentSurvivalWeight_periodizedPrefix, ih, pow_succ]
      ring

/-- Repetition constructs one actual independent behavioral profile whose full
cap is bounded by its signed first-pass finite response bound and renewal value. -/
theorem quittingBestReplyValue_periodizedPrefix_le_max
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι) (window : ℕ) {finiteBound : ℝ}
    (hfinite : ∀ phase : Fin (window + 1),
      quittingRootSequencePureTimeTerminalValue reward roots who (some phase.val) 0 ≤ finiteBound)
    (hcontracts : quittingOpponentSurvivalWeight roots who 0 (window + 1) < 1) :
    quittingBestReplyValue reward (quittingRootSequenceProfile reward
      (quittingPeriodizedTailWindowRoots roots 0 window) 0) who ≤
      max finiteBound (quittingLiveLedgerAccum reward roots who 0 (window + 1) /
        (1 - quittingOpponentSurvivalWeight roots who 0 (window + 1))) := by
  change sSup (Set.range fun deviation : (quittingGame reward).BehaviorStrategy who ↦
    quittingTerminalPayoff reward (Function.update (quittingRootSequenceProfile reward
      (quittingPeriodizedTailWindowRoots roots 0 window) 0) who deviation) who) ≤ _
  rw [sSup_range_quittingTerminalPayoff_update_eq_periodicWindow reward _ who (window + 1)
    (by simpa only [quittingProfileLiveRoot_quittingRootSequenceProfile_zero] using
      quittingPeriodizedTailWindowRoots_add_period roots 0 window)]
  rw [quittingProfileLiveRoot_quittingRootSequenceProfile_zero]
  unfold quittingPeriodicWindowBestResponseValue
  apply max_le
  · rw [quittingPeriodicWindowRefusalValue_periodizedPrefix_eq_div
      reward roots who window hcontracts]
    exact le_max_right _ _
  · apply Finset.sup'_le
    intro phase _
    change quittingRootSequencePureTimeTerminalValue reward _ who (some phase.val) 0 ≤ _
    rw [quittingPureTimeValue_periodizedPrefix_firstPass]
    exact (hfinite phase).trans (le_max_left _ _)

end GameTheory
