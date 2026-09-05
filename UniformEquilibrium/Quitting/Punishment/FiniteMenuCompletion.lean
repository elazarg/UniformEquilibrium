import UniformEquilibrium.Quitting.Punishment.FiniteMenuPunishmentRecursion
import UniformEquilibrium.Quitting.Punishment.InstantPunishment
import UniformEquilibrium.Quitting.Root.FiniteRootWordSequenceBridge
import UniformEquilibrium.Quitting.Terminal.TargetTail.DiagonalTargetTailSelection

/-! # Same-prefix completion of actual finite timing-menu equilibria -/

noncomputable section

namespace GameTheory

variable {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]

/-- Retain the source's literal prefix, then install one fixed stationary
opponent punishment row while the target itself plays Never. -/
def quittingFiniteMenuPunishmentCompletionProfile
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) {deadline : ℕ}
    (mixed : ι → PMF (QuittingFiniteDeadlineTimingAction deadline))
    (horizon : ℕ) (target : ι) (punishmentRoot : ι → PMF Bool) :
    (quittingGame reward).BehaviorProfile :=
  quittingLiteralRootStackProfile reward
    (List.ofFn fun time : Fin (deadline - horizon) ↦
      quittingProfileLiveRoot reward
        (quittingFiniteDeadlineTimingProfile reward deadline mixed) time.val)
    (Function.update (quittingStationaryProfile reward punishmentRoot) target
      (quittingAlwaysContinueStrategy reward target))

omit [Nonempty ι] in
theorem quittingFiniteMenuPunishmentCompletionProfile_eq_source_of_lt
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) {deadline : ℕ}
    (mixed : ι → PMF (QuittingFiniteDeadlineTimingAction deadline))
    (horizon : ℕ) (target : ι) (punishmentRoot : ι → PMF Bool)
    {time : ℕ} (htime : time < deadline - horizon)
    (who : ι) (history : (quittingGame reward).Hist time) :
    quittingFiniteMenuPunishmentCompletionProfile reward mixed horizon target punishmentRoot
        who time history =
      quittingFiniteDeadlineTimingProfile reward deadline mixed who time history := by
  have h := quittingLiteralRootStackProfile_ofFn_apply_of_lt reward
    (quittingProfileLiveRoot reward (quittingFiniteDeadlineTimingProfile reward deadline mixed))
    0 (deadline - horizon)
    (Function.update (quittingStationaryProfile reward punishmentRoot) target
      (quittingAlwaysContinueStrategy reward target)) who time history htime
  simpa only [Nat.zero_add, quittingFiniteMenuPunishmentCompletionProfile,
    quittingProfileLiveRoot, quittingFiniteDeadlineTimingProfile,
    quittingCompactStoppingLawProfile, quittingStoppingLawBehaviorStrategy] using h

/-- One fixed target and one independent stationary punishment row complete
the source with the quantitative joint/deleted-clock bound. The conclusion
caps every complete behavioral replacement and retains every prefix history. -/
theorem exists_finiteMenu_samePrefix_completion
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) {bound : ℝ}
    (hreward : ∀ terminal player, |reward terminal player| ≤ bound)
    (deadline horizon : ℕ) (hhorizon : horizon ≤ deadline)
    (mixed : ι → PMF (QuittingFiniteDeadlineTimingAction deadline))
    {error reach slack : ℝ}
    (hnash : IsQuittingFiniteDeadlineNash reward deadline error mixed)
    (hreach : 0 < reach) (hslack : 0 < slack)
    (hearly : quittingJointSurvivalWeight
      (quittingProfileLiveRoot reward
        (quittingFiniteDeadlineTimingProfile reward deadline mixed))
      0 (deadline - horizon) < reach) :
    ∃ target : ι, ∃ punishmentRoot : ι → PMF Bool,
      quittingStationaryUnilateralCap reward punishmentRoot target <
        quittingPunishmentValue reward target + slack ∧
      (∀ time < deadline - horizon, ∀ who (history : (quittingGame reward).Hist time),
        quittingFiniteMenuPunishmentCompletionProfile reward mixed horizon target punishmentRoot
            who time history =
          quittingFiniteDeadlineTimingProfile reward deadline mixed who time history) ∧
      quittingTerminalExploitability reward
        (quittingFiniteMenuPunishmentCompletionProfile reward mixed horizon target punishmentRoot) ≤
        error + 2 * bound * reach +
          max (2 * bound * Real.sqrt reach)
            (quittingFiniteMenuPunishmentDeficit reward horizon + slack) := by
  let source := quittingFiniteDeadlineTimingProfile reward deadline mixed
  let roots := quittingProfileLiveRoot reward source
  let cutoff := deadline - horizon
  let headWord := List.ofFn fun time : Fin cutoff ↦ roots time.val
  let suffix := List.ofFn fun time : Fin horizon ↦ roots (cutoff + time.val)
  have hsplit : cutoff + horizon = deadline := Nat.sub_add_cancel hhorizon
  have hword : (List.ofFn fun time : Fin deadline ↦ roots time.val) = headWord ++ suffix := by
    have h := List.ofFn_add (f := fun time : Fin (cutoff + horizon) ↦ roots time.val)
    simpa only [hsplit, Fin.val_castLE, Fin.val_natAdd, Fin.val_cast] using h
  obtain ⟨target, htarget⟩ :=
    exists_target_forall_opponentSurvivalWeight_le_of_joint_le_sq roots cutoff
      (Real.sqrt_nonneg reach) (by simpa only [Real.sq_sqrt hreach.le] using hearly.le)
  obtain ⟨punishmentRoot, hpunishment⟩ :=
    exists_quittingStationaryPunishmentRoot_lt_add reward target hslack
  let tail := Function.update (quittingStationaryProfile reward punishmentRoot) target
    (quittingAlwaysContinueStrategy reward target)
  let oldTail := quittingRootSequenceProfile reward roots cutoff
  let completed := quittingLiteralRootStackProfile reward headWord tail
  have hbound : 0 ≤ bound :=
    (abs_nonneg (reward ⟨{target}, Finset.singleton_nonempty target⟩ target)).trans
      (hreward _ target)
  have hsource : source = quittingLiteralRootStackProfile reward headWord oldTail := by
    have hcanonical : source = quittingRootSequenceProfile reward roots 0 := by
      funext who time history
      simp only [quittingRootSequenceProfile, Nat.zero_add, roots, source,
        quittingProfileLiveRoot, quittingFiniteDeadlineTimingProfile,
        quittingCompactStoppingLawProfile, quittingStoppingLawBehaviorStrategy]
    rw [hcanonical]
    simpa only [Nat.zero_add] using
      quittingRootSequenceProfile_eq_literalRootStack reward roots 0 cutoff
  have hmenu (who : ι) : quittingFiniteDeadlineReplyCap reward deadline mixed who =
      quittingFiniteRootWordCap reward headWord who
        (quittingFiniteRootWordCap reward suffix who 0) := by
    rw [quittingFiniteDeadlineReplyCap_eq_finiteRootWordCap, hword,
      quittingFiniteRootWordCap_append]
  have hsuffix (who : ι) : quittingFiniteMenuPunishmentValue reward horizon who ≤
      quittingFiniteRootWordCap reward suffix who 0 := by
    obtain ⟨_, _, _, hminimum⟩ :=
      exists_quittingFiniteRootWordCap_minimizer reward who horizon
    rw [quittingFiniteMenuPunishmentValue_eq_operator_iterate]
    exact hminimum suffix List.length_ofFn
  have htail : quittingContinuationBestResponseValue reward tail target <
      quittingPunishmentValue reward target + slack := by
    change quittingContinuationBestResponseValue reward
      (Function.update (quittingStationaryProfile reward punishmentRoot) target
        (quittingAlwaysContinueStrategy reward target)) target < _
    rw [quittingContinuationBestResponseValue_update_self]
    change quittingBestReplyValue reward
      (quittingStationaryProfile reward punishmentRoot) target < _
    rwa [quittingBestReplyValue_stationary]
  have hpayoff (who : ι) :
      |quittingTerminalPayoff reward completed who -
        quittingTerminalPayoff reward source who| ≤ 2 * bound * reach := by
    rw [hsource]
    simp only [completed, quittingTerminalPayoff_literalRootStack_eq_wordPayoff]
    rw [quittingFiniteRootWordPayoff_sub_eq_jointSurvival_mul, abs_mul,
      abs_of_nonneg (quittingLiteralRootStackJointSurvival_nonneg headWord)]
    have hdiff : |quittingTerminalPayoff reward tail who -
        quittingTerminalPayoff reward oldTail who| ≤ 2 * bound := by
      exact (abs_sub _ _).trans (by
        have hfirst := abs_quittingTerminalPayoff_le reward tail who hreward
        have hsecond := abs_quittingTerminalPayoff_le reward oldTail who hreward
        linarith)
    have hproduct := mul_le_mul_of_nonneg_left hdiff
      (quittingLiteralRootStackJointSurvival_nonneg headWord)
    apply hproduct.trans
    have hjoint : quittingLiteralRootStackJointSurvival headWord < reach := by
      have heq := quittingLiteralRootStackJointSurvival_ofFn roots 0 cutoff
      simp only [Nat.zero_add] at heq
      exact heq.trans_lt hearly
    nlinarith
  refine ⟨target, punishmentRoot, hpunishment, ?_, ?_⟩
  · intro time htime who history
    exact quittingFiniteMenuPunishmentCompletionProfile_eq_source_of_lt
      reward mixed horizon target punishmentRoot htime who history
  · change quittingTerminalExploitability reward completed ≤ _
    rw [quittingTerminalExploitability_eq_max_debt]
    apply QuittingBoundaryHolonomy.finitePlayerMax_le
    intro who
    have hcap := quittingFiniteRootWordCap_sub_le_opponentSurvival_mul_posPart reward headWord who
      (quittingContinuationBestResponseValue reward tail who)
      (quittingFiniteRootWordCap reward suffix who 0)
    rw [← quittingContinuationBestResponseValue_literalRootStack_eq_capFold,
      ← hmenu who] at hcap
    have hseam : quittingLiteralRootStackOpponentSurvival headWord who *
        max 0 (quittingContinuationBestResponseValue reward tail who -
          quittingFiniteRootWordCap reward suffix who 0) ≤
        max (2 * bound * Real.sqrt reach)
          (quittingFiniteMenuPunishmentDeficit reward horizon + slack) := by
      by_cases hwho : who = target
      · subst who
        have hgap : max 0 (quittingContinuationBestResponseValue reward tail target -
            quittingFiniteRootWordCap reward suffix target 0) ≤
              quittingFiniteMenuPunishmentDeficit reward horizon + slack := by
          apply max_le
          · linarith [quittingFiniteMenuPunishmentDeficit_nonneg reward horizon]
          · have hmin := hsuffix target
            have hdeficit := quittingPunishmentValue_sub_menu_le_deficit reward horizon target
            linarith
        have hweight := quittingLiteralRootStackOpponentSurvival_le_one headWord target
        have hsmall := mul_le_mul_of_nonneg_right hweight
          (le_max_left 0 (quittingContinuationBestResponseValue reward tail target -
            quittingFiniteRootWordCap reward suffix target 0))
        simp only [one_mul] at hsmall
        exact (hsmall.trans hgap).trans (le_max_right _ _)
      · have hgap : max 0 (quittingContinuationBestResponseValue reward tail who -
            quittingFiniteRootWordCap reward suffix who 0) ≤ 2 * bound := by
          apply max_le (by linarith)
          have hnew := le_of_abs_le
            (abs_quittingContinuationBestResponseValue_le reward tail who hreward)
          have hold := neg_le_of_abs_le
            (abs_quittingFiniteRootWordCap_zero_le reward suffix who hreward)
          linarith
        have hweight : quittingLiteralRootStackOpponentSurvival headWord who ≤ Real.sqrt reach := by
          have heq := quittingLiteralRootStackOpponentSurvival_ofFn roots who 0 cutoff
          simp only [Nat.zero_add] at heq
          exact heq.trans_le (htarget who hwho)
        have hscaled := mul_le_mul hweight hgap (le_max_left _ _)
          (Real.sqrt_nonneg reach)
        exact (hscaled.trans_eq (mul_comm _ _)).trans (le_max_left _ _)
    have hn := hnash who
    have hp := (abs_le.mp (hpayoff who)).1
    change quittingTerminalDeviationDebt reward completed who ≤ _
    unfold quittingTerminalDeviationDebt
    change quittingContinuationBestResponseValue reward completed who -
      quittingFiniteDeadlineReplyCap reward deadline mixed who ≤ _ at hcap
    change quittingFiniteDeadlineReplyCap reward deadline mixed who ≤
      quittingTerminalPayoff reward source who + error at hn
    linarith

end GameTheory
