import UniformEquilibrium.Quitting.Cycles.CyclicFiniteWord
import UniformEquilibrium.Quitting.Root.FiniteRootWordSequenceBridge

/-! # Censoring an approximate periodic profile

The concrete finite profile retains a whole number of turns and then Continues
forever. Its prescribed payoff has an exact renewal factor. Its full behavioral
cap changes by at most twice the signed reward bound times opponent survival.
The input cap bound is a bound on the actual infinite periodic profile; no local
root Nash, singleton sign, or restriction on the deviator's stopping dates is used.
-/

noncomputable section

namespace GameTheory

variable {ι : Type} [Fintype ι] [DecidableEq ι] {period : ℕ}

omit [Fintype ι] [DecidableEq ι] in
/-- The recursive chronological word is the literal prefix of the periodic sequence. -/
theorem quittingCyclicRootWord_eq_ofFn
    (roots : Fin period → ι → PMF Bool) (phase : Fin period) (fuel : ℕ) :
    quittingCyclicRootWord roots phase fuel =
      List.ofFn (fun time : Fin fuel => quittingCyclicRootSequence roots phase time.val) := by
  induction fuel generalizing phase with
  | zero => simp [quittingCyclicRootWord]
  | succ fuel ih =>
      rw [quittingCyclicRootWord, List.ofFn_succ, ih]
      simp only [Fin.val_zero, quittingCyclicRootSequence_zero, Fin.val_succ,
        quittingCyclicRootSequence_succ]

/-- Deleted-player survival through a cyclic word is its cyclic prefix product. -/
theorem quittingCyclicRootWord_opponentSurvival
    (roots : Fin period → ι → PMF Bool) (phase : Fin period) (fuel : ℕ) (who : ι) :
    quittingLiteralRootStackOpponentSurvival (quittingCyclicRootWord roots phase fuel) who =
      quittingCyclicPrefixWeight
        (fun phase => quittingStationaryFixedOpponentsContinueMass (roots phase) who)
        phase fuel := by
  rw [quittingCyclicRootWord_eq_ofFn]
  have h := quittingLiteralRootStackOpponentSurvival_ofFn
    (quittingCyclicRootSequence roots phase) who 0 fuel
  simp only [zero_add] at h
  rw [h, quittingOpponentSurvivalWeight_cyclicRootSequence]
  simp only [quittingCyclicOrbit_zero]

omit [DecidableEq ι] in
/-- Cutting a literal prefix from the actual periodic profile leaves its actual shifted tail. -/
theorem quittingCyclicBehaviorProfile_eq_literalRootStack
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : Fin period → ι → PMF Bool) (phase : Fin period) (fuel : ℕ) :
    quittingCyclicBehaviorProfile reward roots phase =
      quittingLiteralRootStackProfile reward (quittingCyclicRootWord roots phase fuel)
        (quittingCyclicBehaviorProfile reward roots (quittingCyclicOrbit phase fuel)) := by
  rw [quittingCyclicRootWord_eq_ofFn]
  have h := quittingRootSequenceProfile_eq_literalRootStack reward
    (quittingCyclicRootSequence roots phase) 0 fuel
  simp only [zero_add] at h
  rw [quittingCyclicBehaviorProfile, h]
  congr 1
  funext player time history
  simp only [quittingRootSequenceProfile, quittingCyclicBehaviorProfile,
    quittingCyclicRootSequence_add, zero_add]
  rfl

/-- Arbitrary signed suffix caps are bounded by `M`, so censoring costs at most
`2 * M` times the deleted-player survival of the retained prefix. -/
theorem abs_quittingContinuationBestResponseValue_cyclicFiniteProfile_sub_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : Fin period → ι → PMF Bool) (phase : Fin period) (fuel : ℕ) (who : ι)
    {M : ℝ} (hreward : ∀ terminal player, |reward terminal player| ≤ M) :
    |quittingContinuationBestResponseValue reward
          (quittingCyclicFiniteProfile reward roots phase fuel) who -
        quittingContinuationBestResponseValue reward
          (quittingCyclicBehaviorProfile reward roots phase) who| ≤
      2 * M * quittingCyclicPrefixWeight
        (fun phase => quittingStationaryFixedOpponentsContinueMass (roots phase) who)
        phase fuel := by
  have h := abs_quittingContinuationBestResponseValue_literalRootStack_sub_le reward
    (quittingCyclicRootWord roots phase fuel)
    (quittingAlwaysContinueProfile reward)
    (quittingCyclicBehaviorProfile reward roots (quittingCyclicOrbit phase fuel)) who
  have htail :
      |quittingContinuationBestResponseValue reward (quittingAlwaysContinueProfile reward) who -
          quittingContinuationBestResponseValue reward
            (quittingCyclicBehaviorProfile reward roots (quittingCyclicOrbit phase fuel)) who| ≤
        2 * M := by
    calc
      _ ≤ |quittingContinuationBestResponseValue reward
          (quittingAlwaysContinueProfile reward) who| +
          |quittingContinuationBestResponseValue reward
            (quittingCyclicBehaviorProfile reward roots (quittingCyclicOrbit phase fuel)) who| :=
        abs_sub _ _
      _ ≤ M + M := add_le_add
        (abs_quittingContinuationBestResponseValue_le reward _ who hreward)
        (abs_quittingContinuationBestResponseValue_le reward _ who hreward)
      _ = 2 * M := by ring
  have hscaled := mul_le_mul_of_nonneg_left htail
    (quittingLiteralRootStackOpponentSurvival_nonneg
      (quittingCyclicRootWord roots phase fuel) who)
  rw [← quittingCyclicBehaviorProfile_eq_literalRootStack] at h
  change |quittingContinuationBestResponseValue reward
      (quittingCyclicFiniteProfile reward roots phase fuel) who -
    quittingContinuationBestResponseValue reward
      (quittingCyclicBehaviorProfile reward roots phase) who| ≤ _ at h
  exact (h.trans hscaled).trans_eq (by rw [quittingCyclicRootWord_opponentSurvival]; ring)

/-- A whole-turn censor transports any supplied full behavioral cap bound on the
actual periodic profile, including Never and every after-support deadline. -/
theorem quittingContinuationBestResponseValue_cyclicFiniteProfile_le_of_full_cap
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : Fin period → ι → PMF Bool) (phase : Fin period) (turns : ℕ) (who : ι)
    {M error : ℝ} (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hcap : quittingContinuationBestResponseValue reward
      (quittingCyclicBehaviorProfile reward roots phase) who ≤
        quittingCyclicTerminalValue reward roots phase who + error) :
    quittingContinuationBestResponseValue reward
        (quittingCyclicFiniteProfile reward roots phase (turns * period)) who ≤
      quittingCyclicTerminalValue reward roots phase who + error +
        2 * M * (∏ phase, quittingStationaryFixedOpponentsContinueMass (roots phase) who) ^
          turns := by
  have h := abs_quittingContinuationBestResponseValue_cyclicFiniteProfile_sub_le
    reward roots phase (turns * period) who hreward
  rw [quittingCyclicPrefixWeight_mul_card] at h
  have hdiff := le_of_abs_le h
  linarith

omit [DecidableEq ι] in
/-- Exact renewal gives a delivery error bounded by joint survival, for signed rewards. -/
theorem abs_quittingTerminalPayoff_cyclicFiniteProfile_sub_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : Fin period → ι → PMF Bool) (phase : Fin period) (turns : ℕ) (who : ι)
    {M : ℝ} (hreward : ∀ terminal player, |reward terminal player| ≤ M) :
    |quittingTerminalPayoff reward
          (quittingCyclicFiniteProfile reward roots phase (turns * period)) who -
        quittingCyclicTerminalValue reward roots phase who| ≤
      M * (∏ phase, quittingStationaryContinueMass (roots phase)) ^ turns := by
  have hvalue : |quittingCyclicTerminalValue reward roots phase who| ≤ M :=
    abs_quittingTerminalPayoff_le reward
      (quittingCyclicBehaviorProfile reward roots phase) who hreward
  have hmass : 0 ≤ (∏ phase, quittingStationaryContinueMass (roots phase)) ^ turns :=
    pow_nonneg (Finset.prod_nonneg fun phase _ =>
      quittingStationaryContinueMass_nonneg (roots phase)) turns
  rw [quittingTerminalPayoff_cyclicFiniteProfile_mul_card]
  calc
    _ = (∏ phase, quittingStationaryContinueMass (roots phase)) ^ turns *
        |quittingCyclicTerminalValue reward roots phase who| := by
      rw [show (1 - (∏ phase, quittingStationaryContinueMass (roots phase)) ^ turns) *
          quittingCyclicTerminalValue reward roots phase who -
          quittingCyclicTerminalValue reward roots phase who =
        -((∏ phase, quittingStationaryContinueMass (roots phase)) ^ turns *
          quittingCyclicTerminalValue reward roots phase who) by ring,
        abs_neg, abs_mul, abs_of_nonneg hmass]
    _ ≤ (∏ phase, quittingStationaryContinueMass (roots phase)) ^ turns * M :=
      mul_le_mul_of_nonneg_left hvalue hmass
    _ = _ := by ring

/-- Terminal regret combines the opponent-survival censor cost and the joint-survival
delivery cost. The rewards and own singleton may have either sign. -/
theorem quittingTerminalDeviationDebt_cyclicFiniteProfile_le_of_full_cap
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : Fin period → ι → PMF Bool) (phase : Fin period) (turns : ℕ) (who : ι)
    {M error : ℝ} (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hcap : quittingContinuationBestResponseValue reward
      (quittingCyclicBehaviorProfile reward roots phase) who ≤
        quittingCyclicTerminalValue reward roots phase who + error) :
    quittingTerminalDeviationDebt reward
        (quittingCyclicFiniteProfile reward roots phase (turns * period)) who ≤
      error + 2 * M *
        (∏ phase, quittingStationaryFixedOpponentsContinueMass (roots phase) who) ^ turns +
        M * (∏ phase, quittingStationaryContinueMass (roots phase)) ^ turns := by
  have hbest := quittingContinuationBestResponseValue_cyclicFiniteProfile_le_of_full_cap
    reward roots phase turns who hreward hcap
  have hdelivery := neg_le_of_abs_le
    (abs_quittingTerminalPayoff_cyclicFiniteProfile_sub_le
      reward roots phase turns who hreward)
  unfold quittingTerminalDeviationDebt
  linarith

omit [DecidableEq ι] in
/-- A player with literal Continue roots still Continues at every history after censoring. -/
theorem quittingCyclicFiniteProfile_apply_eq_continue_of_roots
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : Fin period → ι → PMF Bool) (phase : Fin period) (fuel : ℕ) (who : ι)
    (hcontinue : ∀ phase, roots phase who = PMF.pure false)
    (time : ℕ) (history : (quittingGame reward).Hist time) :
    quittingCyclicFiniteProfile reward roots phase fuel who time history = PMF.pure false := by
  rw [quittingCyclicFiniteProfile_apply]
  split
  · exact hcontinue _
  · rfl

end GameTheory
