/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Classification.Existence.ApproximateEquilibriumVanishingNeverAlternative

/-!
# Null-tail elimination for sequentially perfect absorbing sequences

Positive survival after any restart forces each own singleton terminal reward
below the Never payoff plus the row-perfection error. Consequently either all
Continue is an exact terminal Nash profile or, below one fixed positive
threshold, every initially absorbing row-perfect witness terminates after every
restart. The alternatives are inclusive.
-/

namespace GameTheory

open Filter StochasticGame Math.Probability Math.PMFProduct
  QuittingSureSetOwnerRepair

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Positive survival from one restart, together with the upper pure-action
clauses of row perfection against the literal terminal tails, bounds every
own singleton reward by the row error. Initial absorption is not needed. -/
theorem quittingSingletonReward_le_error_of_positiveRestartSurvival
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (ε : ℝ) (start : ℕ)
    (hpositive : 0 < quittingJointSurvivalLimit roots start)
    (hperfect : ∀ time, QuittingRowεPerfect reward
      (quittingRootSequenceTailVector reward roots (time + 1))
      (roots time) ε) (who : ι) :
    reward (quittingSingletonTerminal who) who ≤ ε := by
  let M := quittingRewardBound reward
  have hcharge : Summable (fun time ↦
      quittingRootAbsorptionMass (roots time)) :=
    summable_quittingRootAbsorptionMass_of_jointSurvivalLimit_pos
      roots start hpositive
  have hchargeZero : Tendsto (fun time ↦
      quittingRootAbsorptionMass (roots time)) atTop (nhds 0) :=
    hcharge.tendsto_atTop_zero
  have htime : Tendsto (fun offset ↦ start + offset) atTop atTop := by
    simpa [Nat.add_comm] using tendsto_add_atTop_nat start
  have hopponentZero : Tendsto (fun offset ↦
      quittingRootOpponentAbsorptionMass (roots (start + offset)) who)
      atTop (nhds 0) := by
    apply squeeze_zero
    · exact fun _ ↦ quittingRootOpponentAbsorptionMass_nonneg _ _
    · exact fun offset ↦
        quittingRootOpponentAbsorptionMass_le_absorptionMass
          (roots (start + offset)) who
    · exact hchargeZero.comp htime
  have hlower : Tendsto (fun offset ↦
      reward (quittingSingletonTerminal who) who -
        2 * M * quittingRootOpponentAbsorptionMass
          (roots (start + offset)) who) atTop
      (nhds (reward (quittingSingletonTerminal who) who)) := by
    simpa using tendsto_const_nhds.sub
      (hopponentZero.const_mul (2 * M))
  have hterminal : Tendsto (fun offset ↦
      quittingRootSequenceTerminalValue reward roots who (start + offset))
      atTop (nhds 0) :=
    tendsto_quittingRootSequenceTerminalValue_tail_zero_of_survivalLimit_pos
      reward roots who start (abs_reward_le_quittingRewardBound reward)
      hpositive
  have hupper : Tendsto (fun offset ↦
      quittingRootSequenceTerminalValue reward roots who (start + offset) + ε)
      atTop (nhds ε) := by
    simpa using hterminal.add_const ε
  apply le_of_tendsto_of_tendsto' hlower hupper
  intro offset
  let time := start + offset
  have hquit := (hperfect time who).1
  rw [← quittingRootSequenceTerminalValue_eq_successorPayoff_tailVector]
    at hquit
  have hendpoint :=
    abs_quittingRootQuitPayoff_sub_singletonReward_le_two_mul_opponentAbsorptionMass
      reward (quittingRootSequenceTailVector reward roots (time + 1))
      (roots time) who M (abs_reward_le_quittingRewardBound reward)
  dsimp [time] at hquit hendpoint ⊢
  linarith [abs_le.mp hendpoint |>.1]

namespace QuittingLCPClassification

/-- Arbitrary-never form of the positive-restart null-tail bound. -/
theorem QuittingPayoffTable.solo_sub_never_le_of_positiveRestartSurvival
    (table : QuittingPayoffTable ι) (roots : ℕ → ι → PMF Bool)
    (ε : ℝ) (start : ℕ)
    (hpositive : 0 < quittingJointSurvivalLimit roots start)
    (hperfect : ∀ time, QuittingRowεPerfect table.terminal
      (table.rootSequenceTailVector roots (time + 1)) (roots time) ε)
    (who : ι) :
    table.terminal (quittingSingletonTerminal who) who - table.never who ≤ ε := by
  have hnormalized : ∀ time, QuittingRowεPerfect table.zeroNeverReward
      (quittingRootSequenceTailVector table.zeroNeverReward roots (time + 1))
      (roots time) ε := by
    intro time
    have htranslated : table.terminal = fun S who ↦
        table.zeroNeverReward S who + table.never who := by
      funext S player
      simp [QuittingPayoffTable.zeroNeverReward]
    have htail : table.rootSequenceTailVector roots (time + 1) = fun who ↦
        quittingRootSequenceTailVector table.zeroNeverReward roots
          (time + 1) who + table.never who := by
      funext player
      exact table.rootSequenceTailVector_eq_add_never roots (time + 1) player
    have hrow := hperfect time
    rw [htranslated, htail] at hrow
    exact (quittingRowεPerfect_translate_iff table.zeroNeverReward
      table.never _ (roots time) ε).1 hrow
  exact quittingSingletonReward_le_error_of_positiveRestartSurvival
    table.zeroNeverReward roots ε start hpositive hnormalized who

/-- A root sequence terminates almost surely after every finite restart. -/
def QuittingRootSequenceTerminatesAfterEveryRestart
    (roots : ℕ → ι → PMF Bool) : Prop :=
  ∀ start, quittingJointSurvivalLimit roots start = 0

/-- Literal null-tail lemma in the packet's initially-absorbing shape. The
proof exposes that initial absorption is used only to identify the sequence as
an S.3 witness; the inequality follows from the positive restarted tail. -/
theorem QuittingPayoffTable.solo_sub_never_le_of_completelyAbsorbing_not_everyRestart
    (table : QuittingPayoffTable ι) (roots : ℕ → ι → PMF Bool)
    (ε : ℝ) (_habsorbing : IsCompletelyAbsorbing roots)
    (hperfect : ∀ time, QuittingRowεPerfect table.terminal
      (table.rootSequenceTailVector roots (time + 1)) (roots time) ε)
    (hnotEveryRestart : ¬ QuittingRootSequenceTerminatesAfterEveryRestart roots)
    (who : ι) :
    table.terminal (quittingSingletonTerminal who) who - table.never who ≤ ε := by
  obtain ⟨start, hnonzero⟩ : ∃ start,
      quittingJointSurvivalLimit roots start ≠ 0 := by
    simpa [QuittingRootSequenceTerminatesAfterEveryRestart] using
      hnotEveryRestart
  have hpositive : 0 < quittingJointSurvivalLimit roots start :=
    lt_of_le_of_ne (quittingJointSurvivalLimit_nonneg roots start)
      (Ne.symm hnonzero)
  exact table.solo_sub_never_le_of_positiveRestartSurvival
    roots ε start hpositive hperfect who

/-- The null-tail obstruction is inclusive: either all Continue is an exact
terminal Nash profile, or below one positive threshold every initially
absorbing row-perfect witness terminates after every restart. -/
theorem QuittingPayoffTable.allContinueExactNash_or_everyRestartWitnesses
    (table : QuittingPayoffTable ι) :
    (quittingGame table.terminal).IsεAsymptoticNash table.terminalPayoff 0
        (quittingAlwaysContinueProfile table.terminal) ∨
      ∃ δ : ℝ, 0 < δ ∧ ∀ (ε : ℝ) (roots : ℕ → ι → PMF Bool),
        0 < ε → ε < δ → IsCompletelyAbsorbing roots →
        (∀ time, QuittingRowεPerfect table.terminal
          (table.rootSequenceTailVector roots (time + 1)) (roots time) ε) →
        QuittingRootSequenceTerminatesAfterEveryRestart roots := by
  classical
  by_cases hthreshold : ∃ δ : ℝ, 0 < δ ∧
      ∀ (ε : ℝ) (roots : ℕ → ι → PMF Bool),
        0 < ε → ε < δ → IsCompletelyAbsorbing roots →
        (∀ time, QuittingRowεPerfect table.terminal
          (table.rootSequenceTailVector roots (time + 1)) (roots time) ε) →
        QuittingRootSequenceTerminatesAfterEveryRestart roots
  · exact Or.inr hthreshold
  · left
    have hzero : IsQuittingZeroSolo table.zeroNeverReward := by
      intro who
      by_contra hnot
      let gap := table.zeroNeverReward
        (quittingSingletonTerminal who) who
      have hpositive : 0 < gap := lt_of_not_ge hnot
      have hfailure : ¬ ∀ (ε : ℝ) (roots : ℕ → ι → PMF Bool),
          0 < ε → ε < gap → IsCompletelyAbsorbing roots →
          (∀ time, QuittingRowεPerfect table.terminal
            (table.rootSequenceTailVector roots (time + 1))
            (roots time) ε) →
          QuittingRootSequenceTerminatesAfterEveryRestart roots := by
        intro hall
        exact hthreshold ⟨gap, hpositive, hall⟩
      simp only [not_forall] at hfailure
      obtain ⟨ε, roots, hε, hεlt, habsorbing, hperfect, hnotEvery⟩ :=
        hfailure
      have hbound :=
        table.solo_sub_never_le_of_completelyAbsorbing_not_everyRestart
          roots ε habsorbing hperfect hnotEvery who
      change gap ≤ ε at hbound
      linarith
    have hnashZero :=
      isZeroAsymptoticNash_quittingAlwaysContinue_of_zeroSolo
        table.zeroNeverReward hzero
    exact (table.isεAsymptoticNash_iff 0
      (quittingAlwaysContinueProfile table.terminal)).2 hnashZero

end QuittingLCPClassification
end GameTheory
