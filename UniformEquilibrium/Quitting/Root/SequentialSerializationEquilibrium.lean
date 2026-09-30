import UniformEquilibrium.Quitting.Root.SequentialSerializationDeviation

/-!
# Behavioral equilibrium transfer under small-hazard serialization

The supplied equilibrium is tested against actual pure-deadline behaviors.
Canonical behavioral pure-time extremality then caps every unrestricted
unilateral behavioral deviation from the serialized profile.
-/

noncomputable section

namespace GameTheory

open _root_.Math.Probability

/-- Known-source serialization transfer, for any bounded four-player table
with unit solo exits. The stronger intermediate constant retains the paper's
literal `384ε` constant when specialized and weakened to its source statement. -/
theorem isAsymptoticNash_quittingSerializedRoots
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    (hunit : QuittingUnitSoloExit reward) (roots : ℕ → Fin 4 → PMF Bool)
    {M hazardBound error : ℝ}
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hsmall : ∀ time owner, (roots time owner true).toReal ≤ hazardBound)
    (hnash : (quittingGame reward).IsεAsymptoticNash (quittingTerminalPayoff reward) error
      (quittingRootSequenceProfile reward roots 0)) :
    (quittingGame reward).IsεAsymptoticNash (quittingTerminalPayoff reward)
      (error + 32 * M * hazardBound)
      (quittingRootSequenceProfile reward (quittingSerializedRoots roots) 0) := by
  have hpure : ∀ (who : Fin 4) (quitTime : Option ℕ),
      quittingRootSequencePureTimeTerminalValue reward (quittingSerializedRoots roots)
        who quitTime 0 ≤
      quittingRootSequenceTerminalValue reward (quittingSerializedRoots roots) who 0 +
        (error + 32 * M * hazardBound) := by
    intro who quitTime
    have hM : 0 ≤ M := (abs_nonneg _).trans
      (hreward (quittingSingletonTerminal who) who)
    have hhazard : 0 ≤ hazardBound := ENNReal.toReal_nonneg.trans (hsmall 0 who)
    have hpayoff := abs_quittingSerializedTerminalValue_sub_original_le
      reward roots who (fun terminal => hreward terminal who) hsmall 0
    simp only [Nat.mul_zero] at hpayoff
    have hpayoffLower := (abs_le.mp hpayoff).1
    cases quitTime with
    | none =>
        have hcompare := abs_quittingSerializedNever_sub_original_le
          reward roots who (fun terminal => hreward terminal who) hsmall
        have hcap := hnash who (quittingPureTimeBehaviorStrategy reward who none)
        rw [quittingTerminalPayoff_update_pureTimeBehaviorStrategy,
          quittingProfileLiveRoot_quittingRootSequenceProfile_zero] at hcap
        change quittingRootSequencePureTimeTerminalValue reward roots who none 0 ≤
          quittingRootSequenceTerminalValue reward roots who 0 + error at hcap
        have hcompareUpper := (abs_le.mp hcompare).2
        have hfactor : 0 ≤ M * hazardBound := mul_nonneg hM hhazard
        linarith
    | some deadline =>
        let stage := deadline / 4
        let phase : Fin 4 := ⟨deadline % 4, Nat.mod_lt _ (by norm_num)⟩
        have hclock : 4 * stage + phase.val = deadline := by
          dsimp [stage, phase]
          omega
        have hcompare := abs_quittingSerializedPureDeadline_sub_original_le
          hunit roots who stage phase hreward hsmall
        rw [hclock] at hcompare
        have hcap := hnash who (quittingPureTimeBehaviorStrategy reward who (some stage))
        rw [quittingTerminalPayoff_update_pureTimeBehaviorStrategy,
          quittingProfileLiveRoot_quittingRootSequenceProfile_zero] at hcap
        change quittingRootSequencePureTimeTerminalValue reward roots who (some stage) 0 ≤
          quittingRootSequenceTerminalValue reward roots who 0 + error at hcap
        have hcompareUpper := (abs_le.mp hcompare).2
        linarith
  intro who deviation
  refine (quittingTerminalPayoff_update_le_sSup_pureTimeBehaviorStrategy reward
    (quittingRootSequenceProfile reward (quittingSerializedRoots roots) 0) who deviation).trans ?_
  apply csSup_le (Set.range_nonempty _)
  rintro _ ⟨quitTime, rfl⟩
  dsimp only
  rw [quittingTerminalPayoff_update_pureTimeBehaviorStrategy,
    quittingProfileLiveRoot_quittingRootSequenceProfile_zero]
  exact hpure who quitTime

end GameTheory
