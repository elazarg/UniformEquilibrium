import UniformEquilibrium.Quitting.Terminal.FiniteDeadlineHorizonError
import UniformEquilibrium.Quitting.Paths.StageCoalitionMass
import UniformEquilibrium.Quitting.Punishment.NegativeSoloUniformization
import UniformEquilibrium.Quitting.Root.OneDateNeverNashDebt
import UniformEquilibrium.Quitting.RewardBound

/-! # The same one-date terminal equilibrium at every finite horizon

For signed rewards, an arbitrary stage deviation is compared with its actual
cutoff-and-Continue terminal deviation. After date zero all opponents are quiet,
so the canonical opponent-tail error vanishes. Exact terminal Nash therefore
gives exact finite-horizon Nash, including horizon zero. The literal same profile
also delivers its fixed terminal payoff to every requested accuracy.
-/

noncomputable section

namespace GameTheory

open StochasticGame
open scoped BigOperators

variable {ι : Type} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
theorem expectedStagePayoff_eq_terminal_of_quietAfter_one
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (hquiet : ∀ later, 1 ≤ later →
      quittingProfileLiveRoot reward profile later = quittingAllContinueRoot)
    {time : ℕ} (htime : 1 ≤ time) (who : ι) :
    (quittingGame reward).expectedStagePayoff profile none time who =
      quittingTerminalPayoff reward profile who := by
  have htail := abs_quittingTerminalPayoff_sub_expectedStagePayoff_le_liveTail
    reward profile time who (quittingRewardBound reward)
    (fun terminal => abs_reward_le_quittingRewardBound reward terminal who)
  rw [quittingLiveMass_eq_limit_of_quietAfterDeadline reward 1 profile hquiet htime,
    sub_self, mul_zero] at htail
  exact (sub_eq_zero.mp (abs_eq_zero.mp (le_antisymm htail (abs_nonneg _)))).symm

/-- No finite-support or singleton-sign hypothesis is used on a deviation. -/
theorem isHorizonNash_exact_of_terminalNash_quietAfter_one
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (hquiet : ∀ later, 1 ≤ later →
      quittingProfileLiveRoot reward profile later = quittingAllContinueRoot)
    (hnash : (quittingGame reward).IsεAsymptoticNash (quittingTerminalPayoff reward)
      0 profile) (horizon : ℕ) :
    (quittingGame reward).IsεHorizonNash none horizon 0 profile := by
  classical
  let : Finite (quittingGame reward).State :=
    inferInstanceAs (Finite (Option {S : Finset ι // S.Nonempty}))
  let : ∀ player : ι, Finite ((quittingGame reward).Act player) :=
    fun _ => inferInstanceAs (Finite Bool)
  intro who deviation
  simp only [add_zero]
  let initial : (quittingGame reward).State := none
  change (quittingGame reward).finiteAveragePayoff initial horizon
      (Function.update profile who deviation) who ≤
    (quittingGame reward).finiteAveragePayoff initial horizon profile who
  rw [(quittingGame reward).finiteAveragePayoff_eq_sum_expectedStagePayoff
      (Function.update profile who deviation) initial who horizon,
    (quittingGame reward).finiteAveragePayoff_eq_sum_expectedStagePayoff
      profile initial who horizon]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Finset.sum_le_sum
  intro time _
  by_cases htime : time = 0
  · subst time
    rw [expectedStagePayoff_quittingGame_eq_sum_mass,
      expectedStagePayoff_quittingGame_eq_sum_mass]
    simp only [quittingAbsorbedMass_zero, zero_mul, Finset.sum_const_zero, le_refl]
  · have hpositive : 1 ≤ time := by omega
    have hopponents := quittingOpponentOnlyProfile_quietAfterDeadline
      reward 1 profile hquiet who
    have htail := quittingLiveMass_eq_limit_of_quietAfterDeadline
      reward 1 (quittingOpponentOnlyProfile reward profile who) hopponents hpositive
    have hstage := expectedStagePayoff_update_le_cutoffTerminal_add_opponentLiveTail
      reward profile who deviation time (quittingRewardBound reward)
      (quittingRewardBound_nonneg reward)
      (fun terminal => abs_reward_le_quittingRewardBound reward terminal who)
    rw [htail, sub_self, mul_zero, add_zero] at hstage
    have hterminal := hnash who (quittingContinueAfterStrategy reward who deviation time)
    rw [add_zero] at hterminal
    rw [expectedStagePayoff_eq_terminal_of_quietAfter_one
      reward profile hquiet hpositive who]
    exact hstage.trans hterminal

omit [DecidableEq ι] in
theorem quittingOneDateThenNeverProfile_quietAfter_one
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (root : ι → PMF Bool) :
    ∀ later, 1 ≤ later →
      quittingProfileLiveRoot reward (quittingOneDateThenNeverProfile reward root) later =
        quittingAllContinueRoot := by
  intro later hlater
  obtain ⟨date, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : later ≠ 0)
  rfl

theorem quittingOneDateThenNeverProfile_exactHorizonNash
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (root : ι → PMF Bool)
    (hnash : (quittingGame reward).IsεAsymptoticNash (quittingTerminalPayoff reward) 0
      (quittingOneDateThenNeverProfile reward root)) (horizon : ℕ) :
    (quittingGame reward).IsεHorizonNash none horizon 0
      (quittingOneDateThenNeverProfile reward root) :=
  isHorizonNash_exact_of_terminalNash_quietAfter_one reward _
    (quittingOneDateThenNeverProfile_quietAfter_one reward root) hnash horizon

/-- Accuracy changes only the horizon threshold, not the displayed profile or target. -/
theorem quittingOneDateThenNeverProfile_sameProfile_uniformPayoffWitness
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (root : ι → PMF Bool)
    (hnash : (quittingGame reward).IsεAsymptoticNash (quittingTerminalPayoff reward) 0
      (quittingOneDateThenNeverProfile reward root)) :
    ∀ accuracy : ℝ, 0 < accuracy → ∃ threshold : ℕ,
      ∀ horizon : ℕ, threshold ≤ horizon →
        (quittingGame reward).IsεHorizonNash none horizon accuracy
          (quittingOneDateThenNeverProfile reward root) ∧
        ∀ who, |(quittingGame reward).finiteAveragePayoff none horizon
            (quittingOneDateThenNeverProfile reward root) who -
          quittingTerminalPayoff reward (quittingOneDateThenNeverProfile reward root) who| ≤
            accuracy := by
  intro accuracy haccuracy
  let bound := quittingRewardBound reward
  refine ⟨max 1 (Nat.ceil (bound / accuracy)), ?_⟩
  intro horizon hhorizon
  have hpositive : 0 < horizon := lt_of_lt_of_le Nat.zero_lt_one
    ((Nat.le_max_left _ _).trans hhorizon)
  have hreal : (0 : ℝ) < horizon := by exact_mod_cast hpositive
  have hceil : Nat.ceil (bound / accuracy) ≤ horizon :=
    (Nat.le_max_right _ _).trans hhorizon
  have hcast : (Nat.ceil (bound / accuracy) : ℝ) ≤ horizon := by exact_mod_cast hceil
  have hquotient := (Nat.le_ceil (bound / accuracy)).trans hcast
  have hmul := (div_le_iff₀ haccuracy).mp hquotient
  have hboundary : bound / horizon ≤ accuracy := by
    apply (div_le_iff₀ hreal).mpr
    linarith
  refine ⟨(quittingOneDateThenNeverProfile_exactHorizonNash reward root hnash horizon).mono
    haccuracy.le, ?_⟩
  intro who
  have hpayoff := abs_finiteAveragePayoff_sub_terminal_quietAfterDeadline_le
    reward 1 horizon (quittingOneDateThenNeverProfile reward root)
    (quittingOneDateThenNeverProfile_quietAfter_one reward root) who
    (fun terminal => abs_reward_le_quittingRewardBound reward terminal who) hpositive
  have hbound : |(quittingGame reward).finiteAveragePayoff none horizon
        (quittingOneDateThenNeverProfile reward root) who -
      quittingTerminalPayoff reward (quittingOneDateThenNeverProfile reward root) who| ≤
        bound / horizon := by
    simpa only [bound, Nat.cast_one, mul_one] using hpayoff
  exact hbound.trans hboundary

end GameTheory
