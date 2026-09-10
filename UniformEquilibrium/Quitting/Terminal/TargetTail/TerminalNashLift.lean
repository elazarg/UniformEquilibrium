import UniformEquilibrium.Quitting.Terminal.TargetTail.TerminalUniformPayoffSelection

/-! # Fixed-target payoff transport through terminal-Nash lift families -/

noncomputable section

namespace GameTheory

open Filter StochasticGame

variable {ι κ : Type} [Fintype ι] [DecidableEq ι]
  [Fintype κ] [DecidableEq κ]

/-- A fixed-multiplier lift of terminal approximate equilibria transports every
specified child uniform-equilibrium payoff while preserving its displayed coordinates. -/
theorem exists_uniformEquilibriumPayoff_eq_on_image_of_terminalNash_lift
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (childReward : {S : Finset κ // S.Nonempty} → Payoff κ)
    (playerMap : κ → ι)
    (lift : (quittingGame childReward).BehaviorProfile →
      (quittingGame reward).BehaviorProfile)
    (factor : ℝ)
    (hpayoff : ∀ profile who,
      quittingTerminalPayoff reward (lift profile) (playerMap who) =
        quittingTerminalPayoff childReward profile who)
    (hnash : ∀ {error : ℝ}, 0 ≤ error →
      ∀ profile : (quittingGame childReward).BehaviorProfile,
        (quittingGame childReward).IsεAsymptoticNash
            (quittingTerminalPayoff childReward) error profile →
          (quittingGame reward).IsεAsymptoticNash
            (quittingTerminalPayoff reward) (factor * error) (lift profile))
    (target : Payoff κ)
    (htarget : (quittingGame childReward).IsUniformEquilibriumPayoff none target) :
    ∃ payoff : Payoff ι,
      (∀ who, payoff (playerMap who) = target who) ∧
        (quittingGame reward).IsUniformEquilibriumPayoff none payoff := by
  classical
  let error : ℕ → ℝ := fun step => 1 / ((step : ℝ) + 1)
  have herrorPos : ∀ step, 0 < error step := by
    intro step
    dsimp [error]
    positivity
  have hexists : ∀ step, ∃ profile : (quittingGame childReward).BehaviorProfile,
      (quittingGame childReward).IsεAsymptoticNash
          (quittingTerminalPayoff childReward) (error step) profile ∧
        ∀ who, |quittingTerminalPayoff childReward profile who - target who| ≤
          error step :=
    fun step => exists_terminalNash_terminalPayoff_close_of_isUniformEquilibriumPayoff
      childReward target htarget (herrorPos step)
  choose profiles hchildNash hclose using hexists
  have hmem : ∀ step, quittingTerminalPayoff reward (lift (profiles step)) ∈
      Set.Icc (fun _ : ι => -quittingRewardBound reward)
        (fun _ : ι => quittingRewardBound reward) :=
    fun step => quittingTerminalPayoff_mem_rewardCube reward (lift (profiles step))
  obtain ⟨payoff, -, subsequence, hsubsequence, hlimit⟩ :=
    (isCompact_Icc : IsCompact
      (Set.Icc (fun _ : ι => -quittingRewardBound reward)
        (fun _ : ι => quittingRewardBound reward))).tendsto_subseq hmem
  have herrorLimit : Tendsto error atTop (nhds 0) := by
    simpa [error] using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hsubError : Tendsto (error ∘ subsequence) atTop (nhds 0) :=
    herrorLimit.comp hsubsequence.tendsto_atTop
  have hparentError : Tendsto (fun step => factor * (error ∘ subsequence) step)
      atTop (nhds 0) := by
    simpa only [mul_zero] using tendsto_const_nhds.mul hsubError
  refine ⟨payoff, fun who => ?_, ?_⟩
  · have hcoord : Tendsto
        (fun step => quittingTerminalPayoff reward
          (lift (profiles (subsequence step))) (playerMap who))
        atTop (nhds (payoff (playerMap who))) :=
      (tendsto_pi_nhds.mp hlimit) (playerMap who)
    have hbound : ∀ step,
        |quittingTerminalPayoff reward (lift (profiles (subsequence step)))
            (playerMap who) - target who| ≤ (error ∘ subsequence) step := by
      intro step
      rw [hpayoff]
      exact hclose (subsequence step) who
    have hzero : |payoff (playerMap who) - target who| ≤ 0 := by
      refine le_of_tendsto_of_tendsto' ((hcoord.sub tendsto_const_nhds).abs)
        hsubError hbound
    exact sub_eq_zero.mp (abs_nonpos_iff.mp hzero)
  · refine quittingGame_isUniformEquilibriumPayoff_of_terminalNash_tendsto
      (filter := atTop) reward payoff
      (fun step => factor * (error ∘ subsequence) step)
      (fun step => lift (profiles (subsequence step))) hparentError ?_ hlimit
    refine Frequently.of_forall fun step => ?_
    exact hnash (herrorPos (subsequence step)).le (profiles (subsequence step))
      (hchildNash (subsequence step))

end GameTheory
