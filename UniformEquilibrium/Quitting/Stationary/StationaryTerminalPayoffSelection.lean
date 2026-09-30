import UniformEquilibrium.Quitting.Stationary.SnellCap
import UniformEquilibrium.Quitting.Stationary.Root
import UniformEquilibrium.Quitting.Terminal.TargetTail.TerminalUniformPayoffSelection

/-! # One fixed target selected from contracting stationary terminal approximations -/

noncomputable section

namespace GameTheory

open Filter

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Compactness of actual payoff vectors preserves the stationary witnesses.
Only payoffs are passed to a subsequence: no limiting strategy or cap is used. -/
theorem exists_uniformPayoff_stationaryTargetAcceptance_of_terminalApproximations
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (happroximation : ∀ accuracy : ℝ, 0 < accuracy →
      ∃ root : ι → PMF Bool,
        (∀ who, quittingStationaryFixedOpponentsContinueMass root who < 1) ∧
        (quittingGame reward).IsεAsymptoticNash (quittingTerminalPayoff reward) accuracy
          (quittingStationaryProfile reward root)) :
    ∃ target : Payoff ι,
      (quittingGame reward).IsUniformEquilibriumPayoff none target ∧
      ∀ accuracy : ℝ, 0 < accuracy →
        ∃ root : ι → PMF Bool,
          (∀ who, quittingStationaryFixedOpponentsContinueMass root who < 1) ∧
          (quittingGame reward).IsεAsymptoticNash (quittingTerminalPayoff reward) accuracy
            (quittingStationaryProfile reward root) ∧
          ∀ who, |quittingTerminalPayoff reward (quittingStationaryProfile reward root) who -
            target who| ≤ accuracy := by
  let error : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  have herrorPositive : ∀ n, 0 < error n := by
    intro n
    dsimp [error]
    positivity
  choose roots hcontracts hnash using
    fun n => happroximation (error n) (herrorPositive n)
  let payoffs : ℕ → Payoff ι := fun n =>
    quittingTerminalPayoff reward (quittingStationaryProfile reward (roots n))
  have hmem : ∀ n, payoffs n ∈
      Set.Icc (fun _ => -quittingRewardBound reward)
        (fun _ => quittingRewardBound reward) := by
    intro n
    exact quittingTerminalPayoff_mem_rewardCube reward _
  obtain ⟨target, -, subsequence, hsubsequence, hpayoffLimit⟩ :=
    (isCompact_Icc : IsCompact
      (Set.Icc (fun _ : ι => -quittingRewardBound reward)
        (fun _ : ι => quittingRewardBound reward))).tendsto_subseq hmem
  have herrorLimit : Tendsto error atTop (nhds 0) := by
    simpa [error] using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hselectedError : Tendsto (error ∘ subsequence) atTop (nhds 0) :=
    herrorLimit.comp hsubsequence.tendsto_atTop
  have hUE := quittingGame_isUniformEquilibriumPayoff_of_terminalNash_tendsto
    (filter := atTop) reward target (error ∘ subsequence)
    (fun n => quittingStationaryProfile reward (roots (subsequence n)))
    hselectedError (Filter.Frequently.of_forall fun n => hnash (subsequence n))
    hpayoffLimit
  refine ⟨target, hUE, ?_⟩
  intro accuracy haccuracy
  have heventuallyError : ∀ᶠ n in atTop, error (subsequence n) < accuracy :=
    (tendsto_order.1 hselectedError).2 accuracy haccuracy
  have heventuallyPayoff : ∀ᶠ n in atTop, ∀ who,
      |payoffs (subsequence n) who - target who| < accuracy := by
    apply Filter.eventually_all.mpr
    intro who
    have hcoordinate := (continuous_apply who).tendsto target |>.comp hpayoffLimit
    have hball := hcoordinate.eventually (Metric.ball_mem_nhds (target who) haccuracy)
    filter_upwards [hball] with n hn
    simpa only [Metric.mem_ball, Real.dist_eq, Function.comp_apply] using hn
  obtain ⟨n, herrorSmall, hpayoffSmall⟩ :=
    (heventuallyError.and heventuallyPayoff).exists
  exact ⟨roots (subsequence n), hcontracts (subsequence n),
    (hnash (subsequence n)).mono herrorSmall.le, fun who => (hpayoffSmall who).le⟩

end GameTheory
