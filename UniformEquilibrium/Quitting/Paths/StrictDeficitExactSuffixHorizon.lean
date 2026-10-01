import UniformEquilibrium.Quitting.Paths.StrictDeficitExactSuffixNash
import UniformEquilibrium.Quitting.Paths.JointAbsorptionHorizonRate

/-! # Same-source quantitative strict-deficit suffix equilibrium

One actual reverse-prefix diagonal supplies all rows, values and suffixes.
The row absorption floor is retained in the prescribed geometric horizon bound.
Complete reply regret uses the actual opponent live-tail Cesàro error, not
deleted-opponent geometric absorption. The SAME profile works at every accuracy.
-/

noncomputable section

namespace GameTheory

open Filter
open scoped Topology

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The original common diagonal witness has exact Nash at every literal
suffix, geometric prescribed delivery, full behavioral regret control and
same-profile uniform witnesses at the actual fixed suffix payoff. -/
theorem exists_strictDeficitExactSuffix_sameProfile_quantitativeUniform
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    {M gap : ℝ} (hgap : 0 < gap)
    (hreward : ∀ terminal who, |reward terminal who| ≤ M)
    (hdeficit : HasQuittingFiniteWordStrictSingletonDeficit reward gap)
    (hsolo : ∀ who, 0 ≤ reward (quittingSingletonTerminal who) who) :
    ∃ (roots : ℕ → ι → PMF Bool) (value : ℕ → Payoff ι) (centers : ℕ → ℕ),
      StrictMono centers ∧
      (∀ time, Tendsto
        (fun rank => quittingSimplexOfRoot
          (quittingStrictDeficitExactWordNextRoot reward gap (centers rank - time)))
        atTop (nhds (quittingSimplexOfRoot (roots time)))) ∧
      (∀ time, Tendsto
        (fun rank => quittingStrictDeficitExactWordValue reward gap
          (centers rank + 1 - time)) atTop (nhds (value time))) ∧
      (∀ time, gap / (4 * M + gap) ≤ quittingRootAbsorptionMass (roots time)) ∧
      (∀ time, value time = quittingRootSuccessorPayoff reward (value (time + 1)) (roots time)) ∧
      (∀ time, value time = fun who => quittingRootSequenceTerminalValue reward roots who time) ∧
      (∀ suffix, (quittingGame reward).IsεAsymptoticNash (quittingTerminalPayoff reward) 0
        (quittingRootSequenceProfile reward roots suffix)) ∧
      ∀ suffix,
        (∀ horizon, 0 < horizon → ∀ who,
          |(quittingGame reward).finiteAveragePayoff none horizon
              (quittingRootSequenceProfile reward roots suffix) who - value suffix who| ≤
            M / ((gap / (4 * M + gap)) * (horizon : ℝ))) ∧
        (∀ horizon, 0 < horizon → ∀ who
            (deviation : (quittingGame reward).BehaviorStrategy who),
          (quittingGame reward).finiteAveragePayoff none horizon
              (Function.update (quittingRootSequenceProfile reward roots suffix)
                who deviation) who -
            (quittingGame reward).finiteAveragePayoff none horizon
              (quittingRootSequenceProfile reward roots suffix) who ≤
            M * quittingOpponentLiveTailCesaro reward
              (quittingRootSequenceProfile reward roots suffix) who horizon +
            M / ((gap / (4 * M + gap)) * (horizon : ℝ))) ∧
        (∀ who, Tendsto
          (fun horizon => M * quittingOpponentLiveTailCesaro reward
              (quittingRootSequenceProfile reward roots suffix) who horizon +
            M / ((gap / (4 * M + gap)) * (horizon : ℝ))) atTop (nhds 0)) ∧
        (∀ error, 0 < error → ∃ threshold : ℕ, ∀ horizon, threshold ≤ horizon →
          (quittingGame reward).IsεHorizonNash none horizon error
            (quittingRootSequenceProfile reward roots suffix) ∧
          ∀ who, |(quittingGame reward).finiteAveragePayoff none horizon
            (quittingRootSequenceProfile reward roots suffix) who - value suffix who| ≤ error) ∧
        (quittingGame reward).IsUniformEquilibriumPayoff none (value suffix) := by
  obtain ⟨roots, value, centers, hcenters, hrows, hvalues, hlower, hpolicy, hterminal⟩ :=
    exists_strictDeficitExactSuffix_payoffDiagonal reward hgap hreward hdeficit
  obtain ⟨who, _⟩ := hdeficit []
  have hM : 0 ≤ M := quittingRewardCoordinateBound_nonneg_of_player reward who hreward
  have hcharge : 0 < gap / (4 * M + gap) := by positivity
  have hnash (suffix : ℕ) : (quittingGame reward).IsεAsymptoticNash
      (quittingTerminalPayoff reward) 0 (quittingRootSequenceProfile reward roots suffix) :=
    quittingStrictDeficitExactSuffix_isZeroAsymptoticNash
      reward hgap hreward hdeficit hsolo roots value centers
      hcenters hrows hvalues hterminal suffix
  have hactual (suffix : ℕ) : quittingTerminalPayoff reward
      (quittingRootSequenceProfile reward roots suffix) = value suffix := by
    funext player
    exact (congrFun (hterminal suffix) player).symm
  refine ⟨roots, value, centers, hcenters, hrows, hvalues, hlower, hpolicy, hterminal, hnash, ?_⟩
  intro suffix
  have huniform : ∀ error, 0 < error → ∃ threshold : ℕ, ∀ horizon, threshold ≤ horizon →
      (quittingGame reward).IsεHorizonNash none horizon error
        (quittingRootSequenceProfile reward roots suffix) ∧
      ∀ player, |(quittingGame reward).finiteAveragePayoff none horizon
        (quittingRootSequenceProfile reward roots suffix) player - value suffix player| ≤
        error := by
    intro error herror
    obtain ⟨nashThreshold, hnashThreshold⟩ :=
      quittingGame_isUniformεEquilibrium_of_terminalNash_of_solo_nonneg
        reward (quittingRootSequenceProfile reward roots suffix) herror
        (hnash suffix) M hM hreward hsolo
    have hdelivery : ∀ᶠ horizon : ℕ in atTop, ∀ player,
        |(quittingGame reward).finiteAveragePayoff none horizon
          (quittingRootSequenceProfile reward roots suffix) player - value suffix player| <
          error := by
      apply eventually_all.mpr
      intro player
      have hlimit := tendsto_finiteAveragePayoff_quittingGame
        reward (quittingRootSequenceProfile reward roots suffix) player
      rw [hactual suffix] at hlimit
      have hzero : Tendsto (fun horizon =>
          (quittingGame reward).finiteAveragePayoff none horizon
            (quittingRootSequenceProfile reward roots suffix) player - value suffix player)
          atTop (nhds 0) := by
        simpa only [sub_self] using hlimit.sub_const (value suffix player)
      exact (tendsto_order.1 (hzero.abs)).2 error (by simpa using herror)
    obtain ⟨deliveryThreshold, hdeliveryThreshold⟩ := eventually_atTop.mp hdelivery
    refine ⟨max nashThreshold deliveryThreshold, ?_⟩
    intro horizon hhorizon
    exact ⟨hnashThreshold horizon ((le_max_left _ _).trans hhorizon),
      fun player => (hdeliveryThreshold horizon ((le_max_right _ _).trans hhorizon) player).le⟩
  refine ⟨?_, ?_, ?_, huniform, ?_⟩
  · intro horizon hhorizon player
    rw [← hactual suffix]
    exact abs_finiteAveragePayoff_sub_terminal_rootSequence_of_absorption_lower
      reward roots suffix player hcharge hlower (fun terminal => hreward terminal player)
      horizon hhorizon
  · intro horizon hhorizon player deviation
    exact finiteAveragePayoff_update_sub_rootSequence_le_of_terminalNash_absorption_lower
      reward roots suffix player deviation hcharge hlower
      (fun terminal => hreward terminal player) (hsolo player) (hnash suffix) horizon hhorizon
  · intro player
    have hopponent := (tendsto_quittingOpponentLiveTailCesaro_zero reward
      (quittingRootSequenceProfile reward roots suffix) player).const_mul M
    have hgeometric := tendsto_const_div_atTop_nhds_zero_nat (M / (gap / (4 * M + gap)))
    have hzero := hopponent.add hgeometric
    simpa only [div_div, mul_zero, add_zero] using hzero
  intro error herror
  obtain ⟨threshold, hthreshold⟩ := huniform error herror
  exact ⟨quittingRootSequenceProfile reward roots suffix, threshold, hthreshold⟩

end GameTheory
