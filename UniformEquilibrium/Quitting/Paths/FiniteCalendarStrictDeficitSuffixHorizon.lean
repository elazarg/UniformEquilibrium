import UniformEquilibrium.Quitting.Paths.FiniteCalendarStrictDeficitSource
import UniformEquilibrium.Quitting.Paths.StrictDeficitExactSuffixHorizon

/-! # Raw-calendar sources for the same quantitative strict-deficit suffixes

Both raw source forms delegate to one existing actual reverse-prefix diagonal.
The root/value/center witness, actual absorption floor, every-suffix terminal
Nash, quantitative errors and fixed-target same-profile witnesses are retained.
-/

noncomputable section
namespace GameTheory
open Filter
open scoped Topology
variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- A supplied literal raw margin controls the SAME source diagonal and every
suffix, without assuming caps survive finite-calendar payoff compression. -/
theorem exists_finiteCalendarRawDeficit_sameProfile_quantitativeUniform
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    {M gap : ℝ} (hgap : 0 < gap)
    (hreward : ∀ terminal who, |reward terminal who| ≤ M)
    (hraw : HasQuittingFiniteCalendarRawStrictSingletonDeficit reward gap)
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
  exact exists_strictDeficitExactSuffix_sameProfile_quantitativeUniform
    reward hgap hreward
    (hasQuittingFiniteWordStrictSingletonDeficit_of_finiteCalendarRaw reward gap hraw) hsolo

/-- The strict raw predicate internally supplies its common positive margin
before the actual same-diagonal source construction; no margin is an input. -/
theorem exists_finiteCalendarRawStrict_sameProfile_quantitativeUniform
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) {M : ℝ}
    (hreward : ∀ terminal who, |reward terminal who| ≤ M)
    (hraw : HasQuittingFiniteCalendarRawStrictExclusion reward)
    (hsolo : ∀ who, 0 ≤ reward (quittingSingletonTerminal who) who) :
    ∃ gap > 0,
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
  obtain ⟨gap, hgap, hdeficit⟩ :=
    exists_positive_finiteWordStrictSingletonDeficit_of_finiteCalendarRawStrict reward hraw
  refine ⟨gap, hgap, ?_⟩
  exact exists_strictDeficitExactSuffix_sameProfile_quantitativeUniform
    reward hgap hreward hdeficit hsolo

end GameTheory
