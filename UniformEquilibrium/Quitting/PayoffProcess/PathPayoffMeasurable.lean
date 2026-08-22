/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Mathlib.MeasureTheory.Integral.DominatedConvergence
import UniformEquilibrium.Quitting.PayoffProcess.PathPayoffStability

/-!
# Measurability and integrability of quitting path payoffs

All action and payoff carriers are finite.  Coordinatewise measurable root
probabilities therefore make every survival-weighted absorption term
measurable, and the countable path sum is measurable.  The stopping-law bound
then transfers any integrable reward envelope to the path payoff.
-/

noncomputable section

namespace GameTheory

open MeasureTheory StochasticGame Math.Probability Math.PMFProduct

variable {ι Ω : Type} [Fintype ι] [DecidableEq ι] [MeasurableSpace Ω]

omit [DecidableEq ι] in
/-- Joint continue mass is measurable from the marginal Continue
probabilities. -/
theorem measurable_quittingStationaryContinueMass
    (root : Ω → ι → PMF Bool)
    (hroot : ∀ player,
      Measurable fun ω => (root ω player false).toReal) :
    Measurable fun ω => quittingStationaryContinueMass (root ω) := by
  simp_rw [quittingStationaryContinueMass_eq_prod_continueProbability]
  exact Finset.measurable_prod Finset.univ fun player _ => hroot player

omit [DecidableEq ι] in
/-- A finite survival product is measurable from measurable root
coordinates. -/
theorem measurable_quittingJointSurvivalWeight
    (roots : ℕ → Ω → ι → PMF Bool)
    (hroots : ∀ time player,
      Measurable fun ω => (roots time ω player false).toReal)
    (start fuel : ℕ) :
    Measurable fun ω =>
      quittingJointSurvivalWeight (fun time => roots time ω) start fuel := by
  simp_rw [quittingJointSurvivalWeight_eq_prod,
    quittingStationaryContinueMass_eq_prod_continueProbability]
  apply Finset.measurable_prod
  intro offset _
  apply Finset.measurable_prod
  intro player _
  exact hroots (start + offset) player

omit [DecidableEq ι] in
/-- One-stage absorbing payoff is measurable from coordinatewise measurable
tables and root probabilities. -/
theorem measurable_quittingRootAbsorbingContribution
    (reward : Ω → ({S : Finset ι // S.Nonempty} → Payoff ι))
    (root : Ω → ι → PMF Bool)
    (hreward : ∀ terminal player,
      Measurable fun ω => reward ω terminal player)
    (hroot : ∀ player action,
      Measurable fun ω => (root ω player action).toReal)
  (who : ι) :
    Measurable fun ω =>
      quittingRootAbsorbingContribution (reward ω) (root ω) who := by
  unfold quittingRootAbsorbingContribution quittingRootExpectedPayoff
  apply Measurable.tsum
  intro action
  simp_rw [pmfPi_apply, ENNReal.toReal_prod]
  apply Measurable.mul
  · apply Finset.measurable_prod
    intro player _
    exact hroot player (action player)
  · by_cases hquit : (quittingQuitters action).Nonempty
    · simpa only [quittingRootPayoff, hquit, ↓reduceDIte] using
        hreward ⟨quittingQuitters action, hquit⟩ who
    · simp only [quittingRootPayoff, hquit, ↓reduceDIte, Pi.zero_apply]
      exact measurable_const

omit [DecidableEq ι] in
/-- A varying-table path payoff is measurable from coordinatewise measurable
payoffs and action probabilities. -/
theorem measurable_quittingVariableTailValue
    (reward : ℕ → Ω → ({S : Finset ι // S.Nonempty} → Payoff ι))
    (roots : ℕ → Ω → ι → PMF Bool)
    (hreward : ∀ time terminal player,
      Measurable fun ω => reward time ω terminal player)
    (hroots : ∀ time player action,
      Measurable fun ω => (roots time ω player action).toReal)
    (who : ι) (start : ℕ) :
    Measurable fun ω => quittingVariableTailValue
      (fun time => reward time ω) (fun time => roots time ω) who start := by
  unfold quittingVariableTailValue
  apply Measurable.tsum
  intro offset
  exact (measurable_quittingJointSurvivalWeight roots
    (fun time player => hroots time player false) start offset).mul
      (measurable_quittingRootAbsorbingContribution
        (reward (start + offset)) (roots (start + offset))
        (hreward (start + offset)) (hroots (start + offset)) who)

omit [DecidableEq ι] in
/-- An integrable coordinate envelope makes the varying-table path payoff
integrable. -/
theorem integrable_quittingVariableTailValue
    (μ : Measure Ω)
    (reward : ℕ → Ω → ({S : Finset ι // S.Nonempty} → Payoff ι))
    (roots : ℕ → Ω → ι → PMF Bool)
    (hrewardMeasurable : ∀ time terminal player,
      Measurable fun ω => reward time ω terminal player)
    (hroots : ∀ time player action,
      Measurable fun ω => (roots time ω player action).toReal)
    (bound : Ω → ℝ) (hbound : Integrable bound μ)
    (hrewardBound : ∀ time ω terminal player,
      |reward time ω terminal player| ≤ |bound ω|)
    (who : ι) (start : ℕ) :
    Integrable (fun ω => quittingVariableTailValue
      (fun time => reward time ω) (fun time => roots time ω) who start) μ := by
  apply Integrable.mono' hbound.abs
  · exact (measurable_quittingVariableTailValue reward roots
      hrewardMeasurable hroots who start).aestronglyMeasurable
  · filter_upwards with ω
    simpa only [Real.norm_eq_abs] using
      abs_quittingVariableTailValue_le
        (fun time => reward time ω) (fun time => roots time ω) who start
        (abs_nonneg (bound ω)) (fun offset => hrewardBound (start + offset) ω)

end GameTheory
