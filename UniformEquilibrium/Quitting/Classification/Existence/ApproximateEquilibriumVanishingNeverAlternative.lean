/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import MathUE.Topology.FiniteLabelSubsequence
import UniformEquilibrium.Quitting.Bellman.Finite.NashBellmanQuitEndpointLimit
import UniformEquilibrium.Quitting.Classification.Existence.StationarilyGeneratedBranch
import UniformEquilibrium.Quitting.Classification.SimonFiniteOrbit.ArbitraryNeverExtraction
import UniformEquilibrium.Quitting.Classification.TableExistenceBranches
import UniformEquilibrium.Quitting.Cycles.PhantomBoundaryRestart
import UniformEquilibrium.Quitting.Paths.JointSurvivalSummability
import UniformEquilibrium.Quitting.Paths.VanishingNashRootSequenceFamily
import UniformEquilibrium.Quitting.Punishment.ZeroSoloDisjunct

/-!
# Approximate equilibria: zero solo or vanishing Never

An actual root-sequence approximate equilibrium with positive probability of
never absorbing bounds every singleton self-reward by its Nash error divided
by that probability.  Applying this estimate to approximate equilibria at a
canonical vanishing error scale gives an exhaustive conditional alternative:
either all singleton self-rewards are nonpositive, or the selected family has
vanishing Nash error and vanishing `Never` mass.

The source hypothesis is the existing infinite-horizon behavioral
approximate-equilibrium interface.  It is not finite-horizon Nash existence.
The second arm does not assert complete absorption, unweighted tailwise Nash,
stagewise perfection, or absorption-path compactness.
-/

noncomputable section

namespace GameTheory

open Filter StochasticGame Math.Probability
open scoped Topology

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- A global root-sequence Nash cap with positive `Never` mass bounds every
singleton self-reward by the Nash error divided by that mass. -/
theorem singletonReward_le_nashError_div_never
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (ε : ℝ) (hε : 0 ≤ ε)
    (hnash : IsεQuittingRootSequenceNash reward ε roots)
    (hnever : 0 < quittingJointSurvivalLimit roots 0) (who : ι) :
    reward (quittingSingletonTerminal who) who ≤
      ε / quittingJointSurvivalLimit roots 0 := by
  let q := quittingJointSurvivalLimit roots 0
  have hcharge : Summable (fun time =>
      quittingRootAbsorptionMass (roots time)) :=
    summable_quittingRootAbsorptionMass_of_jointSurvivalLimit_pos
      roots 0 hnever
  have htotalZero : Tendsto (fun time =>
      quittingRootAbsorptionMass (roots time)) atTop (nhds 0) :=
    hcharge.tendsto_atTop_zero
  have hopponentZero : Tendsto (fun time =>
      quittingRootOpponentAbsorptionMass (roots time) who) atTop (nhds 0) := by
    apply squeeze_zero
    · exact fun time => quittingRootOpponentAbsorptionMass_nonneg (roots time) who
    · exact fun time =>
        quittingRootOpponentAbsorptionMass_le_absorptionMass (roots time) who
    · exact htotalZero
  have hlower : Tendsto (fun time =>
      reward (quittingSingletonTerminal who) who -
        2 * quittingRewardBound reward *
          quittingRootOpponentAbsorptionMass (roots time) who)
      atTop (nhds (reward (quittingSingletonTerminal who) who)) := by
    simpa using tendsto_const_nhds.sub
      (hopponentZero.const_mul (2 * quittingRewardBound reward))
  have hterminal : Tendsto (fun time =>
      quittingRootSequenceTerminalValue reward roots who time)
      atTop (nhds 0) := by
    simpa using
      tendsto_quittingRootSequenceTerminalValue_tail_zero_of_survivalLimit_pos
        reward roots who 0 (abs_reward_le_quittingRewardBound reward) hnever
  have hupper : Tendsto (fun time =>
      quittingRootSequenceTerminalValue reward roots who time + ε / q)
      atTop (nhds (ε / q)) := by
    simpa using hterminal.add_const (ε / q)
  apply le_of_tendsto_of_tendsto' hlower hupper
  intro time
  have hreach : 0 < quittingJointSurvivalWeight roots 0 time :=
    hnever.trans_le (le_quittingJointSurvivalWeight_of_tendsto roots 0
      (tendsto_quittingJointSurvivalLimit roots 0) time)
  have hrow :=
    isεQuittingRootNash_tailVector_of_isεQuittingRootSequenceNash
      reward roots hnash time hreach
  have hquit := quittingRootQuitPayoff_le_successor_add_of_isεNash
    reward (quittingRootSequenceTailVector reward roots (time + 1))
    (ε / quittingJointSurvivalWeight roots 0 time) (roots time) who hrow
  rw [← quittingRootSequenceTerminalValue_eq_successorPayoff_tailVector]
    at hquit
  have hqReach : q ≤ quittingJointSurvivalWeight roots 0 time :=
    le_quittingJointSurvivalWeight_of_tendsto roots 0
      (tendsto_quittingJointSurvivalLimit roots 0) time
  have hquotient :
      ε / quittingJointSurvivalWeight roots 0 time ≤ ε / q := by
    exact div_le_div_of_nonneg_left hε hnever hqReach
  have hendpoint :=
    abs_quittingRootQuitPayoff_sub_singletonReward_le_two_mul_opponentAbsorptionMass
      reward (quittingRootSequenceTailVector reward roots (time + 1))
      (roots time) who (quittingRewardBound reward)
      (abs_reward_le_quittingRewardBound reward)
  linarith [abs_le.mp hendpoint |>.1]

/-- Approximate equilibria at every positive accuracy either force the exact
zero-solo condition or supply actual Nash root sequences whose Nash errors and
`Never` masses both vanish. -/
theorem isQuittingZeroSolo_or_nonempty_vanishingNashFamily
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (happrox : QuittingApproximateEquilibriumExistence reward) :
    IsQuittingZeroSolo reward ∨
      Nonempty (QuittingRootSequenceVanishingNashFamily reward) := by
  classical
  let error : ℕ → ℝ := fun index => 1 / ((index : ℝ) + 1)
  have herrorPos : ∀ index, 0 < error index := by
    intro index
    exact one_div_pos.mpr (by positivity)
  let roots : ℕ → ℕ → ι → PMF Bool := fun index =>
    Classical.choose (happrox (error index) (herrorPos index))
  have hnash : ∀ index,
      IsεQuittingRootSequenceNash reward (error index) (roots index) := by
    intro index
    exact Classical.choose_spec (happrox (error index) (herrorPos index))
  have herrorZero : Tendsto error atTop (nhds 0) := by
    exact tendsto_one_div_add_atTop_nhds_zero_nat
  let never : ℕ → ℝ := fun index =>
    quittingJointSurvivalLimit (roots index) 0
  by_cases hneverZero : Tendsto never atTop (nhds 0)
  · exact Or.inr ⟨{
      roots := roots
      error := error
      nash := hnash
      error_tendsto_zero := herrorZero
      never_tendsto_zero := hneverZero }⟩
  · left
    have hneverNonneg : ∀ index, 0 ≤ never index := by
      intro index
      exact quittingJointSurvivalLimit_nonneg (roots index) 0
    obtain ⟨eta, heta, hfrequent⟩ :=
      Math.exists_pos_frequently_ge_of_nonneg_of_not_tendsto_zero
        never hneverNonneg hneverZero
    obtain ⟨subsequence, hsubsequence, hfloor⟩ :=
      extraction_of_frequently_atTop hfrequent
    intro who
    have hbound : ∀ index,
        reward (quittingSingletonTerminal who) who ≤
          error (subsequence index) / eta := by
      intro index
      have hneverPos : 0 < never (subsequence index) :=
        heta.trans_le (hfloor index)
      calc
        reward (quittingSingletonTerminal who) who ≤
            error (subsequence index) / never (subsequence index) := by
          exact singletonReward_le_nashError_div_never reward
            (roots (subsequence index)) (error (subsequence index))
            (herrorPos _).le
            (hnash (subsequence index)) hneverPos who
        _ ≤ error (subsequence index) / eta :=
          div_le_div_of_nonneg_left (herrorPos _).le heta (hfloor index)
    have hboundZero : Tendsto (fun index =>
        error (subsequence index) / eta) atTop (nhds 0) := by
      have hsubsequenceError :=
        herrorZero.comp hsubsequence.tendsto_atTop
      simpa using hsubsequenceError.div_const eta
    exact le_of_tendsto_of_tendsto' tendsto_const_nhds hboundZero hbound

/-- The zero-solo arm of the alternative is literally the stationary branch,
witnessed at every positive tolerance by the exact all-Continue profile. -/
theorem quittingStationaryεEquilibriumExistence_of_zeroSolo
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hzero : IsQuittingZeroSolo reward) :
    QuittingStationaryεEquilibriumExistence reward := by
  intro ε hε
  refine ⟨quittingAllContinueRoot, ?_⟩
  exact
    (isZeroAsymptoticNash_quittingAlwaysContinue_of_zeroSolo reward hzero).mono
      hε.le

namespace QuittingLCPClassification

/-- Over an arbitrary-never payoff table, approximate-equilibrium existence
gives the literal stationary S.1 branch or a normalized zero-never family of
actual Nash root sequences with vanishing `Never` mass. -/
theorem QuittingPayoffTable.stationary_or_vanishingNeverNashFamily
    (table : QuittingPayoffTable ι)
    (happrox : table.ApproximateEquilibriumExistence) :
    table.StationaryεEquilibriumExistence ∨
      Nonempty
        (QuittingRootSequenceVanishingNashFamily table.zeroNeverReward) := by
  have hzeroNever : QuittingApproximateEquilibriumExistence
      table.zeroNeverReward :=
    (table.approximateEquilibriumExistence_iff_zeroNever).mp happrox
  rcases isQuittingZeroSolo_or_nonempty_vanishingNashFamily
      table.zeroNeverReward hzeroNever with hzero | hfamily
  · left
    exact (table.stationaryεEquilibriumExistence_iff).2
      (quittingStationaryεEquilibriumExistence_of_zeroSolo
        table.zeroNeverReward hzero)
  · exact Or.inr hfamily

end QuittingLCPClassification

end GameTheory
