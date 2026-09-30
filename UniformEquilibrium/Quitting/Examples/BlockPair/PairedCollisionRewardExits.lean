/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Examples.BlockPair.PairedCollisionRewardTable
import UniformEquilibrium.Quitting.Classification.Existence.PerfectSequenceExtraction
import UniformEquilibrium.Quitting.Stationary.EndpointCompiler
import UniformEquilibrium.Quitting.Stationary.CompleteBehavioralCap
import MathUE.PMFProduct.FiniteFubini

/-! # Actual low-parameter and sure-pair exits for the literal collision family -/

noncomputable section

namespace GameTheory.PairedCollisionReward

open StochasticGame _root_.Math.Probability Math.PMFProduct

/-- The signed capped-joint theorem applies even to arbitrarily negative parameters. -/
theorem exists_uniformPayoff_of_le_one {c : ℝ} (hc : c ≤ 1) :
    ∃ payoff : Payoff Player,
      (quittingGame (reward c)).IsUniformEquilibriumPayoff none payoff :=
  exists_uniformEquilibriumPayoff_of_soloExitPreference (unitSoloExit c)
    (cappedJointExit hc)

/-- Players zero and one quit surely; the two outsiders continue surely. -/
def surePairRoot : Player → PMF Bool :=
  ![PMF.pure true, PMF.pure true, PMF.pure false, PMF.pure false]

def surePairValue (c : ℝ) : Payoff Player := ![c, c, 1, 1]

theorem surePairRoot_successor (c : ℝ) :
    surePairValue c = quittingRootSuccessorPayoff (reward c) (surePairValue c)
      surePairRoot := by
  funext who
  unfold quittingRootSuccessorPayoff quittingRootExpectedPayoff
  rw [expect_pmfPi_fin4]
  fin_cases who <;>
    simp [surePairRoot, surePairValue, quittingRootPayoff, quittingQuitters, reward]

/-- Member Continue pays four; outsider joining pays zero. -/
theorem surePairRoot_endpointDifference (c : ℝ) (who : Player) :
    quittingRootEndpointDifference (reward c) (surePairValue c) surePairRoot who =
      ![c - 4, c - 4, -1, -1] who := by
  unfold quittingRootEndpointDifference quittingRootQuitPayoff
    quittingRootContinuePayoff quittingRootExpectedPayoff
  rw [expect_pmfPi_fin4, expect_pmfPi_fin4]
  fin_cases who <;>
    simp [surePairRoot, surePairValue, quittingRootPayoff, quittingQuitters, reward]

theorem surePairRoot_endpointNash {c : ℝ} (hc : 4 ≤ c) :
    IsεQuittingRootEndpointNash (reward c) (surePairValue c) 0 surePairRoot := by
  intro who
  rw [surePairRoot_endpointDifference]
  fin_cases who <;> simp [surePairRoot] <;> linarith

theorem surePairRoot_absorbs : quittingStationaryContinueMass surePairRoot < 1 := by
  rw [quittingStationaryContinueMass_eq_prod_continueProbability]
  norm_num [surePairRoot, Fin.prod_univ_succ]

theorem surePairRoot_contracts (who : Player) :
    quittingStationaryFixedOpponentsContinueMass surePairRoot who < 1 := by
  unfold quittingStationaryFixedOpponentsContinueMass quittingFixedOpponentsContinueMass
  rw [quittingStationaryContinueMass_eq_prod_continueProbability]
  fin_cases who <;> norm_num [surePairRoot, Fin.prod_univ_succ]

/-- Exact terminal Nash against all complete behavioral replacements, including Never. -/
theorem surePairProfile_isExactTerminalNash {c : ℝ} (hc : 4 ≤ c) :
    (quittingGame (reward c)).IsεAsymptoticNash (quittingTerminalPayoff (reward c)) 0
      (quittingStationaryProfile (reward c) surePairRoot) :=
  isZeroAsymptoticNash_stationary_of_fixedPoint_endpointNash_contracts
    (reward c) surePairRoot (surePairValue c) surePairRoot_absorbs
    (surePairRoot_successor c) (surePairRoot_endpointNash hc) surePairRoot_contracts

theorem surePairProfile_terminalPayoff (c : ℝ) :
    quittingTerminalPayoff (reward c)
      (quittingStationaryProfile (reward c) surePairRoot) = surePairValue c :=
  quittingTerminalPayoff_stationary_eq_of_fixedPoint (reward c) surePairRoot
    (surePairValue c) surePairRoot_absorbs (surePairRoot_successor c)

/-- Every complete behavioral replacement is capped at the displayed sure-pair payoff. -/
theorem surePairProfile_completeCap {c : ℝ} (hc : 4 ≤ c) (who : Player) :
    quittingContinuationBestResponseValue (reward c)
      (quittingStationaryProfile (reward c) surePairRoot) who = surePairValue c who := by
  rw [quittingContinuationBestResponseValue_stationary_eq_fullRateUnilateralCap]
  exact quittingStationaryFullRateUnilateralCap_eq_of_fixedPoint_endpointNash
    (reward c) surePairRoot (surePairValue c) surePairRoot_absorbs
    (surePairRoot_successor c) (surePairRoot_endpointNash hc)
    (isQuittingStationaryBoundaryAdmissible_of_contracts (reward c)
      surePairRoot (surePairValue c) surePairRoot_contracts) who

theorem surePair_isUniformEquilibriumPayoff {c : ℝ} (hc : 4 ≤ c) :
    (quittingGame (reward c)).IsUniformEquilibriumPayoff none (surePairValue c) :=
  isUniformEquilibriumPayoff_of_stationaryEndpointCertificate_contracts
    (reward c) surePairRoot (surePairValue c) surePairRoot_absorbs
    (surePairRoot_successor c) (surePairRoot_endpointNash hc) surePairRoot_contracts

end GameTheory.PairedCollisionReward
