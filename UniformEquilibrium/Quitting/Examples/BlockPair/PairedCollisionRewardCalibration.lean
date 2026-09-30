/-
Copyright (c) 2026 UniformEquilibrium contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: UniformEquilibrium contributors
-/

import UniformEquilibrium.Quitting.Examples.BlockPair.PairedCollisionRewardPeriodic
import UniformEquilibrium.Quitting.Examples.SolanVieilleBoundaryEquilibrium

/-!
# Parameter-one calibration of the paired-collision construction

The existing quartic uniqueness theorem identifies every supplied admissible
rate pair at parameter one with the old boundary construction. Its sharper
isolations, literal roots, profile and payoff therefore apply without a new
polynomial root selection or uniqueness proof.
-/

noncomputable section

namespace GameTheory.PairedCollisionReward.PeriodicRates

open _root_.Math.PairedPhasePolynomialRoots

variable (rates : PeriodicRates 1)

theorem secondary_formula_at_one :
    rates.secondary = (4 * rates.primary ^ 2 - 1) / (3 * rates.primary ^ 2) := by
  have h := secondaryRate_eq_of_secondaryResidual_zero
    (by norm_num : (1 : ℝ) ∈ Set.Icc (1 : ℝ) 2)
    ⟨rates.primary_pos, rates.primary_lt_one.le⟩ rates.secondary_zero
  norm_num [secondaryRate, startingPolynomial, affineEndpoint] at h
  simpa only [mul_comm] using h

theorem primary_polynomial_at_one :
    FourPlayerPairedSingleton.periodTwoPolynomial rates.primary = 0 := by
  have hres := rates.primary_zero
  dsimp [primaryResidual, affineEndpoint] at hres
  have hfirst : rates.secondary *
      (1 - rates.primary + 3 * rates.secondary - 2 * rates.primary * rates.secondary) -
        1 = 0 := by nlinarith
  rw [rates.secondary_formula_at_one,
    FourPlayerPairedSingleton.periodTwo_secondary_substitution_factorization
      rates.primary_pos.ne'] at hfirst
  have hden : (9 : ℝ) * rates.primary ^ 4 ≠ 0 :=
    mul_ne_zero (by norm_num) (pow_ne_zero 4 rates.primary_pos.ne')
  have hnum := (div_eq_iff hden).mp hfirst
  simp only [zero_mul] at hnum
  have hfactor : -(rates.primary - 1) ≠ 0 := by linarith [rates.primary_lt_one]
  exact (mul_eq_zero.mp hnum).resolve_left hfactor

/-- The old uniqueness result applies on the full admissible interval, not just a bracket. -/
theorem primary_eq_periodTwoParameter :
    rates.primary = FourPlayerPairedSingleton.periodTwoParameter :=
  (Classical.choose_spec FourPlayerPairedSingleton.existsUnique_periodTwoParameter).2
    rates.primary ⟨⟨rates.half_lt, rates.primary_lt_one⟩, rates.primary_polynomial_at_one⟩

theorem secondary_eq_periodTwoSecondary :
    rates.secondary = FourPlayerPairedSingleton.periodTwoSecondary := by
  rw [rates.secondary_formula_at_one, rates.primary_eq_periodTwoParameter]
  rfl

theorem primary_mem_sharpInterval :
    rates.primary ∈ Set.Ioo ((373 : ℝ) / 500) (747 / 1000) := by
  rw [rates.primary_eq_periodTwoParameter]
  exact SolanVieilleBoundary.periodTwoParameter_mem_sharpInterval

theorem secondary_mem_sharpInterval :
    rates.secondary ∈ Set.Ioo ((73 : ℝ) / 100) (74 / 100) := by
  rw [rates.secondary_eq_periodTwoSecondary]
  exact SolanVieilleBoundary.periodTwoSecondary_mem_isolatingInterval

theorem primaryCoin_at_one : rates.primaryCoin = FourPlayerPairedSingleton.primaryCoin := by
  simp only [primaryCoin, commonCoin, rates.primary_eq_periodTwoParameter,
    FourPlayerPairedSingleton.primaryCoin]

theorem secondaryCoin_at_one :
    rates.secondaryCoin = FourPlayerPairedSingleton.secondaryCoin := by
  simp only [secondaryCoin, commonCoin, rates.secondary_eq_periodTwoSecondary,
    FourPlayerPairedSingleton.secondaryCoin]

theorem phaseARoot_at_one : rates.phaseARoot = FourPlayerPairedSingleton.oddRoot := by
  simp only [phaseARoot, rates.primaryCoin_at_one, rates.secondaryCoin_at_one,
    FourPlayerPairedSingleton.oddRoot]

theorem phaseBRoot_at_one : rates.phaseBRoot = FourPlayerPairedSingleton.evenRoot := by
  simp only [phaseBRoot, rates.primaryCoin_at_one, rates.secondaryCoin_at_one,
    FourPlayerPairedSingleton.evenRoot]

theorem cycleRoot_at_one : rates.cycleRoot =
    quittingCyclicContinuationBlockCycle 1 FourPlayerPairedSingleton.periodTwoBlock := by
  funext phase
  rw [FourPlayerPairedSingleton.quittingCyclicContinuationBlockCycle_periodTwoBlock]
  fin_cases phase <;> simp [cycleRoot, rates.phaseARoot_at_one, rates.phaseBRoot_at_one]

/-- Calibration is an equality of actual behavioral profiles, not only of their payoffs. -/
theorem profile_at_one : rates.profile 0 = FourPlayerPairedSingleton.periodTwoProfile := by
  change quittingCyclicBehaviorProfile SolanVieilleBoundary.boundaryReward rates.cycleRoot 0 =
    quittingCyclicBehaviorProfile SolanVieilleBoundary.boundaryReward
      (quittingCyclicContinuationBlockCycle 1 FourPlayerPairedSingleton.periodTwoBlock) 0
  rw [rates.cycleRoot_at_one]

theorem phaseAValue_at_one : rates.phaseAValue = SolanVieilleBoundary.crossBlockPayoff := by
  simp [phaseAValue, affineEndpoint, rates.primary_eq_periodTwoParameter,
    rates.secondary_eq_periodTwoSecondary, SolanVieilleBoundary.crossBlockPayoff]

theorem phaseBValue_at_one : rates.phaseBValue = FourPlayerPairedSingleton.evenValue := by
  simp [phaseBValue, affineEndpoint, rates.primary_eq_periodTwoParameter,
    rates.secondary_eq_periodTwoSecondary, FourPlayerPairedSingleton.evenValue]

end GameTheory.PairedCollisionReward.PeriodicRates
