/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.ExactRepairCertificate
import MathUE.PMFProduct.FiniteFubini
import MathUE.ProbabilityMassFunction.Bool

/-!
# Actual-data promotion of the mixed cutoff-one regression

The checked finite table has the
zero-tail root `(1/2, 1/2)`.  This file is the proof-carrying promotion of
that finite datum: it constructs the root and reward table directly in Lean,
checks the two endpoint Nash equalities and the positive continuation safety,
and names the resulting uniform-equilibrium payoff as `(0, 0)`.

The numerical table is external evidence and is not used as an axiom or
constructor input here.
-/

noncomputable section

namespace GameTheory
namespace QuittingCutoffOneMixedActual

open StochasticGame Math.Probability Math.PMFProduct

-- BEGIN GENERATED CUTOFF_ONE_MIXED_DATA
-- checked finite table
-- fingerprint: sha256:a94fe0c3e4cb98f85c5632cc6169da76c7d3b75f30aaf92f69084da0734a36f5
abbrev Player := Fin 2
abbrev Terminal := {S : Finset Player // S.Nonempty}

/-- The two-player terminal reward rows from the source table. -/
def reward (quitters : Terminal) : Payoff Player :=
  if quitters.1 = {0} then ![-1, 0]
  else if quitters.1 = {1} then ![0, -1]
  else ![1, 1]

/-- The hinted `(1/2, 1/2)` product root from the source table. -/
def root : Player → PMF Bool := fun _ => PMF.uniformOfFintype Bool

/-- The exact zero-tail payoff recomputed from the source table. -/
def value : Payoff Player := ![0, 0]
-- END GENERATED CUTOFF_ONE_MIXED_DATA

@[simp] theorem quitters_vector (a b : Bool) :
    quittingQuitters (![a, b] : Player → Bool) =
      (if a then {0} else ∅) ∪ (if b then {1} else ∅) := by
  ext who
  fin_cases who <;> cases a <;> cases b <;> simp [quittingQuitters]

theorem quitPayoff_eq_value (who : Player) :
    quittingRootQuitPayoff reward (0 : Payoff Player) root who = value who := by
  unfold quittingRootQuitPayoff quittingRootExpectedPayoff
  rw [Math.PMFProduct.expect_pmfPi_fin2]
  fin_cases who <;>
    simp [root, quittingRootPayoff, reward, value, quitters_vector,
      show ({1, 0} : Finset Player) ≠ {0} by decide,
      show ({1, 0} : Finset Player) ≠ {1} by decide,
      Math.ProbabilityMassFunction.expect_uniformOfFintype_bool]

theorem continuePayoff_eq_value (who : Player) :
    quittingRootContinuePayoff reward (0 : Payoff Player) root who = value who := by
  unfold quittingRootContinuePayoff quittingRootExpectedPayoff
  rw [Math.PMFProduct.expect_pmfPi_fin2]
  fin_cases who <;>
    simp [root, quittingRootPayoff, reward, value, quitters_vector,
      Math.ProbabilityMassFunction.expect_uniformOfFintype_bool]

theorem root_isEndpointNash_zero :
    IsεQuittingRootEndpointNash reward (0 : Payoff Player) 0 root := by
  intro who
  rw [quittingRootEndpointDifference, quitPayoff_eq_value,
    continuePayoff_eq_value]
  norm_num

theorem root_isNash_zero :
    IsεQuittingRootNash reward (0 : Payoff Player) 0 root := by
  exact (isZeroQuittingRootEndpointNash_iff_isZeroQuittingRootNash
    reward (0 : Payoff Player) root).1 root_isEndpointNash_zero

theorem root_successor_zero :
    quittingRootSuccessorPayoff reward (0 : Payoff Player) root = value := by
  funext who
  rw [quittingRootSuccessorPayoff_eq_endpointMix,
    quitPayoff_eq_value, continuePayoff_eq_value]
  simp [root, PMF.uniformOfFintype_apply, value]
  ring

@[simp] theorem positiveSingletonDebtCap (who : Player) :
    quittingPositiveSingletonDebtCap reward who = 0 := by
  fin_cases who <;>
    simp [quittingPositiveSingletonDebtCap, quittingSingletonTerminal, reward]

theorem positiveContinuePayoff_eq_value (who : Player) :
    quittingCutoffOnePositiveContinuePayoff reward root who = value who := by
  unfold quittingCutoffOnePositiveContinuePayoff quittingRootContinuePayoff
    quittingRootExpectedPayoff
  rw [Math.PMFProduct.expect_pmfPi_fin2]
  fin_cases who <;>
    simp [root, quittingRootPayoff, reward, value, quitters_vector,
      Math.ProbabilityMassFunction.expect_uniformOfFintype_bool]

theorem safe : ∀ who,
    quittingCutoffOnePositiveContinuePayoff reward root who ≤
      quittingRootSuccessorPayoff reward (0 : Payoff Player) root who := by
  intro who
  rw [positiveContinuePayoff_eq_value, root_successor_zero]

/-- The certificate assembled from the actual cutoff-one table. -/
def certificate : QuittingCutoffOneRepairCertificate reward where
  root := root
  rootNash := root_isNash_zero
  safe := safe

theorem certificate_payoff : certificate.payoff = value := by
  unfold QuittingCutoffOneRepairCertificate.payoff certificate
  exact root_successor_zero

/-- The strongest named payoff supplied by this promoted datum. -/
theorem isUniformEquilibriumPayoff :
    (quittingGame reward).IsUniformEquilibriumPayoff none value := by
  rw [← certificate_payoff]
  exact certificate.isUniformEquilibriumPayoff

end QuittingCutoffOneMixedActual
end GameTheory
